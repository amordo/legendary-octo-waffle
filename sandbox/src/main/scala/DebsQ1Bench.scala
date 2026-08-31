import scala.collection.mutable

import scala.scalanative.libc.stdio.{FILE, fclose, fopen, fread, fwrite}
import scala.scalanative.libc.stdlib.{free, malloc, realloc}
import scala.scalanative.libc.string.memmove
import scala.scalanative.meta.LinktimeInfo
import scala.scalanative.runtime.GC
import scala.scalanative.unsafe._
import scala.scalanative.unsigned._

/** DEBS 2015 Grand Challenge, query 1 ("frequent routes"), replayed from the
 *  NYC taxi trip file: https://debs.org/grand-challenges/2015/
 *
 *  For every trip report the top 10 most frequent routes of the last 30 minutes
 *  are maintained, where a route is the pair (pickup cell, drop-off cell) on a
 *  500 m x 500 m grid whose cell 1.1 is centred at 41.474937, -74.913585 and
 *  which spans 300 x 300 cells. Trips that start or end outside the grid are
 *  outliers and are not counted. A result line is emitted whenever the list or
 *  its order changes, including when a change is caused by events leaving the
 *  window. Ties are broken by freshness, as the challenge FAQ requires.
 *
 *  What varies between the three BENCH_MODEs is only how the operator state is
 *  represented; the algorithm, the reader and the output formatter are shared:
 *
 *    - `heap` : a `mutable.LongMap` of `RouteEntry` objects and a window of
 *      per-event `TripEvent` objects, i.e. what a GC-managed implementation of
 *      this operator naturally looks like.
 *    - `offheap` : the same graph flattened into malloc'd primitive arrays
 *      addressed by integer indices. Nothing is allocated on the GC heap inside
 *      the loop, so `gcCollections` must come out as 0.
 *    - `zone` : the same operator built on `unsafe.Zone` regions instead of
 *      `malloc` -- the window cut into panes that are released as whole regions
 *      and the route table in a zone open for the run. This is the region
 *      program the library invites you to write, and it says what that costs
 *      today; it is an independent implementation rather than `offheap` with an
 *      allocation bolted on, so it is the mode that answers the question.
 *
 *  I/O is held constant on purpose: every mode reads through the same raw byte
 *  reader and parses straight from the buffer without materialising Strings.
 *  Otherwise the String garbage produced by an idiomatic line reader would
 *  dominate everything else and the measurement would be about `readLine`.
 *
 *  Every mode keeps routes whose count has fallen to zero, so the number of
 *  live entries is the number of distinct routes ever seen rather than the
 *  number currently in the window. This is what the open-addressed table needs
 *  (it has no deletion) and it is applied to the heap mode as well to keep them
 *  comparable; a production heap implementation would drop them.
 *
 *  Latency follows the challenge definition: the clock starts when a line
 *  starts being parsed and stops once the result has been rendered to ASCII but
 *  before it is written out. That costs one `System.nanoTime()` per input
 *  event, which is a few percent of the per-event budget -- set
 *  BENCH_MEASURE_DELAY=0 to measure undisturbed throughput. Updates caused by
 *  events leaving the window have no end-to-end delay and are reported with a
 *  delay of 0.
 *
 *  Env vars: DEBS_FILE (required, path to the trip CSV), BENCH_MODE,
 *  BENCH_LIMIT (0 = whole file), BENCH_OUTPUT (path, empty = format and
 *  discard), BENCH_MEASURE_DELAY, BENCH_BUF_KB.
 */
object DebsQ1Bench {

  private final val Lat0 = 41.474937 // centre of cell 1.1
  private final val Lon0 = -74.913585
  private final val CellLat = 0.004491556 // 500 m south, flat-earth assumption
  private final val CellLon = 0.005986 // 500 m east
  private final val GridDim = 300
  private final val WindowSec = 30 * 60
  private final val TopK = 10

  /** Cell as `(x << 16) | y`, or -1 for a coordinate outside the grid. The NaN
   *  guard is not redundant: `Math.floor(NaN).toInt` is 0, which would land in
   *  cell 1.1 instead of being rejected.
   */
  private def cellOf(lon: Double, lat: Double): Int = {
    if (lon.isNaN || lat.isNaN) -1
    else {
      val x = Math.floor((lon - (Lon0 - CellLon / 2)) / CellLon).toInt + 1
      val y = Math.floor(((Lat0 + CellLat / 2) - lat) / CellLat).toInt + 1
      if (x >= 1 && x <= GridDim && y >= 1 && y <= GridDim) (x << 16) | y
      else -1
    }
  }

  // ---------------------------------------------------------------- parsing

  private var pPickupSec = 0
  private var pDropoffSec = 0
  private var pRouteId = 0L

  // Field positions default to the DEBS "combined" 17-column layout (no
  // header, pickup/dropoff at 2/3, coords at 6-9). The raw FOIL trip_data_N.csv
  // export inserts vendor_id/rate_code/store_and_fwd_flag/passenger_count
  // before the timestamps instead, so a header line is used to relocate these
  // when present -- see `configureColumns`.
  private var idxPickup = 2
  private var idxDropoff = 3
  private var idxPlon = 6
  private var idxPlat = 7
  private var idxDlon = 8
  private var idxDlat = 9
  private var maxFieldIdx = 9

  private def sliceToString(p: Ptr[Byte], off: Int, len: Int): String = {
    val sb = new StringBuilder(len)
    var i = 0
    while (i < len) { sb.append(p(off + i).toChar); i += 1 }
    sb.toString
  }

  private def looksLikeHeader(p: Ptr[Byte], off: Int, len: Int): Boolean =
    sliceToString(p, off, len).contains("pickup_datetime")

  /** Locates the columns this query needs by name instead of trusting a fixed
   *  position, since the file the challenge calls "trip data" has shipped under
   *  at least two different layouts.
   */
  private def configureColumns(p: Ptr[Byte], off: Int, len: Int): Unit = {
    val names = sliceToString(p, off, len).split(",", -1)
    def indexOf(name: String): Int = {
      val i = names.indexOf(name)
      require(i >= 0, s"DEBS_FILE header is missing column '$name'")
      i
    }
    idxPickup = indexOf("pickup_datetime")
    idxDropoff = indexOf("dropoff_datetime")
    idxPlon = indexOf("pickup_longitude")
    idxPlat = indexOf("pickup_latitude")
    idxDlon = indexOf("dropoff_longitude")
    idxDlat = indexOf("dropoff_latitude")
    maxFieldIdx =
      Seq(idxPickup, idxDropoff, idxPlon, idxPlat, idxDlon, idxDlat).max
  }

  private def digit(p: Ptr[Byte], i: Int): Int = p(i) - '0'

  private def two(p: Ptr[Byte], i: Int): Int =
    digit(p, i) * 10 + digit(p, i + 1)

  /** Days since 1970-01-01 for a proper Gregorian date (Howard Hinnant's
   *  days_from_civil). The trip timestamps carry no zone, so they are read as
   *  if they were UTC; only differences and formatting matter here.
   */
  private def daysFromCivil(y0: Int, m: Int, d: Int): Long = {
    val y = if (m <= 2) y0 - 1 else y0
    val era = (if (y >= 0) y else y - 399) / 400
    val yoe = y - era * 400
    val mp = if (m > 2) m - 3 else m + 9
    val doy = (153 * mp + 2) / 5 + d - 1
    val doe = yoe * 365 + yoe / 4 - yoe / 100 + doy
    era * 146097L + doe - 719468L
  }

  /** "YYYY-MM-DD HH:MM:SS" to epoch seconds, or -1 if the field is not one.
   *
   *  Fields are addressed as (base, offset) instead of through a shifted
   *  pointer: `Ptr` is a plain `final class` in Scala Native 0.5, not a value
   *  class, so every `p + off` that survives inlining is a GC-heap allocation
   *  and would put the off-heap mode back on the collector's critical path.
   */
  private def parseTimestamp(p: Ptr[Byte], off: Int, len: Int): Int = {
    if (len != 19) -1
    else if (p(off + 4) != '-' || p(off + 7) != '-' || p(off + 10) != ' ' ||
        p(off + 13) != ':' || p(off + 16) != ':') -1
    else {
      var i = 0
      var ok = true
      while (i < 19) {
        if (i != 4 && i != 7 && i != 10 && i != 13 && i != 16) {
          val c = p(off + i)
          if (c < '0' || c > '9') ok = false
        }
        i += 1
      }
      if (!ok) -1
      else {
        val year = two(p, off) * 100 + two(p, off + 2)
        val days = daysFromCivil(year, two(p, off + 5), two(p, off + 8))
        (days * 86400L + two(p, off + 11) * 3600 + two(p, off + 14) * 60 +
          two(p, off + 17)).toInt
      }
    }
  }

  /** Decimal coordinate, or NaN if the field is empty or not a number. */
  private def parseDouble(p: Ptr[Byte], off: Int, len: Int): Double = {
    if (len == 0) Double.NaN
    else {
      var i = 0
      var neg = false
      if (p(off) == '-') { neg = true; i = 1 }
      else if (p(off) == '+') i = 1
      var whole = 0L
      var frac = 0L
      var scale = 1L
      var ok = i < len
      var seenDot = false
      while (i < len && ok) {
        val c = p(off + i)
        if (c == '.' && !seenDot) seenDot = true
        else if (c >= '0' && c <= '9') {
          if (seenDot) { frac = frac * 10 + (c - '0'); scale *= 10 }
          else whole = whole * 10 + (c - '0')
        } else ok = false
        i += 1
      }
      if (!ok) Double.NaN
      else {
        val v = whole.toDouble + frac.toDouble / scale.toDouble
        if (neg) -v else v
      }
    }
  }

  /** Fills `pPickupSec`, `pDropoffSec` and `pRouteId` from one CSV line.
   *  Returns false if the line carries no usable timestamps; `pRouteId` is 0
   *  when the trip is an outlier for this query's grid.
   */
  private def parseLine(p: Ptr[Byte], off: Int, len: Int): Boolean = {
    var i = 0
    var field = 0
    var start = 0
    var pickup = -1
    var dropoff = -1
    var plon = Double.NaN
    var plat = Double.NaN
    var dlon = Double.NaN
    var dlat = Double.NaN
    while (i <= len) {
      if (i == len || p(off + i) == ',') {
        val flen = i - start
        if (field == idxPickup) pickup = parseTimestamp(p, off + start, flen)
        else if (field == idxDropoff)
          dropoff = parseTimestamp(p, off + start, flen)
        else if (field == idxPlon) plon = parseDouble(p, off + start, flen)
        else if (field == idxPlat) plat = parseDouble(p, off + start, flen)
        else if (field == idxDlon) dlon = parseDouble(p, off + start, flen)
        else if (field == idxDlat) dlat = parseDouble(p, off + start, flen)
        field += 1
        start = i + 1
        // fields past the last needed column are irrelevant to query 1
        if (field > maxFieldIdx) i = len
      }
      i += 1
    }
    if (pickup < 0 || dropoff < 0) false
    else {
      pPickupSec = pickup
      pDropoffSec = dropoff
      val from = cellOf(plon, plat)
      val to = cellOf(dlon, dlat)
      pRouteId =
        if (from < 0 || to < 0) 0L
        else (from.toLong << 32) | (to.toLong & 0xffffffffL)
      true
    }
  }

  // ----------------------------------------------------------------- reader

  /** Chunked byte reader handing out line slices of its own buffer as (buffer,
   *  offset, length). Lines are never copied and never become Strings, and no
   *  `Ptr` is constructed per line -- see `parseTimestamp`.
   */
  private final class LineReader(path: String, bufSize: Int) {
    private val file: Ptr[FILE] =
      Zone.acquire { implicit z => fopen(toCString(path), c"rb") }
    if (file == null)
      throw new RuntimeException(s"cannot open DEBS_FILE '$path'")
    val buf: Ptr[Byte] = malloc(bufSize.toUSize)
    private var fill = 0
    private var pos = 0
    private var eof = false
    private var bytes = 0L

    var lineOff = 0
    var lineLen = 0

    def bytesRead: Long = bytes

    def next(): Boolean = {
      var result = -1
      while (result < 0) {
        var i = pos
        while (i < fill && buf(i) != '\n') i += 1
        if (i < fill) {
          var end = i
          if (end > pos && buf(end - 1) == '\r') end -= 1
          lineOff = pos
          lineLen = end - pos
          pos = i + 1
          result = 1
        } else if (eof) {
          if (pos < fill) {
            lineOff = pos
            lineLen = fill - pos
            pos = fill
            result = 1
          } else result = 0
        } else {
          val remaining = fill - pos
          if (remaining == bufSize)
            throw new RuntimeException(
              s"line longer than BENCH_BUF_KB (${bufSize / 1024} KB)"
            )
          memmove(buf, buf + pos, remaining.toUSize)
          pos = 0
          fill = remaining
          val got = fread(buf + fill, 1.toUSize, (bufSize - fill).toUSize, file)
          val n = got.toInt
          if (n <= 0) eof = true
          else { fill += n; bytes += n }
        }
      }
      result == 1
    }

    def close(): Unit = {
      free(buf)
      fclose(file)
      ()
    }
  }

  // ------------------------------------------------------------ Q1 operator

  /** The top-10 is maintained incrementally against a count-bucket index: every
   *  route sits in a doubly linked list of the routes sharing its count, so a
   *  count change is O(1) and a rebuild only has to walk the highest buckets. A
   *  rebuild is needed exactly when a route currently in the top 10 loses a
   *  trip; every other update can only affect the changed route itself.
   *
   *  A rebuild has to scan the whole bucket it stops in, because the freshness
   *  tie-break is not encoded in the bucket order. On the real feed the tenth
   *  route has a count in the tens and that bucket holds a handful of routes.
   *  On uniformly random synthetic data the top 10 sits at count 1 and the
   *  bucket holds the entire window, which makes the benchmark measure that
   *  pathology instead of the workload -- generate skewed test data.
   */
  private sealed trait Q1State {

    /** Adds a trip. Returns true if the published top 10 changed. */
    def add(routeId: Long, dropoffSec: Int, seq: Long): Boolean

    /** Drops every trip whose drop-off is at or before `limitSec`. Returns the
     *  drop-off time of the last expiring trip that changed the top 10, or
     *  Int.MinValue if the list is unaffected.
     */
    def expire(limitSec: Int): Int

    def topLen: Int
    def topRoute(i: Int): Long
    def distinctRoutes: Int
    def windowSize: Int
    def close(): Unit
  }

  private final class RouteEntry(val routeId: Long) {
    var count = 0
    var lastSeq = 0L
    var bucketPrev: RouteEntry = null
    var bucketNext: RouteEntry = null
  }

  private final class TripEvent(val dropoffSec: Int, val route: RouteEntry)

  private final class HeapQ1 extends Q1State {
    private val routes = new mutable.LongMap[RouteEntry](1 << 16)
    private var buckets = new Array[RouteEntry](1024)
    private var maxCount = 0
    private val top = new Array[RouteEntry](TopK)
    private var len = 0
    private val prevTop = new Array[Long](TopK)

    private var window = new Array[TripEvent](1 << 16)
    private var head = 0
    private var size = 0

    def topLen: Int = len
    def topRoute(i: Int): Long = top(i).routeId
    def distinctRoutes: Int = routes.size
    def windowSize: Int = size
    def close(): Unit = ()

    private def better(a: RouteEntry, b: RouteEntry): Boolean =
      a.count > b.count || (a.count == b.count && a.lastSeq > b.lastSeq)

    private def bubbleUp(from: Int): Int = {
      var i = from
      while (i > 0 && better(top(i), top(i - 1))) {
        val t = top(i); top(i) = top(i - 1); top(i - 1) = t
        i -= 1
      }
      i
    }

    private def link(e: RouteEntry, c: Int): Unit = {
      if (c >= buckets.length) {
        val grown = new Array[RouteEntry](Math.max(c + 1, buckets.length * 2))
        Array.copy(buckets, 0, grown, 0, buckets.length)
        buckets = grown
      }
      e.bucketPrev = null
      e.bucketNext = buckets(c)
      if (buckets(c) != null) buckets(c).bucketPrev = e
      buckets(c) = e
    }

    private def unlink(e: RouteEntry, c: Int): Unit = {
      if (e.bucketPrev != null) e.bucketPrev.bucketNext = e.bucketNext
      else buckets(c) = e.bucketNext
      if (e.bucketNext != null) e.bucketNext.bucketPrev = e.bucketPrev
      e.bucketPrev = null
      e.bucketNext = null
    }

    private def indexInTop(e: RouteEntry): Int = {
      var i = 0
      var found = -1
      while (i < len) {
        if (top(i) eq e) found = i
        i += 1
      }
      found
    }

    private def offer(e: RouteEntry): Unit = {
      if (len < TopK) {
        top(len) = e
        len += 1
        bubbleUp(len - 1)
        ()
      } else if (better(e, top(TopK - 1))) {
        top(TopK - 1) = e
        bubbleUp(TopK - 1)
        ()
      }
    }

    private def rebuild(): Boolean = {
      var i = 0
      while (i < len) { prevTop(i) = top(i).routeId; i += 1 }
      val prevLen = len
      len = 0
      while (maxCount > 0 && buckets(maxCount) == null) maxCount -= 1
      var c = maxCount
      while (c > 0 && len < TopK) {
        var e = buckets(c)
        while (e != null) { offer(e); e = e.bucketNext }
        c -= 1
      }
      if (len != prevLen) true
      else {
        var changed = false
        var k = 0
        while (k < len) {
          if (top(k).routeId != prevTop(k)) changed = true
          k += 1
        }
        changed
      }
    }

    def add(routeId: Long, dropoffSec: Int, seq: Long): Boolean = {
      var e = routes.getOrNull(routeId)
      if (e == null) {
        e = new RouteEntry(routeId)
        routes.update(routeId, e)
      }
      val old = e.count
      if (old > 0) unlink(e, old)
      e.count = old + 1
      e.lastSeq = seq
      link(e, e.count)
      if (e.count > maxCount) maxCount = e.count

      if (size == window.length) {
        val grown = new Array[TripEvent](window.length * 2)
        var i = 0
        while (i < size) {
          grown(i) = window((head + i) % window.length)
          i += 1
        }
        window = grown
        head = 0
      }
      window((head + size) % window.length) = new TripEvent(dropoffSec, e)
      size += 1

      val idx = indexInTop(e)
      if (idx >= 0) bubbleUp(idx) != idx
      else if (len < TopK) { offer(e); true }
      else if (better(e, top(TopK - 1))) { offer(e); true }
      else false
    }

    def expire(limitSec: Int): Int = {
      var changedAt = Int.MinValue
      var go = size > 0
      while (go) {
        val ev = window(head)
        if (ev.dropoffSec > limitSec) go = false
        else {
          window(head) = null
          head = (head + 1) % window.length
          size -= 1
          val e = ev.route
          val old = e.count
          unlink(e, old)
          e.count = old - 1
          if (e.count > 0) link(e, e.count)
          if (indexInTop(e) >= 0 && rebuild()) changedAt = ev.dropoffSec
          go = size > 0
        }
      }
      changedAt
    }
  }

  /** Same structure with the object graph flattened: entries live in dense
   *  parallel arrays and every reference is an index, so growth is a `realloc`
   *  and the hash index can be rebuilt without invalidating anything.
   */
  private final class OffHeapQ1 extends Q1State {
    private var entryCap = 1 << 16
    private var entryCount = 0
    private var eKey =
      malloc((entryCap.toLong * 8).toUSize).asInstanceOf[Ptr[Long]]
    private var eSeq =
      malloc((entryCap.toLong * 8).toUSize).asInstanceOf[Ptr[Long]]
    private var eCnt =
      malloc((entryCap.toLong * 4).toUSize).asInstanceOf[Ptr[Int]]
    private var ePrev =
      malloc((entryCap.toLong * 4).toUSize).asInstanceOf[Ptr[Int]]
    private var eNext =
      malloc((entryCap.toLong * 4).toUSize).asInstanceOf[Ptr[Int]]

    // open-addressed routeId -> entry index + 1, 0 meaning empty
    private var idxCap = 1 << 17
    private var idxMask = idxCap - 1
    private var index = fillInt(
      malloc((idxCap.toLong * 4).toUSize).asInstanceOf[Ptr[Int]],
      idxCap,
      0
    )

    private var bucketCap = 1024
    private var bucketHead = fillInt(
      malloc((bucketCap.toLong * 4).toUSize).asInstanceOf[Ptr[Int]],
      bucketCap,
      -1
    )
    private var maxCount = 0

    private val top = malloc((TopK * 4).toUSize).asInstanceOf[Ptr[Int]]
    private val prevTop = malloc((TopK * 8).toUSize).asInstanceOf[Ptr[Long]]
    private var len = 0

    private var winCap = 1 << 16
    private var wDrop =
      malloc((winCap.toLong * 4).toUSize).asInstanceOf[Ptr[Int]]
    private var wEntry =
      malloc((winCap.toLong * 4).toUSize).asInstanceOf[Ptr[Int]]
    private var head = 0
    private var size = 0

    private def fillInt(p: Ptr[Int], n: Int, v: Int): Ptr[Int] = {
      var i = 0
      while (i < n) { p(i) = v; i += 1 }
      p
    }

    def topLen: Int = len
    def topRoute(i: Int): Long = eKey(top(i))
    def distinctRoutes: Int = entryCount
    def windowSize: Int = size

    def close(): Unit = {
      free(eKey.asInstanceOf[Ptr[Byte]])
      free(eSeq.asInstanceOf[Ptr[Byte]])
      free(eCnt.asInstanceOf[Ptr[Byte]])
      free(ePrev.asInstanceOf[Ptr[Byte]])
      free(eNext.asInstanceOf[Ptr[Byte]])
      free(index.asInstanceOf[Ptr[Byte]])
      free(bucketHead.asInstanceOf[Ptr[Byte]])
      free(top.asInstanceOf[Ptr[Byte]])
      free(prevTop.asInstanceOf[Ptr[Byte]])
      free(wDrop.asInstanceOf[Ptr[Byte]])
      free(wEntry.asInstanceOf[Ptr[Byte]])
    }

    private def hashOf(key: Long): Int = {
      var h = key * 0x9e3779b97f4a7c15L
      h ^= h >>> 32
      h.toInt & idxMask
    }

    private def rehash(): Unit = {
      idxCap <<= 1
      idxMask = idxCap - 1
      free(index.asInstanceOf[Ptr[Byte]])
      index = fillInt(
        malloc((idxCap.toLong * 4).toUSize).asInstanceOf[Ptr[Int]],
        idxCap,
        0
      )
      var e = 0
      while (e < entryCount) {
        var i = hashOf(eKey(e))
        while (index(i) != 0) i = (i + 1) & idxMask
        index(i) = e + 1
        e += 1
      }
    }

    private def growEntries(): Unit = {
      entryCap <<= 1
      eKey =
        realloc(eKey.asInstanceOf[Ptr[Byte]], (entryCap.toLong * 8).toUSize)
          .asInstanceOf[Ptr[Long]]
      eSeq =
        realloc(eSeq.asInstanceOf[Ptr[Byte]], (entryCap.toLong * 8).toUSize)
          .asInstanceOf[Ptr[Long]]
      eCnt =
        realloc(eCnt.asInstanceOf[Ptr[Byte]], (entryCap.toLong * 4).toUSize)
          .asInstanceOf[Ptr[Int]]
      ePrev =
        realloc(ePrev.asInstanceOf[Ptr[Byte]], (entryCap.toLong * 4).toUSize)
          .asInstanceOf[Ptr[Int]]
      eNext =
        realloc(eNext.asInstanceOf[Ptr[Byte]], (entryCap.toLong * 4).toUSize)
          .asInstanceOf[Ptr[Int]]
    }

    private def entryFor(key: Long): Int = {
      var i = hashOf(key)
      var v = index(i)
      while (v != 0 && eKey(v - 1) != key) {
        i = (i + 1) & idxMask
        v = index(i)
      }
      if (v != 0) v - 1
      else {
        if (entryCount == entryCap) growEntries()
        val e = entryCount
        entryCount += 1
        eKey(e) = key
        eSeq(e) = 0L
        eCnt(e) = 0
        ePrev(e) = -1
        eNext(e) = -1
        index(i) = e + 1
        if (entryCount * 10 >= idxCap * 6) rehash()
        e
      }
    }

    private def better(a: Int, b: Int): Boolean =
      eCnt(a) > eCnt(b) || (eCnt(a) == eCnt(b) && eSeq(a) > eSeq(b))

    private def bubbleUp(from: Int): Int = {
      var i = from
      while (i > 0 && better(top(i), top(i - 1))) {
        val t = top(i); top(i) = top(i - 1); top(i - 1) = t
        i -= 1
      }
      i
    }

    private def link(e: Int, c: Int): Unit = {
      if (c >= bucketCap) {
        val grown = Math.max(c + 1, bucketCap * 2)
        bucketHead = realloc(
          bucketHead.asInstanceOf[Ptr[Byte]],
          (grown.toLong * 4).toUSize
        ).asInstanceOf[Ptr[Int]]
        var i = bucketCap
        while (i < grown) { bucketHead(i) = -1; i += 1 }
        bucketCap = grown
      }
      ePrev(e) = -1
      eNext(e) = bucketHead(c)
      if (bucketHead(c) >= 0) ePrev(bucketHead(c)) = e
      bucketHead(c) = e
    }

    private def unlink(e: Int, c: Int): Unit = {
      if (ePrev(e) >= 0) eNext(ePrev(e)) = eNext(e)
      else bucketHead(c) = eNext(e)
      if (eNext(e) >= 0) ePrev(eNext(e)) = ePrev(e)
      ePrev(e) = -1
      eNext(e) = -1
    }

    private def indexInTop(e: Int): Int = {
      var i = 0
      var found = -1
      while (i < len) {
        if (top(i) == e) found = i
        i += 1
      }
      found
    }

    private def offer(e: Int): Unit = {
      if (len < TopK) {
        top(len) = e
        len += 1
        bubbleUp(len - 1)
        ()
      } else if (better(e, top(TopK - 1))) {
        top(TopK - 1) = e
        bubbleUp(TopK - 1)
        ()
      }
    }

    private def rebuild(): Boolean = {
      var i = 0
      while (i < len) { prevTop(i) = eKey(top(i)); i += 1 }
      val prevLen = len
      len = 0
      while (maxCount > 0 && bucketHead(maxCount) < 0) maxCount -= 1
      var c = maxCount
      while (c > 0 && len < TopK) {
        var e = bucketHead(c)
        while (e >= 0) { offer(e); e = eNext(e) }
        c -= 1
      }
      if (len != prevLen) true
      else {
        var changed = false
        var k = 0
        while (k < len) {
          if (eKey(top(k)) != prevTop(k)) changed = true
          k += 1
        }
        changed
      }
    }

    def add(routeId: Long, dropoffSec: Int, seq: Long): Boolean = {
      val e = entryFor(routeId)
      val old = eCnt(e)
      if (old > 0) unlink(e, old)
      eCnt(e) = old + 1
      eSeq(e) = seq
      link(e, old + 1)
      if (old + 1 > maxCount) maxCount = old + 1

      if (size == winCap) {
        val grown = winCap * 2
        val nDrop = malloc((grown.toLong * 4).toUSize).asInstanceOf[Ptr[Int]]
        val nEntry = malloc((grown.toLong * 4).toUSize).asInstanceOf[Ptr[Int]]
        var i = 0
        while (i < size) {
          val src = (head + i) % winCap
          nDrop(i) = wDrop(src)
          nEntry(i) = wEntry(src)
          i += 1
        }
        free(wDrop.asInstanceOf[Ptr[Byte]])
        free(wEntry.asInstanceOf[Ptr[Byte]])
        wDrop = nDrop
        wEntry = nEntry
        winCap = grown
        head = 0
      }
      val slot = (head + size) % winCap
      wDrop(slot) = dropoffSec
      wEntry(slot) = e
      size += 1

      val idx = indexInTop(e)
      if (idx >= 0) bubbleUp(idx) != idx
      else if (len < TopK) { offer(e); true }
      else if (better(e, top(TopK - 1))) { offer(e); true }
      else false
    }

    def expire(limitSec: Int): Int = {
      var changedAt = Int.MinValue
      var go = size > 0
      while (go) {
        val drop = wDrop(head)
        if (drop > limitSec) go = false
        else {
          val e = wEntry(head)
          head = (head + 1) % winCap
          size -= 1
          val old = eCnt(e)
          unlink(e, old)
          eCnt(e) = old - 1
          if (old - 1 > 0) link(e, old - 1)
          if (indexInTop(e) >= 0 && rebuild()) changedAt = drop
          go = size > 0
        }
      }
      changedAt
    }
  }

  /** One trip in the window: drop-off second, route entry index, next record.
   *  The link is `Ptr[Byte]` because a struct cannot mention itself.
   */
  private type TripRec = CStruct3[Int, Int, Ptr[Byte]]

  /** A slice of the window that owns its region. Panes are cut on arrival
   *  count, not on time, so the oldest pane is always the one that drains first
   *  no matter how the drop-off times are ordered in the file.
   */
  private final class ZonePane(val zone: Zone) {
    var allocated = 0
    var expired = 0
    var next: ZonePane = null
  }

  /** The same operator written against `unsafe.Zone` instead of `malloc`, the
   *  way a Scala Native program that wants regions would actually be written.
   *
   *  The window is the part with region-shaped lifetime, so it is cut into
   *  panes of `PaneTrips` consecutive arrivals; each pane opens a zone, trips
   *  are allocated one record at a time inside it, and the whole zone is closed
   *  in one call once its last record has left the window. Expiry itself stays
   *  exact and per event -- the regions only decide when the memory goes back,
   *  which is what a region allocator is for.
   *
   *  The route table cannot be paned: any route may be touched again
   *  arbitrarily far in the future, so its arrays live in a single zone that
   *  stays open for the whole run. A zone has no `realloc` and no per-object
   *  free, so growing one of them allocates a larger copy in the zone and
   *  abandons the old one until the run ends -- that is the price of the region
   *  model, and it is left in rather than worked around.
   *
   *  This mode deliberately differs from `offheap` in two ways at once, because
   *  writing it idiomatically forces both: `Zone.alloc` per trip, and the `Tag`
   *  and `Ptr` objects that typed struct access materialises. Both land on the
   *  GC heap in Scala Native 0.5, so unlike `offheap` this mode does collect.
   *  GcPauseBench measures the two costs separately on a synthetic workload;
   *  here the question is only what they add up to on a real one.
   */
  private final class ZoneQ1 extends Q1State {
    private final val PaneTrips = 1 << 16

    private val stateZone: Zone = Zone.open()

    private def longs(n: Int): Ptr[Long] = {
      implicit val z: Zone = stateZone
      alloc[Long](n)
    }

    private def ints(n: Int): Ptr[Int] = {
      implicit val z: Zone = stateZone
      alloc[Int](n)
    }

    private def newTrip(pane: ZonePane): Ptr[TripRec] = {
      implicit val z: Zone = pane.zone
      alloc[TripRec]()
    }

    private def fillInt(
        p: Ptr[Int],
        from: Int,
        until: Int,
        v: Int
    ): Ptr[Int] = {
      var i = from
      while (i < until) { p(i) = v; i += 1 }
      p
    }

    private var entryCap = 1 << 16
    private var entryCount = 0
    private var eKey = longs(entryCap)
    private var eSeq = longs(entryCap)
    private var eCnt = ints(entryCap)
    private var ePrev = ints(entryCap)
    private var eNext = ints(entryCap)

    // open-addressed routeId -> entry index + 1; zone memory arrives zeroed,
    // which is exactly the empty marker
    private var idxCap = 1 << 17
    private var idxMask = idxCap - 1
    private var index = ints(idxCap)

    private var bucketCap = 1024
    private var bucketHead = fillInt(ints(bucketCap), 0, bucketCap, -1)
    private var maxCount = 0

    private val top = ints(TopK)
    private val prevTop = longs(TopK)
    private var len = 0

    private var paneHead: ZonePane = null
    private var paneTail: ZonePane = null
    private var winHead: Ptr[TripRec] = null
    private var winTail: Ptr[TripRec] = null
    private var size = 0

    def topLen: Int = len
    def topRoute(i: Int): Long = eKey(top(i))
    def distinctRoutes: Int = entryCount
    def windowSize: Int = size

    def close(): Unit = {
      var pane = paneHead
      while (pane != null) {
        pane.zone.close()
        pane = pane.next
      }
      paneHead = null
      paneTail = null
      stateZone.close()
    }

    private def hashOf(key: Long): Int = {
      var h = key * 0x9e3779b97f4a7c15L
      h ^= h >>> 32
      h.toInt & idxMask
    }

    private def grownLongs(src: Ptr[Long], n: Int, cap: Int): Ptr[Long] = {
      val dst = longs(cap)
      var i = 0
      while (i < n) { dst(i) = src(i); i += 1 }
      dst
    }

    private def grownInts(src: Ptr[Int], n: Int, cap: Int): Ptr[Int] = {
      val dst = ints(cap)
      var i = 0
      while (i < n) { dst(i) = src(i); i += 1 }
      dst
    }

    private def rehash(): Unit = {
      idxCap <<= 1
      idxMask = idxCap - 1
      index = ints(idxCap)
      var e = 0
      while (e < entryCount) {
        var i = hashOf(eKey(e))
        while (index(i) != 0) i = (i + 1) & idxMask
        index(i) = e + 1
        e += 1
      }
    }

    private def growEntries(): Unit = {
      val old = entryCap
      entryCap <<= 1
      eKey = grownLongs(eKey, old, entryCap)
      eSeq = grownLongs(eSeq, old, entryCap)
      eCnt = grownInts(eCnt, old, entryCap)
      ePrev = grownInts(ePrev, old, entryCap)
      eNext = grownInts(eNext, old, entryCap)
    }

    private def entryFor(key: Long): Int = {
      var i = hashOf(key)
      var v = index(i)
      while (v != 0 && eKey(v - 1) != key) {
        i = (i + 1) & idxMask
        v = index(i)
      }
      if (v != 0) v - 1
      else {
        if (entryCount == entryCap) growEntries()
        val e = entryCount
        entryCount += 1
        eKey(e) = key
        eSeq(e) = 0L
        eCnt(e) = 0
        ePrev(e) = -1
        eNext(e) = -1
        index(i) = e + 1
        if (entryCount * 10 >= idxCap * 6) rehash()
        e
      }
    }

    private def better(a: Int, b: Int): Boolean =
      eCnt(a) > eCnt(b) || (eCnt(a) == eCnt(b) && eSeq(a) > eSeq(b))

    private def bubbleUp(from: Int): Int = {
      var i = from
      while (i > 0 && better(top(i), top(i - 1))) {
        val t = top(i); top(i) = top(i - 1); top(i - 1) = t
        i -= 1
      }
      i
    }

    private def link(e: Int, c: Int): Unit = {
      if (c >= bucketCap) {
        val grown = Math.max(c + 1, bucketCap * 2)
        bucketHead = fillInt(
          grownInts(bucketHead, bucketCap, grown),
          bucketCap,
          grown,
          -1
        )
        bucketCap = grown
      }
      ePrev(e) = -1
      eNext(e) = bucketHead(c)
      if (bucketHead(c) >= 0) ePrev(bucketHead(c)) = e
      bucketHead(c) = e
    }

    private def unlink(e: Int, c: Int): Unit = {
      if (ePrev(e) >= 0) eNext(ePrev(e)) = eNext(e)
      else bucketHead(c) = eNext(e)
      if (eNext(e) >= 0) ePrev(eNext(e)) = ePrev(e)
      ePrev(e) = -1
      eNext(e) = -1
    }

    private def indexInTop(e: Int): Int = {
      var i = 0
      var found = -1
      while (i < len) {
        if (top(i) == e) found = i
        i += 1
      }
      found
    }

    private def offer(e: Int): Unit = {
      if (len < TopK) {
        top(len) = e
        len += 1
        bubbleUp(len - 1)
        ()
      } else if (better(e, top(TopK - 1))) {
        top(TopK - 1) = e
        bubbleUp(TopK - 1)
        ()
      }
    }

    private def rebuild(): Boolean = {
      var i = 0
      while (i < len) { prevTop(i) = eKey(top(i)); i += 1 }
      val prevLen = len
      len = 0
      while (maxCount > 0 && bucketHead(maxCount) < 0) maxCount -= 1
      var c = maxCount
      while (c > 0 && len < TopK) {
        var e = bucketHead(c)
        while (e >= 0) { offer(e); e = eNext(e) }
        c -= 1
      }
      if (len != prevLen) true
      else {
        var changed = false
        var k = 0
        while (k < len) {
          if (eKey(top(k)) != prevTop(k)) changed = true
          k += 1
        }
        changed
      }
    }

    def add(routeId: Long, dropoffSec: Int, seq: Long): Boolean = {
      val e = entryFor(routeId)
      val old = eCnt(e)
      if (old > 0) unlink(e, old)
      eCnt(e) = old + 1
      eSeq(e) = seq
      link(e, old + 1)
      if (old + 1 > maxCount) maxCount = old + 1

      if (paneTail == null || paneTail.allocated == PaneTrips) {
        val pane = new ZonePane(Zone.open())
        if (paneTail == null) paneHead = pane else paneTail.next = pane
        paneTail = pane
      }
      val trip = newTrip(paneTail)
      paneTail.allocated += 1
      trip._1 = dropoffSec
      trip._2 = e
      // _3 stays null, zone allocations come back zeroed
      if (winTail == null) winHead = trip
      else winTail._3 = trip.asInstanceOf[Ptr[Byte]]
      winTail = trip
      size += 1

      val idx = indexInTop(e)
      if (idx >= 0) bubbleUp(idx) != idx
      else if (len < TopK) { offer(e); true }
      else if (better(e, top(TopK - 1))) { offer(e); true }
      else false
    }

    def expire(limitSec: Int): Int = {
      var changedAt = Int.MinValue
      var go = size > 0
      while (go) {
        val trip = winHead
        val drop = trip._1
        if (drop > limitSec) go = false
        else {
          val e = trip._2
          val next = trip._3.asInstanceOf[Ptr[TripRec]]
          winHead = next
          if (next == null) winTail = null
          size -= 1
          // release drained panes before charging this record, otherwise the
          // count of a pane that filled up and emptied without a successor
          // would run past its size and it would never be released
          while (paneHead.expired == paneHead.allocated &&
              paneHead.next != null) {
            val done = paneHead
            paneHead = done.next
            done.zone.close()
          }
          paneHead.expired += 1
          val cnt = eCnt(e)
          unlink(e, cnt)
          eCnt(e) = cnt - 1
          if (cnt - 1 > 0) link(e, cnt - 1)
          if (indexInTop(e) >= 0 && rebuild()) changedAt = drop
          go = size > 0
        }
      }
      changedAt
    }
  }

  // -------------------------------------------------------------- rendering

  private val outBuf: Ptr[Byte] = malloc(1024.toUSize)
  private var outFile: Ptr[FILE] = null

  private def put(off: Int, c: Char): Int = {
    outBuf(off) = c.toByte
    off + 1
  }

  private def writeUnsigned(off0: Int, v0: Long, minDigits: Int): Int = {
    var digits = 1
    var probe = v0 / 10
    while (probe > 0) { digits += 1; probe /= 10 }
    while (digits < minDigits) digits += 1
    var i = off0 + digits - 1
    var v = v0
    while (i >= off0) {
      outBuf(i) = ('0' + (v % 10).toInt).toByte
      v /= 10
      i -= 1
    }
    off0 + digits
  }

  private def writeTimestamp(off0: Int, epochSec: Int): Int = {
    val days = Math.floorDiv(epochSec.toLong, 86400L)
    val secOfDay = (epochSec.toLong - days * 86400L).toInt
    val z = days + 719468L
    val era = (if (z >= 0) z else z - 146096) / 146097
    val doe = z - era * 146097
    val yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
    val doy = doe - (365 * yoe + yoe / 4 - yoe / 100)
    val mp = (5 * doy + 2) / 153
    val d = (doy - (153 * mp + 2) / 5 + 1).toInt
    val m = (if (mp < 10) mp + 3 else mp - 9).toInt
    val y = (if (m <= 2) yoe + era * 400 + 1 else yoe + era * 400).toInt
    var off = writeUnsigned(off0, y.toLong, 4)
    off = put(off, '-')
    off = writeUnsigned(off, m.toLong, 2)
    off = put(off, '-')
    off = writeUnsigned(off, d.toLong, 2)
    off = put(off, ' ')
    off = writeUnsigned(off, (secOfDay / 3600).toLong, 2)
    off = put(off, ':')
    off = writeUnsigned(off, ((secOfDay / 60) % 60).toLong, 2)
    off = put(off, ':')
    writeUnsigned(off, (secOfDay % 60).toLong, 2)
  }

  private def writeCell(off0: Int, cell: Int): Int = {
    val off = writeUnsigned(off0, ((cell >>> 16) & 0xffff).toLong, 1)
    writeUnsigned(put(off, '.'), (cell & 0xffff).toLong, 1)
  }

  private def writeNull(off0: Int): Int = {
    var off = put(off0, 'N')
    off = put(off, 'U')
    off = put(off, 'L')
    put(off, 'L')
  }

  private var outputs = 0L
  private var topSink = 0L

  /** Renders one result line up to but not including the delay field, which the
   *  caller appends once the clock has been read (the challenge counts encoding
   *  the result as processing, but not the write).
   */
  private def renderTop(
      state: Q1State,
      pickupSec: Int,
      dropoffSec: Int
  ): Int = {
    var off = writeTimestamp(0, pickupSec)
    off = put(off, ',')
    off = writeTimestamp(off, dropoffSec)
    var i = 0
    while (i < TopK) {
      off = put(off, ',')
      if (i < state.topLen) {
        val route = state.topRoute(i)
        topSink ^= route * (i + 1)
        off = writeCell(off, (route >>> 32).toInt)
        off = put(off, ',')
        off = writeCell(off, (route & 0xffffffffL).toInt)
      } else {
        off = writeNull(off)
        off = put(off, ',')
        off = writeNull(off)
      }
      i += 1
    }
    put(off, ',')
  }

  private def flush(len0: Int): Unit = {
    val len = put(len0, '\n')
    outputs += 1
    if (outFile != null) {
      fwrite(outBuf, 1.toUSize, len.toUSize, outFile)
      ()
    }
  }

  // ---------------------------------------------------------------- metrics

  @extern
  private object libc {
    def getrusage(who: CInt, usage: Ptr[Byte]): CInt = extern
  }

  /** Peak RSS in bytes, or -1. `ru_maxrss` sits behind the two 16 B timevals
   *  that posixlib's `rusage` declares; macOS reports bytes, Linux kilobytes.
   */
  private def maxRssBytes(): Long = {
    val buf = stackalloc[Byte](256)
    if (libc.getrusage(0, buf) != 0) -1L
    else {
      val v = !(buf + 32).asInstanceOf[Ptr[Long]]
      if (LinktimeInfo.isMac) v else v * 1024L
    }
  }

  private var delayCap = 1 << 20
  private var delayCount = 0
  private var delays =
    malloc((delayCap.toLong * 8).toUSize).asInstanceOf[Ptr[Long]]

  private def recordDelay(ns: Long): Unit = {
    if (delayCount == delayCap) {
      delayCap <<= 1
      delays =
        realloc(delays.asInstanceOf[Ptr[Byte]], (delayCap.toLong * 8).toUSize)
          .asInstanceOf[Ptr[Long]]
    }
    delays(delayCount) = ns
    delayCount += 1
  }

  private def percentile(sorted: Array[Long], q: Double): Long =
    if (sorted.length == 0) -1L
    else {
      val rank = Math.ceil(q * sorted.length).toInt - 1
      sorted(Math.min(sorted.length - 1, Math.max(0, rank)))
    }

  def main(args: Array[String]): Unit = {
    val path = Option(System.getenv("DEBS_FILE")).getOrElse("")
    require(
      path.nonEmpty,
      "DEBS_FILE must point at the DEBS 2015 trip CSV " +
        "(https://debs.org/grand-challenges/2015/)"
    )
    val mode = Option(System.getenv("BENCH_MODE")).getOrElse("heap")
    require(
      mode == "heap" || mode == "offheap" || mode == "zone",
      s"BENCH_MODE must be heap, offheap or zone, got '$mode'"
    )
    val limit = Option(System.getenv("BENCH_LIMIT")).fold(0L)(_.toLong)
    val bufKb = Option(System.getenv("BENCH_BUF_KB")).fold(1024)(_.toInt)
    val measureDelay =
      Option(System.getenv("BENCH_MEASURE_DELAY")).forall(v =>
        v != "0" && v != "false"
      )
    val outPath = Option(System.getenv("BENCH_OUTPUT")).getOrElse("")
    if (outPath.nonEmpty)
      outFile = Zone.acquire { implicit z => fopen(toCString(outPath), c"wb") }

    val state: Q1State =
      if (mode == "offheap") new OffHeapQ1
      else if (mode == "zone") new ZoneQ1
      else new HeapQ1
    val reader = new LineReader(path, bufKb * 1024)

    var events = 0L
    var outliers = 0L
    var malformed = 0L
    var seq = 0L

    val rssBefore = maxRssBytes()
    val gcCollectionsBefore = GC.getStatsCollectionTotal().toLong
    val gcTimeNanosBefore = GC.getStatsCollectionDurationTotal().toLong
    val start = System.nanoTime()

    var more = reader.next()
    if (more && looksLikeHeader(reader.buf, reader.lineOff, reader.lineLen)) {
      configureColumns(reader.buf, reader.lineOff, reader.lineLen)
      more = reader.next()
    }
    while (more) {
      val t0 = if (measureDelay) System.nanoTime() else 0L
      if (parseLine(reader.buf, reader.lineOff, reader.lineLen)) {
        events += 1
        val dropoff = pDropoffSec
        val expiredAt = state.expire(dropoff - WindowSec)
        if (expiredAt != Int.MinValue) {
          // an update caused by a window timeout carries no end-to-end delay
          val at = expiredAt + WindowSec
          flush(writeUnsigned(renderTop(state, at, at), 0L, 1))
        }
        if (pRouteId != 0L) {
          seq += 1
          if (state.add(pRouteId, dropoff, seq)) {
            val off = renderTop(state, pPickupSec, dropoff)
            val delay = if (measureDelay) System.nanoTime() - t0 else 0L
            flush(writeUnsigned(off, delay, 1))
            if (measureDelay) recordDelay(delay)
          }
        } else outliers += 1
      } else malformed += 1
      more = (limit == 0L || events < limit) && reader.next()
    }

    val elapsedSec = (System.nanoTime() - start) / 1e9
    val gcCollections =
      GC.getStatsCollectionTotal().toLong - gcCollectionsBefore
    val gcTimeMs =
      (GC.getStatsCollectionDurationTotal().toLong - gcTimeNanosBefore) / 1e6
    val rssPeak = maxRssBytes()
    val bytes = reader.bytesRead

    val sample = new Array[Long](delayCount)
    var i = 0
    var delaySum = 0L
    while (i < delayCount) {
      sample(i) = delays(i)
      delaySum += delays(i)
      i += 1
    }
    java.util.Arrays.sort(sample)

    println(
      ("mode=%s events=%d outliers=%d malformed=%d bytes=%d elapsedSec=%.3f " +
        "eventsPerSec=%.0f bytesPerSec=%.0f outputs=%d distinctRoutes=%d " +
        "windowSize=%d delaySamples=%d delayMeanNs=%.0f delayP50Ns=%d " +
        "delayP99Ns=%d delayP999Ns=%d delayMaxNs=%d gcCollections=%d " +
        "gcTimeMs=%.3f gcTimeShare=%.4f rssPeakBytes=%d rssGrowthBytes=%d " +
        "gcHeapUsedBytes=%d gcHeapMaxBytes=%d topSink=%d")
        .format(
          mode,
          events,
          outliers,
          malformed,
          bytes,
          elapsedSec,
          events / elapsedSec,
          bytes / elapsedSec,
          outputs,
          state.distinctRoutes,
          state.windowSize,
          delayCount,
          if (delayCount == 0) 0.0 else delaySum.toDouble / delayCount,
          percentile(sample, 0.50),
          percentile(sample, 0.99),
          percentile(sample, 0.999),
          if (delayCount == 0) -1L else sample(delayCount - 1),
          gcCollections,
          gcTimeMs,
          gcTimeMs / 1000 / elapsedSec,
          rssPeak,
          rssPeak - rssBefore,
          GC.getUsedHeapSize().toLong,
          GC.getMaxHeapSize().toLong,
          topSink
        )
    )

    if (outFile != null) fclose(outFile)
    reader.close()
    state.close()
    free(delays.asInstanceOf[Ptr[Byte]])
    free(outBuf)
  }
}
