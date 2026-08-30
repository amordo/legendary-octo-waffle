import scala.scalanative.libc.stdlib.{free, malloc}
import scala.scalanative.meta.LinktimeInfo
import scala.scalanative.runtime.GC
import scala.scalanative.unsafe._

/** Allocation-churn harness: N threads repeatedly build and drop a linked list
 *  of `BENCH_CHAIN_LEN` nodes for a fixed duration; reports throughput, GC
 *  time/count deltas and memory footprint.
 *
 *  The memory modes (BENCH_MODE) exercise the *same* logical workload and form
 *  a ladder, each rung adding one cost over the previous one:
 *
 *    - `arena`       : per-thread off-heap bump arena, cursor reset at the
 *                      batch boundary. No GC, no locking: the ceiling.
 *    - `zone`        : the same regions through `unsafe.Zone`, one zone per
 *                      chain. Pages come from a single process-wide pool whose
 *                      claim/reclaim are `synchronized`, so this measures what
 *                      the idiomatic API costs under parallelism.
 *    - `arenaStruct` : the arena written naively with CStruct-typed pointers,
 *                      which allocates Tags on the GC heap.
 *    - `heap`        : GC-managed `Node` objects; the baseline.
 *
 *  `arena` is the intended GC-free reference point. The `none` GC is *not* a
 *  valid one: it bump-allocates fresh mmap'd memory and never reuses it, so it
 *  measures page-fault throughput rather than allocation throughput.
 *
 *  Known confound: an on-heap `Node` carries an object header while the
 *  off-heap node does not (32 B vs 16 B), so the off-heap modes also benefit
 *  from higher density. Normalise by bytes, not allocations, when attributing
 *  the speedup.
 *
 *  Env vars: BENCH_MODE, BENCH_THREADS, BENCH_DURATION_SEC, BENCH_CHAIN_LEN.
 */
object GcPauseBench {
  final class Node(val value: Long, val next: Node)

  @extern
  private object libc {
    def getrusage(who: CInt, usage: Ptr[Byte]): CInt = extern
  }

  /** Peak resident set size in bytes, or -1 if unavailable. posixlib's `rusage`
   *  only declares the two POSIX-mandated timevals, so `ru_maxrss` is read by
   *  offset: it follows `ru_utime` and `ru_stime`, both 16 B on every supported
   *  platform. macOS reports bytes, Linux and the BSDs kilobytes.
   */
  private def maxRssBytes(): Long = {
    val buf = stackalloc[Byte](256) // struct rusage is 144 B
    val RusageSelf = 0
    if (libc.getrusage(RusageSelf, buf) != 0) -1L
    else {
      val ruMaxRss = !(buf + 32).asInstanceOf[Ptr[Long]]
      if (LinktimeInfo.isMac) ruMaxRss else ruMaxRss * 1024L
    }
  }

  /** Off-heap node layout, as two raw 64-bit words: [0] = value, [1] = address
   *  of the next node (0 == end of chain).
   *
   *  Deliberately *not* a `CStruct2[Long, Ptr[Byte]]`: `Tag.CStruct2` is a case
   *  class and `materializeCStruct2Tag` an implicit def, so every pointer
   *  arithmetic / field access in the loop summons and allocates a fresh Tag on
   *  the GC heap -- silently turning "off-heap" code into a GC-bound workload
   *  (measured: ~950 collections per 3 s run). Hoisting the Tag into a val
   *  removes neither the allocations nor the cost: it also defeats the
   *  `@alwaysinline` constant-folding of sizes/offsets and halves throughput.
   *  Primitive tags such as `Tag.Long` are singletons, so `Ptr[Long]`
   *  arithmetic folds to constants and allocates nothing.
   */
  private final val NodeWords = 2
  private final val NodeBytes = NodeWords * 8L

  /** GC-managed chain: dropping `head` creates garbage. */
  def churnHeap(
      deadline: Long,
      chainLen: Int,
      sinks: Array[Long],
      idx: Int
  ): Long = {
    var allocated = 0L
    var sink = 0L
    // The clock is read once per chain, never per allocation: at ~20 ns a call
    // System.nanoTime() costs as much as the allocation itself and would
    // compress every measured difference towards 1.0.
    while (System.nanoTime() < deadline) {
      var head: Node = null
      var i = 0
      while (i < chainLen) {
        head = new Node(allocated + i, head)
        i += 1
      }
      allocated += chainLen
      sink ^= head.value // keep the chain observable
      // head dies here: the whole chain becomes garbage
    }
    sinks(idx) = sink
    allocated
  }

  /** Per-thread off-heap bump arena: dropping the chain resets the cursor, so
   *  the same buffer is reused instead of being reclaimed by a GC.
   */
  def churnArena(
      deadline: Long,
      chainLen: Int,
      sinks: Array[Long],
      idx: Int
  ): Long = {
    val nodeSize = NodeBytes
    val base = malloc(nodeSize * chainLen.toLong)
    if (base == null)
      throw new OutOfMemoryError("arena allocation failed")
    val arena = base.asInstanceOf[Ptr[Long]]

    var allocated = 0L
    var sink = 0L
    // see churnHeap: the clock is read once per chain, not per allocation
    while (System.nanoTime() < deadline) {
      var head = 0L // address of the head node, 0 == empty chain
      var i = 0
      while (i < chainLen) {
        val node = arena + i * NodeWords // bump-allocate
        node(0) = allocated + i
        node(1) = head
        head = node.toLong
        i += 1
      }
      allocated += chainLen
      sink ^= arena((chainLen - 1) * NodeWords) // keep the chain observable
      // the cursor restarts at 0: the same buffer is reused, nothing to reclaim
    }
    sinks(idx) = sink
    free(base)
    allocated
  }

  /** Same regions through the library allocator: one `Zone` per chain, closed
   *  at the batch boundary.
   *
   *  Measured at ~10.5 M alloc/s -- 90x slower than `churnArena` and 35x slower
   *  than the GC heap -- and it triggers GC collections despite being nominally
   *  off-heap. The cost is per `alloc` call, not per zone: throughput is flat
   *  across chainLen 256..65536, so zone open/close is not the culprit.
   *
   *  Cause: `CSize`/`USize` is `final class USize(...) extends ScalaNumber`, a
   *  real heap object rather than a value class. `MemoryPoolZone.allocSmall`
   *  and its `pad` helper build ~6-8 such temporaries per allocation, all on
   *  the GC heap (measured: ~176 B of garbage per `alloc` call). Escaping the
   *  GC via `unsafe.Zone` is therefore self-defeating in its current form.
   */
  def churnZone(
      deadline: Long,
      chainLen: Int,
      sinks: Array[Long],
      idx: Int
  ): Long = {
    var allocated = 0L
    var sink = 0L
    while (System.nanoTime() < deadline) {
      val z = Zone.open()
      try {
        var head = 0L
        var last: Ptr[Long] = null
        var i = 0
        while (i < chainLen) {
          val node = z.alloc(NodeWords * 8).asInstanceOf[Ptr[Long]]
          node(0) = allocated + i
          node(1) = head
          head = node.toLong
          last = node
          i += 1
        }
        allocated += chainLen
        sink ^= last(0)
      } finally z.close()
    }
    sinks(idx) = sink
    allocated
  }

  /** Same arena, written the naive way with typed struct pointers. Kept as a
   *  measurable control: the `Tag` summoned by `+`, `_1` and `_2` is allocated
   *  on the GC heap, so this variant is not actually off-heap.
   */
  def churnArenaStruct(
      deadline: Long,
      chainLen: Int,
      sinks: Array[Long],
      idx: Int
  ): Long = {
    val base =
      malloc(sizeof[CStruct2[Long, Ptr[Byte]]].toLong * chainLen.toLong)
    if (base == null)
      throw new OutOfMemoryError("arena allocation failed")
    val arena = base.asInstanceOf[Ptr[CStruct2[Long, Ptr[Byte]]]]

    var allocated = 0L
    var sink = 0L
    while (System.nanoTime() < deadline) {
      var head: Ptr[CStruct2[Long, Ptr[Byte]]] = null
      var i = 0
      while (i < chainLen) {
        val node = arena + i
        node._1 = allocated + i
        node._2 = head.asInstanceOf[Ptr[Byte]]
        head = node
        i += 1
      }
      allocated += chainLen
      sink ^= head._1
    }
    sinks(idx) = sink
    free(base)
    allocated
  }

  def main(args: Array[String]): Unit = {
    val mode = Option(System.getenv("BENCH_MODE")).getOrElse("heap")
    val threads = Option(System.getenv("BENCH_THREADS")).fold(1)(_.toInt)
    val durationSec =
      Option(System.getenv("BENCH_DURATION_SEC")).fold(5)(_.toInt)
    val chainLen = Option(System.getenv("BENCH_CHAIN_LEN")).fold(256)(_.toInt)
    val modes = Set("heap", "arena", "zone", "arenaStruct")
    require(
      modes.contains(mode),
      s"BENCH_MODE must be one of ${modes.mkString(", ")}, got '$mode'"
    )

    val deadline = System.nanoTime() + durationSec.toLong * 1000000000L
    val counts = new Array[Long](threads)
    val sinks = new Array[Long](threads)
    val workers = Array.tabulate(threads) { i =>
      new Thread(new Runnable {
        def run(): Unit =
          counts(i) = mode match {
            case "arena"       => churnArena(deadline, chainLen, sinks, i)
            case "zone"        => churnZone(deadline, chainLen, sinks, i)
            case "arenaStruct" => churnArenaStruct(deadline, chainLen, sinks, i)
            case _             => churnHeap(deadline, chainLen, sinks, i)
          }
      })
    }

    val rssBefore = maxRssBytes()
    val gcCollectionsBefore = GC.getStatsCollectionTotal().toLong
    val gcTimeNanosBefore = GC.getStatsCollectionDurationTotal().toLong
    val start = System.nanoTime()

    workers.foreach(_.start())
    workers.foreach(_.join())

    val elapsedSec = (System.nanoTime() - start) / 1e9
    val gcCollections =
      GC.getStatsCollectionTotal().toLong - gcCollectionsBefore
    val gcTimeMs =
      (GC.getStatsCollectionDurationTotal().toLong - gcTimeNanosBefore) / 1e6
    val total = counts.sum
    val nodeBytes =
      if (mode == "heap") 32L // rtti + lock word + value + next
      else NodeBytes
    val rssPeak = maxRssBytes()
    val gcHeapUsed = GC.getUsedHeapSize().toLong
    val gcHeapMax = GC.getMaxHeapSize().toLong

    println(
      ("mode=%s threads=%d chainLen=%d elapsedSec=%.3f allocations=%d " +
        "allocPerSec=%.0f nodeBytes=%d bytesPerSec=%.0f gcCollections=%d " +
        "gcTimeMs=%.3f gcTimeShare=%.4f rssPeakBytes=%d rssGrowthBytes=%d " +
        "gcHeapUsedBytes=%d gcHeapMaxBytes=%d sink=%d")
        .format(
          mode,
          threads,
          chainLen,
          elapsedSec,
          total,
          total / elapsedSec,
          nodeBytes,
          total * nodeBytes / elapsedSec,
          gcCollections,
          gcTimeMs,
          gcTimeMs / 1000 / elapsedSec,
          rssPeak,
          rssPeak - rssBefore,
          gcHeapUsed,
          gcHeapMax,
          sinks.foldLeft(0L)(_ ^ _)
        )
    )
  }
}
