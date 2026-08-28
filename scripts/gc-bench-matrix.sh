#!/usr/bin/env bash
# Allocation-throughput matrix: memory-mode x withGC x thread-count for the
# sandbox project's GcPauseBench. Produces one line of metrics per run in
# scripts/gc-bench-arena-results.csv.
#
# Usage:
#   scripts/gc-bench-matrix.sh [gc-list] [thread-list] [duration-sec] [mode-list]
# Examples:
#   scripts/gc-bench-matrix.sh                          # full matrix, 5s per run
#   scripts/gc-bench-matrix.sh immix "1 4" 3            # quick smoke test
#   scripts/gc-bench-matrix.sh immix "1 8" 5 arena      # off-heap arena only
#
# Modes: 'heap' (GC-managed nodes), 'arena' (per-thread off-heap bump arena
# with explicit reset) and 'arenaStruct' (the same arena written naively with
# CStruct-typed pointers, which allocates Tags on the GC heap). 'arena' is the
# GC-free reference point; the 'none' GC is not, since it never reuses memory.
# Under 'arena' the GC axis only affects incidental runtime allocations, so a
# single GC is usually enough.
#
# This build overrides the repo-wide nativeConfig from project/MyScalaNativePlugin.scala,
# which forces check/checkFatalWarnings/dump and full source-level debugging on
# every project. Those are compiler-development settings, not measurement ones:
# they cost the GC-managed path a factor of ~2 (340M -> 699M allocs/s at 4
# threads) while leaving the raw-pointer arena untouched, which alone moved the
# measured arena advantage from 9.2x to 4.3x.
#
# Requires: sbt, clang (already on PATH). Scala binary version is fixed to
# "3" (project id sandbox3). Multithreading is enabled for all runs since
# GcPauseBench always spawns real OS threads.
#
# Each run is bounded by RUN_TIMEOUT_SEC (env var, default 150s): if sbt
# doesn't finish in time (e.g. a GC deadlock under high thread count), the
# sbt/java process and its native child are killed and a TIMEOUT row is
# recorded instead of blocking forever.
set -uo pipefail
cd "$(dirname "$0")/.."

GCS="${1:-none immix commix boehm}"
THREAD_COUNTS="${2:-1 4 8 16}"
DURATION_SEC="${3:-5}"
MODES="${4:-heap arena}"
CHAIN_LENS="${5:-256}"
RUN_TIMEOUT_SEC="${RUN_TIMEOUT_SEC:-150}"

RESULTS_FILE="${RESULTS_FILE:-scripts/gc-bench-arena-results.csv}"
LOG_FILE="scripts/gc-bench-matrix.log"

PERF_CONFIG='.withCheck(false).withCheckFatalWarnings(false).withSourceLevelDebuggingConfig(_.disableAll).withLTO(scala.scalanative.build.LTO.thin).withDump(false)'

if [[ ! -f "$RESULTS_FILE" ]]; then
  echo "mode,gc,threads,chainLen,elapsedSec,allocations,allocPerSec,nodeBytes,bytesPerSec,gcCollections,gcTimeMs,gcTimeShare" > "$RESULTS_FILE"
fi

: > "$LOG_FILE"

for mode in $MODES; do
for gc in $GCS; do
  echo "==> Setting nativeConfig GC=$gc (mode=$mode)" | tee -a "$LOG_FILE"
  for chainLen in $CHAIN_LENS; do
  for threads in $THREAD_COUNTS; do
    echo "==> Running mode=$mode gc=$gc threads=$threads chainLen=$chainLen duration=${DURATION_SEC}s" | tee -a "$LOG_FILE"

    TMP_OUT=$(mktemp)
    BENCH_MODE="$mode" BENCH_THREADS="$threads" BENCH_DURATION_SEC="$DURATION_SEC" \
    BENCH_CHAIN_LEN="$chainLen" \
      sbt -Dscala.scalanative.multithreading.enable=true \
        "set sandbox.forBinaryVersion(\"3\")/nativeConfig ~= (_.withGC(scala.scalanative.build.GC(\"$gc\"))$PERF_CONFIG)" \
        "set sandbox.forBinaryVersion(\"3\")/Compile/mainClass := Some(\"GcPauseBench\")" \
        "sandbox3/run" > "$TMP_OUT" 2>&1 &
    SBT_PID=$!

    waited=0
    timed_out=0
    while kill -0 "$SBT_PID" 2>/dev/null; do
      sleep 2
      waited=$((waited + 2))
      if [[ $waited -ge $RUN_TIMEOUT_SEC ]]; then
        timed_out=1
        echo "!! TIMEOUT after ${RUN_TIMEOUT_SEC}s for mode=$mode gc=$gc threads=$threads chainLen=$chainLen, killing pid=$SBT_PID (likely GC hang)" | tee -a "$LOG_FILE"
        pkill -9 -P "$SBT_PID" 2>/dev/null
        kill -9 "$SBT_PID" 2>/dev/null
        break
      fi
    done
    wait "$SBT_PID" 2>/dev/null

    cat "$TMP_OUT" | tee -a "$LOG_FILE" > /dev/null
    OUTPUT=$(cat "$TMP_OUT")
    rm -f "$TMP_OUT"

    if [[ $timed_out -eq 1 ]]; then
      echo "$mode,$gc,$threads,$chainLen,TIMEOUT,,,,,,," >> "$RESULTS_FILE"
      continue
    fi

    LINE=$(echo "$OUTPUT" | grep -E '^mode=' || true)
    if [[ -z "$LINE" ]]; then
      echo "!! No benchmark output found for mode=$mode gc=$gc threads=$threads chainLen=$chainLen, see $LOG_FILE" >&2
      echo "$mode,$gc,$threads,$chainLen,ERROR,,,,,,," >> "$RESULTS_FILE"
      continue
    fi

    # parse "mode=M threads=T chainLen=L elapsedSec=E allocations=A
    # allocPerSec=P nodeBytes=B bytesPerSec=BS gcCollections=C gcTimeMs=T
    # gcTimeShare=S sink=X"
    # (plain vars, not associative arrays: macOS ships bash 3.2)
    v_threads=""; v_chainLen=""; v_elapsedSec=""; v_allocations=""; v_allocPerSec=""
    v_nodeBytes=""; v_bytesPerSec=""
    v_gcCollections=""; v_gcTimeMs=""; v_gcTimeShare=""
    for pair in $LINE; do
      key="${pair%%=*}"
      val="${pair#*=}"
      case "$key" in
        threads) v_threads="$val" ;;
        chainLen) v_chainLen="$val" ;;
        elapsedSec) v_elapsedSec="$val" ;;
        allocations) v_allocations="$val" ;;
        allocPerSec) v_allocPerSec="$val" ;;
        nodeBytes) v_nodeBytes="$val" ;;
        bytesPerSec) v_bytesPerSec="$val" ;;
        gcCollections) v_gcCollections="$val" ;;
        gcTimeMs) v_gcTimeMs="$val" ;;
        gcTimeShare) v_gcTimeShare="$val" ;;
      esac
    done

    echo "$mode,$gc,$v_threads,$v_chainLen,$v_elapsedSec,$v_allocations,$v_allocPerSec,$v_nodeBytes,$v_bytesPerSec,$v_gcCollections,$v_gcTimeMs,$v_gcTimeShare" >> "$RESULTS_FILE"
  done
  done
done
done

echo "Done. Results in $RESULTS_FILE"
