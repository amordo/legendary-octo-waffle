#!/usr/bin/env bash
# DEBS 2015 Grand Challenge query 1 ("frequent routes") replayed from the NYC
# taxi trip file by sandbox/src/main/scala/DebsQ1Bench.scala. Produces one line
# of metrics per run in scripts/debs-q1-results.csv.
#
# Usage:
#   DEBS_FILE=/path/to/sorted_data.csv scripts/debs-q1-bench.sh [mode-list] [gc-list] [limit]
# Examples:
#   DEBS_FILE=~/data/debs2015.csv scripts/debs-q1-bench.sh
#   DEBS_FILE=~/data/debs2015.csv scripts/debs-q1-bench.sh offheap immix 200000
#
# Modes: 'heap' (LongMap of route objects, one event object per trip) and
# 'offheap' (the same graph flattened into malloc'd primitive arrays). Both run
# the same algorithm over the same raw-byte reader, so the only variable is how
# the operator state is represented. Under 'offheap' the GC axis only affects
# incidental runtime allocations -- gcCollections is expected to be 0 there, and
# a non-zero value means something on the path started allocating again.
#
# The data file is not redistributable; download it from
# https://debs.org/grand-challenges/2015/ (20-day extract ~130 MB, full year
# ~12 GB) and point DEBS_FILE at it.
#
# As in scripts/gc-bench-matrix.sh, this overrides the repo-wide nativeConfig
# from project/MyScalaNativePlugin.scala, which forces check/dump and full
# source-level debugging on every project. Those are compiler-development
# settings and cost the GC-managed path about a factor of two.
set -uo pipefail
cd "$(dirname "$0")/.."

MODES="${1:-heap offheap}"
GCS="${2:-immix}"
LIMIT="${3:-0}"
RUN_TIMEOUT_SEC="${RUN_TIMEOUT_SEC:-900}"

if [[ -z "${DEBS_FILE:-}" ]]; then
  echo "DEBS_FILE must point at the DEBS 2015 trip CSV" >&2
  exit 1
fi
if [[ ! -f "$DEBS_FILE" ]]; then
  echo "DEBS_FILE '$DEBS_FILE' does not exist" >&2
  exit 1
fi

RESULTS_FILE="${RESULTS_FILE:-scripts/debs-q1-results.csv}"
LOG_FILE="scripts/debs-q1-bench.log"

PERF_CONFIG='.withCheck(false).withCheckFatalWarnings(false).withSourceLevelDebuggingConfig(_.disableAll).withLTO(scala.scalanative.build.LTO.none).withDump(false)'

CSV_HEADER="mode,gc,events,outliers,malformed,bytes,elapsedSec,eventsPerSec,bytesPerSec,outputs,distinctRoutes,windowSize,delaySamples,delayMeanNs,delayP50Ns,delayP99Ns,delayP999Ns,delayMaxNs,gcCollections,gcTimeMs,gcTimeShare,rssPeakBytes,rssGrowthBytes,gcHeapUsedBytes,gcHeapMaxBytes"
if [[ "$(head -n1 "$RESULTS_FILE" 2>/dev/null)" != "$CSV_HEADER" ]]; then
  { echo "$CSV_HEADER"; cat "$RESULTS_FILE" 2>/dev/null; } > "$RESULTS_FILE.tmp"
  mv "$RESULTS_FILE.tmp" "$RESULTS_FILE"
fi

: > "$LOG_FILE"

for mode in $MODES; do
for gc in $GCS; do
  echo "==> Running mode=$mode gc=$gc limit=$LIMIT file=$DEBS_FILE" | tee -a "$LOG_FILE"

  TMP_OUT=$(mktemp)
  DEBS_FILE="$DEBS_FILE" BENCH_MODE="$mode" BENCH_LIMIT="$LIMIT" \
    sbt "set sandbox.forBinaryVersion(\"3\")/nativeConfig ~= (_.withGC(scala.scalanative.build.GC(\"$gc\"))$PERF_CONFIG)" \
      "set sandbox.forBinaryVersion(\"3\")/Compile/mainClass := Some(\"DebsQ1Bench\")" \
      "sandbox3/run" > "$TMP_OUT" 2>&1 &
  SBT_PID=$!

  waited=0
  timed_out=0
  while kill -0 "$SBT_PID" 2>/dev/null; do
    sleep 2
    waited=$((waited + 2))
    if [[ $waited -ge $RUN_TIMEOUT_SEC ]]; then
      timed_out=1
      echo "!! TIMEOUT after ${RUN_TIMEOUT_SEC}s for mode=$mode gc=$gc, killing pid=$SBT_PID" | tee -a "$LOG_FILE"
      pkill -9 -P "$SBT_PID" 2>/dev/null
      kill -9 "$SBT_PID" 2>/dev/null
      break
    fi
  done
  wait "$SBT_PID" 2>/dev/null

  cat "$TMP_OUT" >> "$LOG_FILE"
  OUTPUT=$(cat "$TMP_OUT")
  rm -f "$TMP_OUT"

  if [[ $timed_out -eq 1 ]]; then
    echo "$mode,$gc,TIMEOUT" >> "$RESULTS_FILE"
    continue
  fi

  LINE=$(echo "$OUTPUT" | grep -E '^mode=' || true)
  if [[ -z "$LINE" ]]; then
    echo "!! No benchmark output for mode=$mode gc=$gc, see $LOG_FILE" >&2
    echo "$mode,$gc,ERROR" >> "$RESULTS_FILE"
    continue
  fi

  # parse the single "key=value ..." summary line (plain vars, not associative
  # arrays: macOS ships bash 3.2)
  v_events=""; v_outliers=""; v_malformed=""; v_bytes=""; v_elapsedSec=""
  v_eventsPerSec=""; v_bytesPerSec=""; v_outputs=""; v_distinctRoutes=""
  v_windowSize=""; v_delaySamples=""; v_delayMeanNs=""; v_delayP50Ns=""
  v_delayP99Ns=""; v_delayP999Ns=""; v_delayMaxNs=""; v_gcCollections=""
  v_gcTimeMs=""; v_gcTimeShare=""; v_rssPeakBytes=""; v_rssGrowthBytes=""
  v_gcHeapUsedBytes=""; v_gcHeapMaxBytes=""
  for pair in $LINE; do
    key="${pair%%=*}"
    val="${pair#*=}"
    case "$key" in
      events) v_events="$val" ;;
      outliers) v_outliers="$val" ;;
      malformed) v_malformed="$val" ;;
      bytes) v_bytes="$val" ;;
      elapsedSec) v_elapsedSec="$val" ;;
      eventsPerSec) v_eventsPerSec="$val" ;;
      bytesPerSec) v_bytesPerSec="$val" ;;
      outputs) v_outputs="$val" ;;
      distinctRoutes) v_distinctRoutes="$val" ;;
      windowSize) v_windowSize="$val" ;;
      delaySamples) v_delaySamples="$val" ;;
      delayMeanNs) v_delayMeanNs="$val" ;;
      delayP50Ns) v_delayP50Ns="$val" ;;
      delayP99Ns) v_delayP99Ns="$val" ;;
      delayP999Ns) v_delayP999Ns="$val" ;;
      delayMaxNs) v_delayMaxNs="$val" ;;
      gcCollections) v_gcCollections="$val" ;;
      gcTimeMs) v_gcTimeMs="$val" ;;
      gcTimeShare) v_gcTimeShare="$val" ;;
      rssPeakBytes) v_rssPeakBytes="$val" ;;
      rssGrowthBytes) v_rssGrowthBytes="$val" ;;
      gcHeapUsedBytes) v_gcHeapUsedBytes="$val" ;;
      gcHeapMaxBytes) v_gcHeapMaxBytes="$val" ;;
    esac
  done

  echo "$mode,$gc,$v_events,$v_outliers,$v_malformed,$v_bytes,$v_elapsedSec,$v_eventsPerSec,$v_bytesPerSec,$v_outputs,$v_distinctRoutes,$v_windowSize,$v_delaySamples,$v_delayMeanNs,$v_delayP50Ns,$v_delayP99Ns,$v_delayP999Ns,$v_delayMaxNs,$v_gcCollections,$v_gcTimeMs,$v_gcTimeShare,$v_rssPeakBytes,$v_rssGrowthBytes,$v_gcHeapUsedBytes,$v_gcHeapMaxBytes" >> "$RESULTS_FILE"
done
done

echo "Done. Results in $RESULTS_FILE"
