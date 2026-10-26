#!/bin/sh
# The editor's module tests, on Heist's own build of Fixpt (fixpt/).
# A test passes if it prints no line starting with FAIL and exits 0.
here=$(cd "$(dirname "$0")" && pwd)
fixpt="$here/../../fixpt/target/release/fixpt"
[ -x "$fixpt" ] || { echo "build fixpt first: (cd fixpt && cargo build --release -p fixpt-cli)"; exit 2; }
status=0
for t in "$here"/*-test.fx; do
  out=$(cd "$here" && "$fixpt" run "$(basename "$t")" 2>&1)
  code=$?
  if [ $code -ne 0 ] || echo "$out" | grep -q '^FAIL'; then
    echo "FAIL $(basename "$t") (exit $code)"; echo "$out" | sed 's/^/  /'; status=1
  else
    echo "ok   $(basename "$t")"
  fi
done
exit $status
