#!/bin/sh
# The editor's module tests, on Heist's own build of Fixpt (fixpt/).
# A test passes if it prints no line starting with FAIL and exits 0.
here=$(cd "$(dirname "$0")" && pwd)
fixpt="$here/../../fixpt/target/release/fixpt"
[ -x "$fixpt" ] || { echo "build fixpt first: (cd fixpt && cargo build --release -p fixpt-cli)"; exit 2; }
status=0
for t in "$here"/*-test.fx; do
  # A test that uses the editor's files says which (`;;; needs: a.fx …`),
  # and its arguments (`;;; args: …`); it runs after them, in editor/.
  needs=$(sed -n 's/^;;; needs: //p' "$t")
  args=$(sed -n 's/^;;; args: //p' "$t")
  if [ -n "$needs" ]; then
    out=$(cd "$here/.." && "$fixpt" run $needs "tests/$(basename "$t")" -- $(for a in $args; do echo "tests/$a"; done) 2>&1)
  else
    out=$(cd "$here" && "$fixpt" run "$(basename "$t")" 2>&1)
  fi
  code=$?
  # The notes of globals redefined across the files, dropped.
  out=$(printf '%s\n' "$out" | grep -v '^; ' || true)
  if [ $code -ne 0 ] || echo "$out" | grep -q '^FAIL'; then
    echo "FAIL $(basename "$t") (exit $code)"; echo "$out" | sed 's/^/  /'; status=1
  else
    echo "ok   $(basename "$t")"
  fi
done
exit $status
