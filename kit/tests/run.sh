#!/bin/sh
# kit's tests: each NAME-test.fx is checked by `fixpt check` (refused at
# nothing, both checkers agreeing) and run by `fixpt run`, whose asserts
# fail the run on a wrong answer, and which ends by writing "NAME: ok".
#   run.sh [NAME …]    those tests; all if none named
here=$(cd "$(dirname "$0")" && pwd)
fixpt="$here/../../fixpt/target/release/fixpt"
status=0
if [ $# -eq 0 ]; then
  set --; for f in "$here"/*-test.fx; do n=$(basename "$f" -test.fx); set -- "$@" "$n"; done
fi
for n in "$@"; do
  t="$n-test.fx"
  [ -e "$here/$t" ] || { echo "FAIL $n: no such test"; status=1; continue; }
  checked=$(cd "$here" && "$fixpt" check "$t" 2>&1)
  if printf '%s\n' "$checked" | grep -q '^!' || ! printf '%s\n' "$checked" | grep -q '^; both checkers agree$'; then
    echo "FAIL $n: check"; printf '%s\n' "$checked" | grep -v '^define \|^(' | sed 's/^/  /'; status=1; continue
  fi
  ran=$(cd "$here" && "$fixpt" run "$t" 2>&1); code=$?
  if [ $code -eq 0 ] && [ "$ran" = "$n: ok" ]; then
    echo "ok   $n"
  else
    echo "FAIL $n: run (exit $code)"; printf '%s\n' "$ran" | sed 's/^/  /'; status=1
  fi
done
exit $status
