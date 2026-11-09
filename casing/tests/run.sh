#!/bin/sh
# casing's tests: each NAME.cs, a model, run by bin/casing, and each
# NAME.fx (a program of casing's modules) run by Fixpt; what it writes,
# and its exit status, compared with FILE.out. UPDATE=1 writes them.
#   run.sh [FILE …]    those tests; all if none named
here=$(cd "$(dirname "$0")" && pwd)
casing="$here/../../bin/casing"
status=0
if [ $# -gt 0 ]; then
  for n in "$@"; do n=$(basename "$n")
    [ -e "$here/$n" ] || { echo "FAIL $n: no such test"; exit 1; }
    tests="$tests $here/$n"
  done
  set -- $tests
else
  set -- "$here"/*.cs "$here"/*.fx
fi
for t in "$@"; do
  [ -e "$t" ] || continue
  name=$(basename "$t")
  got=$(cd "$here" && case "$name" in
    *.cs) "$casing" --check-symmetry "$name" 2>&1; echo "[exit $?]";;
    *.fx) "$here/../../fixpt/target/release/fixpt" run "$name" 2>&1; echo "[exit $?]";;
  esac)
  if [ -n "$UPDATE" ]; then
    printf '%s\n' "$got" > "$here/$name.out"; echo "wrote $name.out"
  elif [ "$got" = "$(cat "$here/$name.out" 2>/dev/null)" ]; then
    echo "ok   $name"
  else
    echo "FAIL $name"; printf '%s\n' "$got" | diff "$here/$name.out" - | sed 's/^/  /'; status=1
  fi
done
exit $status
