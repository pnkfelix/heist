#!/bin/sh
# The CFA's tests: each NAME.fx or NAME.scm analysed by bin/cfa (as a world
# of its own, at the depth its first line says, `;;; depth: N`, else 0),
# its notes compared with NAME.fx.out (NAME.scm.out). UPDATE=1 writes them.
#   run.sh [FILE …]    those tests (NAME.fx, NAME.scm); all if none named
here=$(cd "$(dirname "$0")" && pwd)
cfa="$here/../../bin/cfa"
status=0
if [ $# -gt 0 ]; then
  for n in "$@"; do n=$(basename "$n")
    [ -e "$here/$n" ] || { echo "FAIL $n: no such test"; exit 1; }
    tests="$tests $here/$n"
  done
  set -- $tests
else
  set -- "$here"/*.fx "$here"/*.scm
fi
for t in "$@"; do
  [ -e "$t" ] || continue
  name=$(basename "$t")
  depth=$(sed -n '1s/^;;; depth: //p' "$t")
  got=$({ cd "$here" && "$cfa" -m "${depth:-0}" "$(basename "$t")" 2>&1; echo "[exit $?]"; })
  if [ -n "$UPDATE" ]; then
    printf '%s\n' "$got" > "$here/$name.out"; echo "wrote $name.out"
  elif [ "$got" = "$(cat "$here/$name.out" 2>/dev/null)" ]; then
    echo "ok   $name"
  else
    echo "FAIL $name"; printf '%s\n' "$got" | diff "$here/$name.out" - | sed 's/^/  /'; status=1
  fi
done
exit $status
