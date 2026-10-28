#!/bin/sh
# combo's tests: each NAME.smt2 run by bin/combo, each NAME.cnf by
# `bin/combo --dimacs NAME.cnf --stats` (so that the search itself is
# checked) and with --no-elim, each NAME.icnf by --icnf, each NAME.serve's
# requests given to `bin/combo --serve`, each NAME.fx (a program that
# links combo in) run by Fixpt; what it writes, and its exit
# status, compared with FILE.out. UPDATE=1 writes them. The .out files of
# the .smt2, .cnf and .icnf tests are lockpick's own answers (at 2bae0a4,
# lockpick's stderr aside): combo's searches and models are its.
#   run.sh [FILE …]    those tests; all if none named
here=$(cd "$(dirname "$0")" && pwd)
combo="$here/../../bin/combo"
status=0
if [ $# -gt 0 ]; then
  for n in "$@"; do n=$(basename "$n")
    [ -e "$here/$n" ] || { echo "FAIL $n: no such test"; exit 1; }
    tests="$tests $here/$n"
  done
  set -- $tests
else
  set -- "$here"/*.smt2 "$here"/*.cnf "$here"/*.icnf "$here"/*.serve "$here"/*.fx
fi
for t in "$@"; do
  [ -e "$t" ] || continue
  name=$(basename "$t")
  got=$(cd "$here" && case "$name" in
    *.smt2) "$combo" "$name" 2>/dev/null; echo "[exit $?]";;
    *.cnf) "$combo" --dimacs "$name" --stats 2>&1; echo "[exit $?]"
           "$combo" --dimacs "$name" --stats --no-elim 2>&1; echo "[exit $?]";;
    *.icnf) "$combo" --icnf "$name" 2>&1; echo "[exit $?]";;
    *.serve) "$combo" --serve < "$name" 2>&1; echo "[exit $?]";;
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
