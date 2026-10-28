#!/bin/sh
# s7st's tests: each NAME.scm run by bin/s7st, and each NAME.serve given
# to `bin/s7st --serve` as its requests; the output (and exit status)
# compared with NAME.out. UPDATE=1 writes NAME.out instead.
#   run.sh [NAME …]    those tests (NAME.scm or NAME.serve); all if none
#                      named, and the check that prelude.fx is prelude.scm's
here=$(cd "$(dirname "$0")" && pwd)
s7st="$here/../../bin/s7st"
status=0
if [ $# -gt 0 ]; then
  for n in "$@"; do n=$(basename "$n"); n=${n%.scm}; n=${n%.serve}
    found=
    for t in "$here/$n.scm" "$here/$n.serve"; do [ -e "$t" ] && { tests="$tests $t"; found=1; }; done
    [ -n "$found" ] || { echo "FAIL $n: no $n.scm or $n.serve"; exit 1; }
  done
  set -- $tests
elif ! python3 "$here/../gen-prelude.py" --check; then
  echo "FAIL prelude.fx is not prelude.scm's: run s7st/gen-prelude.py"
  status=1
fi
[ $# -gt 0 ] || set -- "$here"/*.scm "$here"/*.serve
for t in "$@"; do
  case "$t" in
    *.scm) name=$(basename "$t" .scm)
           # The tests' directory taken out of what errors say, so it is the same anywhere.
           got=$({ "$s7st" "$t" 2>&1; echo "[exit $?]"; } | sed "s|$here/||g");;
    *) name=$(basename "$t" .serve)
       got=$({ "$s7st" --serve < "$t" 2>&1; echo "[exit $?]"; });;
  esac
  if [ -n "$UPDATE" ]; then
    printf '%s\n' "$got" > "$here/$name.out"
    echo "wrote $name.out"
  elif [ "$got" = "$(cat "$here/$name.out" 2>/dev/null)" ]; then
    echo "ok   $name"
  else
    echo "FAIL $name"
    printf '%s\n' "$got" | diff "$here/$name.out" - | sed 's/^/  /'
    status=1
  fi
done
exit $status
