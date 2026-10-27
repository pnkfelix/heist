#!/bin/sh
# s7st's tests: each NAME.scm run by bin/s7st, its output (and exit
# status) compared with NAME.out. UPDATE=1 writes NAME.out instead.
here=$(cd "$(dirname "$0")" && pwd)
s7st="$here/../../bin/s7st"
status=0
if ! python3 "$here/../gen-prelude.py" --check; then
  echo "FAIL prelude.fx is not prelude.scm's: run s7st/gen-prelude.py"
  status=1
fi
for t in "$here"/*.scm; do
  name=$(basename "$t" .scm)
  # The tests' directory taken out of what errors say, so it is the same anywhere.
  got=$({ "$s7st" "$t" 2>&1; echo "[exit $?]"; } | sed "s|$here/||g")
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
