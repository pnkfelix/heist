#!/bin/sh
# s7st/bench/run.sh [LARCENY]: the benchmarks in body.scm, timed by runs.scm,
# on s7st and, if LARCENY (a `larceny` script) is given, on Larceny's
# interpreter and compiler. Each prints a time per run.
here=$(cd "$(dirname "$0")" && pwd)
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
{ cat "$here/body.scm"; sed 's/ R / 3 /' "$here/runs.scm"; } > "$tmp/s7.scm"
echo "== s7st"; "$here/../../bin/s7st" "$tmp/s7.scm"
[ -n "$1" ] || exit 0
cp "$tmp/s7.scm" "$tmp/int.scm"
echo "== Larceny, interpreted"
(cd "$tmp" && printf '(import (scheme base) (scheme write) (scheme time) (scheme load) (primitives evaluator interpret))\n(evaluator interpret)\n(load "int.scm")\n' \
   | "$1" -r7rs 2>&1 | grep ' ms' | sed 's/^> //')
{ echo '(import (scheme base) (scheme write) (scheme time))'; cat "$here/body.scm"; sed 's/ R / 20 /' "$here/runs.scm"; } > "$tmp/c.sps"
echo "== Larceny, compiled"
(cd "$tmp" && "$1" -r7rs -program c.sps 2>&1 | grep ' ms')
