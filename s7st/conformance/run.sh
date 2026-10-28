#!/bin/sh
# s7st against Larceny's R7RS test suite (test/R7RS/Lib/tests/scheme/),
# read from the sibling repository ~/Dev/LangPlay/inthematrix-rrof at a
# pinned commit, into a directory of its own: nothing of it is copied here.
#   s7st/conformance/run.sh [LIBRARY …]    each driver's summary; all of
#                                          R7RS-small's if none named
#   VERBOSE=1 …                            each failure, too
here=$(cd "$(dirname "$0")" && pwd)
s7st="$here/../../bin/s7st"
repo="${R7RS_TESTS_REPO:-$HOME/Dev/LangPlay/inthematrix-rrof}"
commit=d184ff8d
tmp=$(mktemp -d /tmp/s7st-r7rs.XXXXXX)
trap 'rm -rf "$tmp"' EXIT
git -C "$repo" archive "$commit" test/R7RS/Lib | tar -x -C "$tmp" || { echo "cannot read $repo at $commit"; exit 2; }
cd "$tmp/test/R7RS/Lib" || exit 2
libs="$*"
[ -n "$libs" ] || libs="base case-lambda char complex cxr eval file inexact lazy load process-context read repl time write"
for lib in $libs; do
  out=$(timeout 600 "$s7st" -L . "tests/scheme/run/$lib.sps" 2>&1)
  summary=$(printf '%s\n' "$out" | grep -E "tests? (passed|failed)|Error:" | tail -1)
  printf '%-16s %s\n' "$lib" "${summary:-(no summary)}"
  [ -n "$VERBOSE" ] && printf '%s\n' "$out" | sed 's/^/    /'
done
