#!/bin/sh
# The editor's module tests, on Heist's own build of Fixpt (fixpt/).
# A test passes if it prints no line starting with FAIL and exits 0.
here=$(cd "$(dirname "$0")" && pwd)
fixpt="$here/../../fixpt/target/release/fixpt"
[ -x "$fixpt" ] || { echo "build fixpt first: (cd fixpt && cargo build --release -p fixpt-cli)"; exit 2; }
status=0
for t in "$here"/*-test.fx; do
  # A test that uses the editor's files says which (`;;; needs: a.fx …`),
  # and its arguments (`;;; args: …`). It runs in editor/, after a prelude
  # that makes the modules of editor.fx up to the last file it needs (each
  # made of all those before it) and includes them.
  needs=$(sed -n 's/^;;; needs: //p' "$t")
  args=$(sed -n 's/^;;; args: //p' "$t")
  if [ -n "$needs" ]; then
    last=$(basename "${needs##* }" .fx)
    prelude="$here/../prelude-$$.fx"
    { sed -n "1,/^(define m-$last /p" "$here/../editor.fx"
      sed -n "s/^(define \(m-[^ ]*\) .*/(include \1)/p; /^(define m-$last /q" "$here/../editor.fx"
    } > "$prelude"
    out=$(cd "$here/.." && "$fixpt" run "$(basename "$prelude")" "tests/$(basename "$t")" -- $(for a in $args; do echo "tests/$a"; done) 2>&1)
    rm -f "$prelude"
  else
    out=$(cd "$here" && "$fixpt" run "$(basename "$t")" 2>&1)
  fi
  code=$?
  # The notes of globals redefined across the files, dropped.
  out=$(printf '%s\n' "$out" | grep -v '^; ' || true)
  if [ $code -ne 0 ] || echo "$out" | grep -q '^FAIL'; then
    # Where the test ran, as make says it, for M-x compile's next-error.
    if [ -n "$needs" ]; then dir="$here/.."; else dir="$here"; fi
    echo "FAIL $(basename "$t") (exit $code)"
    echo "run.sh: Entering directory '$(cd "$dir" && pwd)'"
    echo "$out" | sed 's/^/  /'
    echo "run.sh: Leaving directory '$(cd "$dir" && pwd)'"
    status=1
  else
    echo "ok   $(basename "$t")"
  fi
done
exit $status
