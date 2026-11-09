#!/bin/sh
# Cross-check casing against Alloy 6: each casing/tests/NAME.cs that has
# NAME.als (and maybe NAME.*.als) here is run by both, and each command's
# verdict compared: an instance or counterexample found, or not.
#
# In a .als, each command follows a marker naming the casing command it
# stands for, counting from 1 in the .cs:
#   --# 3                    command 3; the verdicts must agree
#   --# 3 differs: why       command 3; they are meant to differ (casing
#                            is not Alloy here), and must
# and a casing command that cannot be said in Alloy is listed so:
#   --# 4 skip: why
# A line `--# options: -n` passes options to Alloy's exec (-n: noOverflow).
#
#   xcheck.sh [NAME …]       those models; all if none named
# Alloy is $ALLOY_JAR (default ~/Dev/LangPlay/alloy-6.2.0/
# org.alloytools.alloy.dist.jar), run by $JAVA (default openjdk.java, or
# java), which must be Java 17 or later.
here=$(cd "$(dirname "$0")" && pwd)
tests="$here/../tests"
casing="$here/../../bin/casing"
jar=${ALLOY_JAR:-$HOME/Dev/LangPlay/alloy-6.2.0/org.alloytools.alloy.dist.jar}
java=${JAVA:-$(command -v openjdk.java || command -v java)}
[ -f "$jar" ] || { echo "no Alloy jar at $jar (set ALLOY_JAR)"; exit 2; }
work=$(mktemp -d "${TMPDIR:-/tmp}/xcheck.XXXXXX")
trap 'rm -rf "$work"' EXIT

if [ $# -eq 0 ]; then
  set -- $(ls "$here"/*.als | sed 's,.*/,,; s,\..*,,' | sort -u)
fi

status=0; agree=0; differ=0; skip=0; bad=0; unchecked=0
for name in "$@"; do
  name=$(basename "$name" .cs)
  [ -f "$tests/$name.cs" ] || { echo "FAIL $name: no tests/$name.cs"; status=1; continue; }
  # casing's verdicts, one per line: sat or unsat
  (cd "$tests" && "$casing" "$name.cs" 2>&1) > "$work/$name.casing"
  grep -E '^(run|check) .*: (no )?(instance|counterexample) found' "$work/$name.casing" \
    | sed -E 's/.*: no (instance|counterexample) found.*/unsat/; t; s/.*: (instance|counterexample) found.*/sat/' \
    > "$work/$name.cv"
  n=$(wc -l < "$work/$name.cv")
  : > "$work/$name.seen"
  for als in "$here/$name.als" "$here/$name".*.als; do
    [ -f "$als" ] || continue
    a=$(basename "$als")
    opts=$(sed -n 's/^--# options: *//p' "$als")
    out="$work/out-$a"
    (cd "$work" && "$java" --enable-native-access=ALL-UNNAMED -jar "$jar" \
       exec -f $opts -o "$work/sol-$a" -c '*' "$als" 2>&1) > "$out"
    # Alloy's verdicts, in order: SAT or UNSAT (an error stops the file)
    grep -E '^[0-9]+\. +(run|check) ' "$out" | awk '{print $NF}' > "$work/$a.av"
    # the markers, in order, each before a command
    grep -E '^--# [0-9]+( |$)' "$als" | grep -v ' skip:' > "$work/$a.marks"
    grep -E '^--# [0-9]+ skip:' "$als" | while read -r _ i _ why; do
      echo "$i" >> "$work/$name.seen"
      echo "  skip  $name #$i: $why"
    done
    nm=$(wc -l < "$work/$a.marks"); na=$(wc -l < "$work/$a.av")
    if [ "$nm" -ne "$na" ]; then
      echo "FAIL $a: $nm marked commands, Alloy ran $na"; sed 's/^/  | /' "$out" | grep -v WARNING
      status=1; bad=$((bad + nm)); continue
    fi
    j=0
    while read -r _ i rest; do
      j=$((j + 1)); echo "$i" >> "$work/$name.seen"
      av=$(sed -n "${j}p" "$work/$a.av" | tr 'A-Z' 'a-z')
      cv=$(sed -n "${i}p" "$work/$name.cv")
      [ -n "$cv" ] || { echo "FAIL $a: marker $i, but $name.cs has $n commands"; status=1; bad=$((bad + 1)); continue; }
      case "$rest" in
        differs:*)
          if [ "$av" != "$cv" ]; then differ=$((differ + 1)); echo "  differ $name #$i: casing $cv, Alloy $av (${rest#differs: })"
          else echo "FAIL $name #$i: meant to differ, but both $cv (${rest#differs: })"; status=1; bad=$((bad + 1)); fi;;
        *)
          if [ "$av" = "$cv" ]; then agree=$((agree + 1))
          else echo "FAIL $name #$i: casing $cv, Alloy $av"; status=1; bad=$((bad + 1)); fi;;
      esac
    done < "$work/$a.marks"
  done
  i=1
  while [ "$i" -le "$n" ]; do
    grep -qx "$i" "$work/$name.seen" || { echo "  not checked: $name #$i"; unchecked=$((unchecked + 1)); }
    i=$((i + 1))
  done
  skip=$((skip + $(cat "$here/$name.als" "$here/$name".*.als 2>/dev/null | grep -c '^--# [0-9]* skip:')))
  echo "done $name"
done
echo "agree $agree, differ as meant $differ, skipped $skip, not checked $unchecked, failed $bad"
exit $status
