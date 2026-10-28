#!/bin/sh
# The editor driven through a pseudo-terminal (drive.py): each ui/NAME.keys
# is a scenario -- its first line the file's text (\n for newlines), the
# rest the keys, one argument of drive.py a line -- and ui/NAME.screen
# what the screen must show at the end.
#   ui.sh [NAME …]             those scenarios; all if none named
#   ui.sh --update [NAME …]    their screens written instead (or UPDATE=1)
here=$(cd "$(dirname "$0")" && pwd)
tmp=$(mktemp -d /tmp/heist-ui.XXXXXX)
trap 'rm -rf "$tmp"' EXIT
status=0
update=${UPDATE:-}
[ "$1" = "--update" ] && { update=1; shift; }
[ $# -gt 0 ] || set -- "$here"/ui/*.keys
for k in "$@"; do
  k="$here/ui/$(basename "$k" .keys).keys"
  name=$(basename "$k" .keys)
  # A scenario named *.fx is of an FX-26 file, its faces shown too; *.scm,
  # of a Scheme file, its faces too (s7st's analysis, scheme.fx).
  case "$name" in *.fx) file=a.fx; faces=--faces;; *.scm) file=a.scm; faces=--faces;; *) file=a.txt; faces=;; esac
  mkdir -p "$tmp/$name"
  head -1 "$k" | sed 's/\\n/\n/g' > "$tmp/$name/$file"
  printf 'second file\nhere\n' > "$tmp/$name/b.txt"
  # Keys: one drive.py argument per line (in a function, whose own
  # arguments they are, so the scenarios' list stays the script's).
  keys() { set --
    while IFS= read -r line; do set -- "$@" "$line"; done <<KEYS
$(tail -n +2 "$k")
KEYS
    "$here/drive.py" --rows 12 --cols 40 $faces --file "$file" "$@"; }
  # The scenario's directory, which listings show, as TMP.
  got=$(cd "$tmp/$name" && keys | sed -e "s|$tmp/$name|TMP|g" -e "s|$tmp|TMP|g")
  if [ -n "$update" ]; then
    printf '%s\n' "$got" > "$here/ui/$name.screen"; echo "wrote $name.screen"
  elif [ "$got" = "$(cat "$here/ui/$name.screen")" ]; then
    echo "ok   ui/$name"
  else
    echo "FAIL ui/$name"; printf '%s\n' "$got" | diff "$here/ui/$name.screen" - | sed 's/^/  /'; status=1
  fi
done
exit $status
