#!/bin/sh
# The editor driven through a pseudo-terminal (drive.py): each ui/NAME.keys
# is a scenario -- its first line the file's text (\n for newlines), the
# rest the keys, one argument of drive.py a line -- and ui/NAME.screen
# what the screen must show at the end. `ui.sh --update` writes the
# screens instead.
here=$(cd "$(dirname "$0")" && pwd)
tmp=$(mktemp -d /tmp/heist-ui.XXXXXX)
trap 'rm -rf "$tmp"' EXIT
status=0
for k in "$here"/ui/*.keys; do
  name=$(basename "$k" .keys)
  # A scenario named *.fx is of an FX-26 file, its faces shown too.
  case "$name" in *.fx) file=a.fx; faces=--faces;; *) file=a.txt; faces=;; esac
  mkdir -p "$tmp/$name"
  head -1 "$k" | sed 's/\\n/\n/g' > "$tmp/$name/$file"
  printf 'second file\nhere\n' > "$tmp/$name/b.txt"
  # Keys: one drive.py argument per line.
  set --
  while IFS= read -r line; do set -- "$@" "$line"; done <<KEYS
$(tail -n +2 "$k")
KEYS
  # The scenario's directory, which listings show, as TMP.
  got=$(cd "$tmp/$name" && "$here/drive.py" --rows 12 --cols 40 $faces --file "$file" "$@" | sed -e "s|$tmp/$name|TMP|g" -e "s|$tmp|TMP|g")
  if [ "$1" = "--update" ] || [ "${UPDATE:-}" = 1 ]; then
    printf '%s\n' "$got" > "$here/ui/$name.screen"; echo "wrote $name.screen"
  elif [ "$got" = "$(cat "$here/ui/$name.screen")" ]; then
    echo "ok   ui/$name"
  else
    echo "FAIL ui/$name"; printf '%s\n' "$got" | diff "$here/ui/$name.screen" - | sed 's/^/  /'; status=1
  fi
done
exit $status
