#!/usr/bin/env python3
"""Make s7st/prelude.fx from s7st/prelude.scm: the Scheme text as one
FX-26 string, `s7-prelude`, which session.fx's `s7-init!` runs.

    s7st/gen-prelude.py            write prelude.fx
    s7st/gen-prelude.py --check    exit 1 if prelude.fx is not what it would write
"""
import os, sys

here = os.path.dirname(os.path.abspath(__file__))

def generate():
    text = open(os.path.join(here, 'prelude.scm')).read()
    body = text.replace('\\', '\\\\').replace('"', '\\"')
    return (';;; prelude.fx: prelude.scm, as a string. Made by gen-prelude.py: edit\n'
            ';;; prelude.scm, then run it.\n\n'
            '(define s7-prelude string "' + body + '")\n')

out = generate()
path = os.path.join(here, 'prelude.fx')
if '--check' in sys.argv:
    sys.exit(0 if os.path.exists(path) and open(path).read() == out else 1)
open(path, 'w').write(out)
