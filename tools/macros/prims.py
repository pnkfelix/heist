"""`(s7-prim! N MIN MAX (lambda ((a s7-values)) BODY))` as
`(def-prim N MIN MAX (a) BODY)`, in s7st's and the CFA's files (one
program), the macro defined in the first, after the other macros.

  prims.py [--write] FIRST-FILE FILE...
"""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from sx import Src, is_list, head, walk
from rewrite import Out, kept_comments_ok, one_line, uses_name, keyword_as_name

NAME = 'def-prim'
DEF = ("(define-syntax def-prim\n"
       "  (syntax-rules () ((_ n lo hi (a) body) (s7-prim! n lo hi (lambda ((a s7-values)) body)))))\n")


def match(n):
    if head(n) != 's7-prim!' or len(n[3]) != 5:
        return None
    lam = n[3][4]
    if head(lam) != 'lambda' or len(lam[3]) != 3 or not is_list(lam[3][1]) or len(lam[3][1][3]) != 1:
        return None
    p = lam[3][1][3][0]
    if not is_list(p) or len(p[3]) != 2 or p[3][1][0] != 'atom' or p[3][1][3] != 's7-values' or p[3][0][0] != 'atom':
        return None
    if keyword_as_name(n):
        return None
    return dict(first=n[3][1], last=n[3][3], param=p[3][0][3], body=lam[3][2], lam=lam)


def render(src, n, m):
    if not kept_comments_ok(src, n, [(m['first'][1], m['last'][2]), (m['body'][1], m['body'][2])]):
        return None
    col = src.col(n[1])
    o = Out(src, col)
    o.lit('(' + NAME + ' ')
    o.piece(m['first'][1], m['last'][2])
    o.lit(' (' + m['param'] + ')')
    same = '\n' not in src.text[m['lam'][1]:m['body'][1]]
    if same:
        o.lit(' ')
    else:
        o.newline(col + 2)
    o.piece(m['body'][1], m['body'][2])
    o.lit(')')
    return o.text()


def rewrite(text):
    count = 0
    while True:
        src = Src(text)
        edits = []
        for f in src.forms:
            for n in walk(f):
                m = match(n)
                if m:
                    new = render(src, n, m)
                    if new is not None:
                        edits.append((n[1], n[2], new))
        # Registrations do not nest; apply all.
        for a, b, new in sorted(edits, reverse=True):
            text = text[:a] + new + text[b:]
        count += len(edits)
        if not edits:
            return text, count


def main(argv):
    write = '--write' in argv
    files = [a for a in argv if not a.startswith('--')]
    texts = [open(f).read() for f in files]
    if any(uses_name(t, NAME) for t in texts):
        raise SystemExit(f'`{NAME}` is taken')
    news, total, n = [], 0, 0
    for t in texts:
        new, c = rewrite(t)
        news.append(new)
        n += c
    first = Src(news[0])
    # After the other macros' definitions, if any; else before the first form.
    at = news[0].find('(define-syntax ')
    if at >= 0:
        # Past the last `define-syntax`, and its newline.
        for f in first.forms:
            if head(f) == 'define-syntax':
                at = f[2] + 1
        news[0] = news[0][:at] + DEF + news[0][at:]
    else:
        at = first.forms[0][1]
        news[0] = news[0][:at] + DEF + '\n' + news[0][at:]
    for f, t, new in zip(files, texts, news):
        Src(new)
        total += len(t) - len(new)
        print(f'{f:24} {len(t):7} -> {len(new):7} ({len(new) - len(t):+6})')
        if write:
            open(f, 'w').write(new)
    print(f'{n} registrations, saved {total}')


if __name__ == '__main__':
    main(sys.argv[1:])
