"""Heist's FX-26 files rewritten to use `loop`, `when` and `unless`
macros (docs/macros.md).

  rewrite.py [--write] FILE...             module files
  rewrite.py [--write] --program FILE...   one program's files

A module file defines the macros it uses itself; a program's files share
one top level, so the first of them defines them for all. A macro is used
only if its uses save more characters than its definition costs, and a
module file is changed only if it is shorter for it. Without `--write`,
says what it would do. Where the file (or the program) defines some of
these macros already, it uses them, and adds the others' definitions after
its last `define-syntax`; a file that defines only other macros is left as
it is.
"""
import sys, os, re
sys.path.insert(0, os.path.dirname(__file__))
from sx import Src, is_list, head, walk
from survey import loop_match

DEFS = {
    'when': "(define-syntax NAME (syntax-rules () ((_ c e ...) (if c (begin e ...) #u))))\n",
    'unless': "(define-syntax NAME (syntax-rules () ((_ c e ...) (if c #u (begin e ...)))))\n",
    'loop': ("(define-syntax NAME\n"
             "  (syntax-rules ()\n"
             "    ((_ go eff ((x t i) ...) r body) (letrec ((go (subr eff (t ...) r) (lambda (x ...) body))) (go i ...)))))\n"),
}
ORDER = ['loop', 'when', 'unless']
# Each macro's name, or, in a file that already names something so, the
# first of the others that it does not.
NAMES = {'loop': ['loop', 'iterate', 'repeat'], 'when': ['when', 'if-so'], 'unless': ['unless', 'if-not']}


def def_of(k, name):
    return DEFS[k].replace('NAME', name)


DEFS_HEAD = ";; Macros: each file defines its own, for now (docs/macros.md).\n"
PROGRAM_HEAD = ";; Macros, for all of this program's files (docs/macros.md).\n"


def is_u(x):
    return x[0] == 'atom' and x[3] == '#u'


def when_match(n):
    if head(n) != 'if' or len(n[3]) != 4:
        return None
    _, c, a, b = n[3]
    if is_u(b) and not is_u(a):
        return ('when', n, c, a[3][1:] if head(a) == 'begin' and len(a[3]) > 1 else [a], a)
    if is_u(a) and not is_u(b):
        return ('unless', n, c, b[3][1:] if head(b) == 'begin' and len(b[3]) > 1 else [b], b)
    return None


class Out:
    """Text being built at a known column, pieces of `src` reindented."""

    def __init__(self, src, col):
        self.src, self.parts, self.col = src, [], col

    def lit(self, s):
        self.parts.append(s)
        self._adv(s)

    def _adv(self, s):
        if '\n' in s:
            self.col = len(s) - s.rfind('\n') - 1
        else:
            self.col += len(s)

    def piece(self, a, b):
        """src[a:b], its lines after the first shifted as its start moves."""
        src = self.src
        delta = self.col - src.col(a)
        t = src.text
        out, i = [], a
        while True:
            j = t.find('\n', i, b)
            if j < 0:
                out.append(t[i:b])
                break
            out.append(t[i:j + 1])
            k = j + 1
            if any(s < k < e for s, e in src.strings):
                i = k
                continue
            sp = k
            while sp < b and t[sp] == ' ':
                sp += 1
            if sp < b and t[sp] != '\n':
                n = max(0, (sp - k) + delta)
                out.append(' ' * n)
            i = sp
        s = ''.join(out)
        self.parts.append(s)
        self._adv(s)

    def newline(self, col):
        self.lit('\n' + ' ' * col)

    def text(self):
        return ''.join(self.parts)


def one_line(src, n):
    return '\n' not in src.text[n[1]:n[2]]


def kept_comments_ok(src, n, kept):
    """Whether every comment in node `n` lies in one of the `kept` spans."""
    for cs, ce in src.comments:
        if n[1] <= cs < n[2] and not any(a <= cs < b for a, b in kept):
            return False
    return True


_top = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'fixpt/crates/fixpt-fx26/src/top.rs')).read()
_kw = _top[_top.index('pub const KEYWORDS'):]
KEYWORDS = set(re.findall(r'"([^"]+)"', _kw[:_kw.index('];')])) | {'define-syntax', 'define-syntax-rec'}


def bare_keyword(*parts):
    """Whether one of a use's parts is an FX-26 keyword alone: Fixpt
    eed406e0 refuses it as an expression (`fields` is a form's name) or a
    binder in a pattern's list, though it takes one as the loop's name,
    and inside a part's list (docs/requests/fixpt-macros-from-heist.md)."""
    return any(x[0] == 'atom' and x[3] in KEYWORDS for x in parts)


def name_only_called(body, name):
    """Whether `name` occurs in `body` only at the head of a call: not as
    a value or a label, which the expander will not let the macro bind."""
    def go(n, labels):
        if n[0] == 'atom':
            return n[3] != name
        if n[0] != 'list':
            return True
        kids = n[3]
        if kids and kids[0][0] == 'atom' and kids[0][3] == name and n[4] != 'q':
            if labels:
                return False
            kids = kids[1:]
        lab = head(n) in ('product', 'productof', 'sumof', 'tagcase', 'moduleof', 'module')
        return all(go(k, lab) for k in kids)
    return go(body, False)


def render_loop(src, n, m):
    kept = [(m['eff'][1], m['eff'][2]), (m['res'][1], m['res'][2]), (m['body'][1], m['body'][2])]
    kept += [(x[1], x[2]) for x in m['tys'] + m['args']]
    if not kept_comments_ok(src, n, kept):
        return None
    col = src.col(n[1])
    o = Out(src, col)
    o.lit('(' + NAME_OF['loop'] + ' ' + m['name'][3] + ' ')
    o.piece(m['eff'][1], m['eff'][2])
    o.lit(' (')
    for k, (x, t, a) in enumerate(zip(m['params'], m['tys'], m['args'])):
        if k:
            o.lit(' ')
        o.lit('(' + x[3] + ' ')
        o.piece(t[1], t[2])
        o.lit(' ')
        o.piece(a[1], a[2])
        o.lit(')')
    o.lit(') ')
    o.piece(m['res'][1], m['res'][2])
    if one_line(src, n):
        o.lit(' ')
    else:
        o.newline(col + 2)
    o.piece(m['body'][1], m['body'][2])
    o.lit(')')
    return o.text()


def render_when(src, w):
    kind, n, c, es, arm = w
    kept = [(c[1], c[2]), (es[0][1], es[-1][2])]
    if not kept_comments_ok(src, n, kept):
        return None
    col = src.col(n[1])
    o = Out(src, col)
    o.lit('(' + NAME_OF[kind] + ' ')
    o.piece(c[1], c[2])
    if one_line(src, n):
        o.lit(' ')
    else:
        o.newline(col + 2)
    o.piece(es[0][1], es[-1][2])
    o.lit(')')
    return o.text()


def matches(src, enabled):
    found = []
    for f in src.forms:
        if head(f) == 'define-syntax':
            continue  # a macro's own template
        for n in walk(f):
            if 'loop' in enabled:
                m = loop_match(src, n)
                if m and m['name'][3] not in NAME_OF.values() and name_only_called(m['body'], m['name'][3]) and not bare_keyword(*m['params'], *m['args'], m['body']):
                    found.append(('loop', n, m))
                    continue
            if 'when' in enabled or 'unless' in enabled:
                w = when_match(n)
                if w and w[0] in enabled and not bare_keyword(w[2], *w[3]):
                    found.append((w[0], n, w))
    return found


def one_pass(text, enabled):
    src = Src(text)
    found = matches(src, enabled)
    # Innermost first: a match none of whose descendants match.
    spans = [(n[1], n[2]) for _, n, _ in found]
    edits = []
    for kind, n, m in found:
        if any(n[1] <= a and b <= n[2] and (a, b) != (n[1], n[2]) for a, b in spans):
            continue
        new = render_loop(src, n, m) if kind == 'loop' else render_when(src, m)
        if new is not None:
            edits.append((n[1], n[2], new, kind))
    for a, b, new, _ in sorted(edits, reverse=True):
        text = text[:a] + new + text[b:]
    return text, edits


def rewrite(text, enabled):
    count = {k: 0 for k in enabled}
    while True:
        text2, edits = one_pass(text, enabled)
        for *_, k in edits:
            count[k] += 1
        if not edits:
            return text, count
        text = text2


def unquoted(n):
    """`n` and its parts, but not data quoted with `'`."""
    if n[0] == 'list' and n[4] == 'q' and n[3][0][3] == "'":
        return
    yield n
    if n[0] == 'list':
        for k in n[3]:
            yield from unquoted(k)


def uses_name(text, name):
    src = Src(text)
    return any(n[0] == 'atom' and n[3] == name for f in src.forms for n in unquoted(f))


NAME_OF = dict((k, k) for k in ORDER)
HAVE = {}  # the macros a file (or program) defines already


def choose_name(texts, k):
    for name in NAMES[k]:
        if not any(uses_name(t, name) for t in texts):
            NAME_OF[k] = name
            return name
    raise SystemExit(f'no name free for {k}')


def defined(texts):
    """The macros the files define already, each kind by its name."""
    return {k: name for k in ORDER for name in NAMES[k]
            if any(def_of(k, name) in t for t in texts)}


def after_defs(text, enabled):
    """`text` with the definitions of `enabled` added after its last
    `define-syntax`."""
    if not enabled:
        return text
    at = max(f[2] for f in Src(text).forms if head(f) == 'define-syntax') + 1
    return text[:at] + ''.join(def_of(k, NAME_OF[k]) for k in ORDER if k in enabled) + text[at:]


def defs_text(enabled, head_=DEFS_HEAD):
    return head_ + ''.join(def_of(k, NAME_OF[k]) for k in ORDER if k in enabled)


def insert_defs(text, enabled, head_=DEFS_HEAD):
    src = Src(text)
    first = src.forms[0]
    if head(first) == 'module-parameters':
        at = first[2]
        while at < len(text) and text[at] != '\n':
            at += 1
        return text[:at + 1] + '\n' + defs_text(enabled, head_) + text[at + 1:]
    # Before the first form, after the header comments; or, if the first
    # form is a docstring, before it.
    at = first[1]
    return text[:at] + defs_text(enabled, head_) + '\n' + text[at:]


def plan(text, candidates=ORDER):
    """The macros worth defining in `text`, each by its net saving."""
    chosen, report = [], {}
    for k in candidates:
        if k in HAVE:
            continue
        name = choose_name([text], k)
        new, count = rewrite(text, [k])
        net = len(text) - len(new) - len(def_of(k, name))
        report[k] = (count[k], net) if name == k else (name, count[k], net)
        if net > 0:
            chosen.append(k)
    return chosen, report


def main_program(files, write):
    """Files sharing one top level: each macro planned over all, defined
    once, in the first."""
    texts = [open(f).read() for f in files]
    HAVE.clear()
    HAVE.update(defined(texts))
    NAME_OF.update(HAVE)
    chosen, report = [], {}
    for k in ORDER:
        if k in HAVE:
            continue
        name = choose_name(texts, k)
        saved = n = 0
        for t in texts:
            new, count = rewrite(t, [k])
            saved += len(t) - len(new)
            n += count[k]
        report[k] = (n, saved - len(def_of(k, name))) if name == k else (name, n, saved - len(def_of(k, name)))
        if saved > len(def_of(k, name)):
            chosen.append(k)
    total = 0
    for i, (f, t) in enumerate(zip(files, texts)):
        new, _ = rewrite(t, chosen + list(HAVE))
        if i == 0 and chosen:
            new = after_defs(new, chosen) if HAVE else insert_defs(new, chosen, PROGRAM_HEAD)
        Src(new)
        total += len(t) - len(new)
        print(f'{f:28} {len(t):7} -> {len(new):7} ({len(new) - len(t):+6})')
        if write:
            open(f, 'w').write(new)
    print('program:', report, 'saved', total)


def main(argv):
    write = '--write' in argv
    if '--program' in argv:
        return main_program([a for a in argv if not a.startswith('--')], write)
    files = [a for a in argv if not a.startswith('--')]
    total = 0
    for f in files:
        text = open(f).read()
        HAVE.clear()
        HAVE.update(defined([text]))
        if '(define-syntax ' in text and not HAVE:
            print(f'{f:28} {len(text):7} unchanged: it defines other macros')
            continue
        NAME_OF.update(HAVE)
        chosen, report = plan(text)
        if not chosen and not HAVE:
            print(f'{f:28} {len(text):7} unchanged {report}')
            continue
        new, count = rewrite(text, chosen + list(HAVE))
        if chosen:
            new = after_defs(new, chosen) if HAVE else insert_defs(new, chosen)
        Src(new)  # still reads
        if len(new) >= len(text) and not (HAVE and len(new) == len(text)):
            print(f'{f:28} {len(text):7} unchanged, the definitions cost more {report}')
            continue
        total += len(text) - len(new)
        print(f'{f:28} {len(text):7} -> {len(new):7} ({len(new) - len(text):+6}) {report}')
        if write:
            open(f, 'w').write(new)
    print('saved', total)


if __name__ == '__main__':
    main(sys.argv[1:])
