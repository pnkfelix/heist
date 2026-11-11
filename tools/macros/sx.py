"""A reader of FX-26 source that keeps each form's span, for rewriting.

Node: ('list', start, end, children, open_char) or ('atom', start, end, text)
or ('str', start, end). Comments are kept as spans in `comments`, strings'
spans in `strings`, so that a rewrite can tell whether a gap holds one.
"""
import re

DELIMS = set('()[] \t\n\r";')


class Src:
    def __init__(self, text):
        self.text = text
        self.comments = []   # (start, end)
        self.strings = []    # (start, end)
        self.i = 0
        self.forms = []
        while True:
            self.skip()
            if self.i >= len(text):
                break
            self.forms.append(self.read())

    def skip(self):
        t = self.text
        while self.i < len(t):
            c = t[self.i]
            if c in ' \t\n\r\f':
                self.i += 1
            elif c == ';':
                j = t.find('\n', self.i)
                j = len(t) if j < 0 else j
                self.comments.append((self.i, j))
                self.i = j
            elif t.startswith('#|', self.i):
                depth, j = 0, self.i
                while j < len(t):
                    if t.startswith('#|', j):
                        depth += 1; j += 2
                    elif t.startswith('|#', j):
                        depth -= 1; j += 2
                        if depth == 0:
                            break
                    else:
                        j += 1
                self.comments.append((self.i, j))
                self.i = j
            elif t.startswith('#;', self.i):
                s = self.i
                self.i += 2
                self.skip()
                self.read()
                self.comments.append((s, self.i))
            else:
                return

    def read(self):
        t = self.text
        s = self.i
        c = t[s]
        if c in '([':
            close = ')' if c == '(' else ']'
            self.i += 1
            kids = []
            while True:
                self.skip()
                if self.i >= len(t):
                    raise SyntaxError(f'unclosed list at {s}')
                if t[self.i] == close:
                    self.i += 1
                    return ('list', s, self.i, kids, c)
                kids.append(self.read())
        if c == '"':
            j = s + 1
            while t[j] != '"':
                j += 2 if t[j] == '\\' else 1
            self.i = j + 1
            self.strings.append((s, self.i))
            return ('str', s, self.i)
        if c in "'`":
            self.i += 1
            inner = self.read()
            return ('list', s, self.i, [('atom', s, s + 1, c), inner], 'q')
        if c == ',':
            n = 2 if t.startswith(',@', s) else 1
            self.i += n
            inner = self.read()
            return ('list', s, self.i, [('atom', s, s + n, t[s:s + n]), inner], 'q')
        if t.startswith('#\\', s):
            j = s + 3
            while j < len(t) and t[j] not in DELIMS:
                j += 1
            self.i = j
            return ('atom', s, j, t[s:j])
        if t.startswith('#(', s) or t.startswith('#u8(', s):
            self.i = t.index('(', s)
            v = self.read()
            return ('list', s, self.i, v[3], '#')
        if c == '|':
            j = t.index('|', s + 1)
            self.i = j + 1
            return ('atom', s, self.i, t[s:self.i])
        j = s
        while j < len(t) and t[j] not in DELIMS:
            j += 1
        if j == s:
            raise SyntaxError(f'unexpected {c!r} at {s}')
        self.i = j
        return ('atom', s, j, t[s:j])

    def has_comment(self, a, b):
        return any(a <= cs < b for cs, _ in self.comments)

    def col(self, pos):
        return pos - (self.text.rfind('\n', 0, pos) + 1)


def is_list(n):
    return n[0] == 'list' and n[4] in '(['


def head(n):
    return n[3][0][3] if is_list(n) and n[3] and n[3][0][0] == 'atom' else None


def walk(n):
    yield n
    if n[0] == 'list':
        for k in n[3]:
            yield from walk(k)


def sym(n):
    return n[0] == 'atom' and not n[3][0].isdigit() and n[3][0] not in '#"-+' or (n[0] == 'atom' and re.fullmatch(r'[-+][^0-9].*|[-+]', n[3]) is not None)
