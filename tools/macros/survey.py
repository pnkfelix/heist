"""Count macro candidates in Heist's FX-26 files, with rough savings."""
import sys, os, glob, collections
sys.path.insert(0, os.path.dirname(__file__))
from sx import Src, is_list, head, walk

H = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))


def loop_match(src, n):
    """(letrec ((N (subr E (T…) R) (lambda (x…) B))) (N a…)) -> parts."""
    if head(n) != 'letrec' or len(n[3]) != 3:
        return None
    _, binds, call = n[3]
    if not is_list(binds) or len(binds[3]) != 1:
        return None
    b = binds[3][0]
    if not is_list(b) or len(b[3]) != 3 or b[3][0][0] != 'atom':
        return None
    name, ty, lam = b[3]
    if head(ty) != 'subr' or len(ty[3]) != 4 or not is_list(ty[3][2]):
        return None
    if head(lam) != 'lambda' or len(lam[3]) != 3 or not is_list(lam[3][1]):
        return None
    params = lam[3][1][3]
    if not all(p[0] == 'atom' for p in params):
        return None
    if not is_list(call) or head(call) != name[3] or len(call[3]) - 1 != len(params):
        return None
    if len(ty[3][2][3]) != len(params):
        return None
    return dict(name=name, eff=ty[3][1], tys=ty[3][2][3], res=ty[3][3], params=params, body=lam[3][2], args=call[3][1:])


def when_match(src, n):
    """(if C (begin E…) #u) -> when; (if C #u (begin E…)) -> unless."""
    if head(n) != 'if' or len(n[3]) != 4:
        return None
    _, c, a, b = n[3]
    u = lambda x: x[0] == 'atom' and x[3] == '#u'
    if u(b) and head(a) == 'begin':
        return ('when', c, a[3][1:])
    if u(a) and head(b) == 'begin':
        return ('unless', c, b[3][1:])
    if u(b):
        return ('when1', c, [a])
    if u(a):
        return ('unless1', c, [b])
    return None


def files():
    out = []
    for f in sorted(glob.glob(H + '/**/*.fx', recursive=True)):
        r = os.path.relpath(f, H)
        if r.startswith(('fixpt/', 'target/', 'docs/')) or '/tests/' in r:
            continue
        out.append(r)
    return out


if __name__ == '__main__':
    tot = collections.Counter()
    for r in files():
        text = open(os.path.join(H, r)).read()
        try:
            s = Src(text)
        except Exception as e:
            print('UNREAD', r, e)
            continue
        c = collections.Counter()
        for f in s.forms:
            for n in walk(f):
                if loop_match(s, n):
                    c['loop'] += 1
                w = when_match(s, n)
                if w:
                    c[w[0]] += 1
                if head(n) == 'letrec':
                    c['letrec'] += 1
        tot.update(c)
        print(f'{r:28} {len(text):7} ' + ' '.join(f'{k}={v}' for k, v in sorted(c.items())))
    print('TOTAL', dict(tot))
