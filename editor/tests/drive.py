#!/usr/bin/env python3
"""Drive the editor in a pseudo-terminal, and show the screen it leaves.

    drive.py [--rows N] [--cols N] [--file FILE] KEYS...

Each KEYS argument is typed, then a pause: `\\x18\\x13` style escapes are
understood, and an argument `@500` pauses 500 ms instead. The editor's
output is interpreted as the few VT100 sequences it writes (cursor
position, clear, SGR, cursor shown or hidden, the alternate screen), and
the screen as it was just before the editor left the alternate screen is
printed, with the cursor's place: rows as text, `|` at their right edge.
"""
import os, pty, sys, time, select, re, argparse

ap = argparse.ArgumentParser()
ap.add_argument("--rows", type=int, default=12)
ap.add_argument("--cols", type=int, default=50)
ap.add_argument("--file", default=None)
ap.add_argument("--settle", type=float, default=2.0, help="seconds to wait for startup")
ap.add_argument("--faces", action="store_true", help="also print each cell's face, as a letter")
ap.add_argument("keys", nargs="*")
a = ap.parse_args()

here = os.path.dirname(os.path.abspath(__file__))
edit = os.path.join(here, "..", "..", "bin", "heist-edit")
argv = [edit] + ([a.file] if a.file else [])

pid, fd = pty.fork()
if pid == 0:
    os.environ["TERM"] = "xterm"
    os.execv(edit, argv)

import fcntl, termios, struct
fcntl.ioctl(fd, termios.TIOCSWINSZ, struct.pack("HHHH", a.rows, a.cols, 0, 0))

out = bytearray()
def pump(seconds):
    end = time.time() + seconds
    while True:
        left = end - time.time()
        if left <= 0:
            return
        r, _, _ = select.select([fd], [], [], left)
        if r:
            try:
                data = os.read(fd, 65536)
            except OSError:
                return
            if not data:
                return
            out.extend(data)

def quiet(seconds, limit=10.0):
    """Pump until no output has come for `seconds`, or `limit` has passed."""
    end = time.time() + limit
    while time.time() < end:
        before = len(out)
        pump(seconds)
        if len(out) == before:
            return

# Started: the first screen drawn (the cursor shown after drawing), and
# then quiet, so that the parties outside (syntax, index) have had a go.
end = time.time() + a.settle + 10
while b"\x1b[?25h" not in out and time.time() < end:
    pump(0.1)
quiet(0.3)
for k in a.keys:
    if k.startswith("@"):
        pump(int(k[1:]) / 1000)
        continue
    os.write(fd, k.encode("utf-8").decode("unicode_escape").encode("latin-1"))
    quiet(0.25)
quiet(0.5)
try:
    os.kill(pid, 9)
except ProcessLookupError:
    pass

# A minimal terminal.
rows, cols = a.rows, a.cols
grid = [[" "] * cols for _ in range(rows)]
fgrid = [[" "] * cols for _ in range(rows)]
# The faces' SGR parameters (screen.fx's face-sgr), as letters.
FACE = {"0": " ", "0;1;35": "k", "0;1;34": "f", "0;36": "t", "0;32": "s", "0;2": "c",
        "0;1;31": "e", "0;30;45": "i", "0;7": "m", "0;2;7": "M", "0;1;36": "p"}
sgr = "0"
cur = [0, 0]
last = None
text = out.decode("utf-8", "replace")
i = 0
while i < len(text):
    c = text[i]
    if c == "\x1b":
        m = re.match(r"\x1b\[(\??)([0-9;]*)([A-Za-z])", text[i:])
        if m:
            priv, params, fin = m.groups()
            ps = [int(p) for p in params.split(";") if p]
            if fin == "H":
                cur = [(ps[0] - 1) if ps else 0, (ps[1] - 1) if len(ps) > 1 else 0]
            elif fin == "J" and ps == [2]:
                grid = [[" "] * cols for _ in range(rows)]
                fgrid = [[" "] * cols for _ in range(rows)]
            elif fin == "m" and not priv:
                sgr = params or "0"
            elif priv == "?" and ps == [1049] and fin == "l":
                last = ([r[:] for r in grid], cur[:], [r[:] for r in fgrid])
            i += m.end()
            continue
        i += 1
        continue
    if c in "\r\n":
        i += 1
        continue
    if 0 <= cur[0] < rows and 0 <= cur[1] < cols:
        grid[cur[0]][cur[1]] = c
        fgrid[cur[0]][cur[1]] = FACE.get(sgr, "?")
    cur[1] += 1
    i += 1
if last is None:
    last = (grid, cur, fgrid)
g, c, fg = last
for r in g:
    print("".join(r).rstrip().ljust(cols) + "|")
print(f"cursor {c[0]},{c[1]}")
if a.faces:
    for r in fg:
        print("".join(r).rstrip().ljust(cols) + "|")
