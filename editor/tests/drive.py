#!/usr/bin/env python3
"""Drive the editor in a pseudo-terminal, and show the screen it leaves.

    drive.py [--rows N] [--cols N] [--file FILE] KEYS...

Each KEYS argument is typed, then a pause: `\\x18\\x13` style escapes are
understood, an argument `@500` pauses 500 ms instead, `@until TEXT` waits
(10 s at most) until the screen shows TEXT, and an argument `=`
prints the screen as it is then, before the last. The editor's
output is interpreted as the few VT100 sequences it writes (cursor
position, clear, SGR, cursor shown or hidden, the alternate screen), and
the screen as it was just before the editor left the alternate screen is
printed, with the cursor's place: rows as text, `|` at their right edge.

The editor is run with `--report-idle` (main.fx): it says when it has
settled, and how many bytes it has read, so that after each key this
waits for that rather than for a quiet that may come too soon or late --
unless a pause comes next, which is waited instead.
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
edit = os.environ.get("HEIST_EDIT") or os.path.join(here, "..", "..", "bin", "heist-edit")
argv = [edit, "--report-idle"] + ([a.file] if a.file else [])

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
            pump.last = time.time()

pump.last = time.time()

IDLE = re.compile(rb"\x1b\]7777;idle;([0-9]+)\x07")
sent = 0
def settled(limit=10.0):
    """Pump until the editor has settled having read all that was sent --
    the last it wrote, a marker saying so: once it does more, it says so
    again when it is done -- or `limit` has passed."""
    end = time.time() + limit
    while time.time() < end:
        ms = list(IDLE.finditer(out, max(0, len(out) - 64)))
        if ms and ms[-1].end() == len(out) and int(ms[-1].group(1)) >= sent:
            return
        pump(min(0.05, max(0.0, end - time.time())))
    ms = list(IDLE.finditer(out))
    sys.stderr.write(f"drive.py: not settled within {limit:g} s, {sent} bytes sent"
                     + (f"; last said idle at {ms[-1].group(1).decode()} bytes read, {len(out) - ms[-1].end()} bytes after it"
                        if ms else "; never said idle")
                     + f"; {time.time() - pump.last:.1f} s since output\n")

# A minimal terminal.
FACE = {"0": " ", "0;1;35": "k", "0;1;34": "f", "0;36": "t", "0;32": "s", "0;2": "c",
        "0;1;31": "e", "0;30;45": "i", "0;7": "m", "0;2;7": "M", "0;1;36": "p", "0;4": "u", "0;1;4": "B", "0;1;7": "P"}

def render(data):
    """The screen `data` leaves, as rows, the cursor, and the faces: as it
    was just before the alternate screen was left, if it was."""
    rows, cols = a.rows, a.cols
    grid = [[" "] * cols for _ in range(rows)]
    fgrid = [[" "] * cols for _ in range(rows)]
    sgr = "0"
    cur = [0, 0]
    last = None
    text = IDLE.sub(b"", bytes(data)).decode("utf-8", "replace")
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
    return last if last is not None else (grid, cur, fgrid)

def show(screen):
    g, c, fg = screen
    for r in g:
        print("".join(r).rstrip().ljust(a.cols) + "|")
    print(f"cursor {c[0]},{c[1]}")
    if a.faces:
        for r in fg:
            print("".join(r).rstrip().ljust(a.cols) + "|")

# Started: settled once, the parties outside (syntax, index) having had a go.
settled(a.settle + 10)
snapshots = []
for i, k in enumerate(a.keys):
    if k == "=":
        settled()
        snapshots.append(len(out))
        continue
    if k.startswith("@until "):
        want = k[len("@until "):]
        shown = lambda: any(want in "".join(r) for r in render(out)[0])
        end = time.time() + 10
        while time.time() < end and not shown():
            pump(0.05)
        if not shown():
            sys.stderr.write(f"drive.py: the screen did not show {want!r} within 10 s\n")
        settled()
        continue
    if k.startswith("@"):
        pump(int(k[1:]) / 1000)
        continue
    b = k.encode("utf-8").decode("unicode_escape").encode("latin-1")
    os.write(fd, b)
    sent += len(b)
    # A pause next says how long to wait: for what may not settle (a
    # loop to interrupt), or a process's output.
    if not re.match(r"@[0-9]+$", a.keys[i + 1] if i + 1 < len(a.keys) else ""):
        settled()
settled()
try:
    os.kill(pid, 9)
except ProcessLookupError:
    pass

for n, at in enumerate(snapshots):
    print(f"== screen {n + 1}")
    show(render(bytes(out[:at])))
if snapshots:
    print("== at the end")
show(render(bytes(out)))
