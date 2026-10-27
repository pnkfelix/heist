# A request to the Fixpt team: `rnew` and `rmake-array` inline in the direct native code

Status: done by Fixpt in b7b60d98 (2026-10-27), pulled by Heist's
82b06f73. After it, on the benchmark below, `make-array` 487 → 58 ms and
`new` 304 → 37 ms. Drafted 2026-10-27 by Heist, for the user to take to
the Fixpt team. Measured at Fixpt main 8793b0cb (Heist's `fixpt/` subtree), x86_64
Linux, the default machine (`fast`).

---

s7st, Heist's R7RS interpreter written in FX-26, keeps all of its mutable
data in one long-lived region, `@sc`. Every Scheme pair has two cells
(`car`, `cdr`) made by `new`, and every procedure call makes a frame of
slots with `make-array`. In the default machine's native code, both of
these are call-outs to Rust (`%region-new`, `%region-make-array`). That
makes them 20–30 times as costly as allocating an immutable sum or
product, which is done inline.

## The numbers

`docs/requests/bench/region-alloc.fx`, run with `fixpt run`, does 10
million iterations of each operation (times in ms, so ns/op ≈ ms / 10):

| per iteration                             | ms  |
| ----------------------------------------- | --: |
| a literal sum, matched                    |  20 |
| a fresh sum `(sum a i)`, matched          |  35 |
| a global read                             |  16 |
| `array-ref` of an array at `@sc`          |  30 |
| `array-length` of an array at `@sc`       |  23 |
| **`(make-array 3 …)` at `@sc`**           | **487** |
| **`(new …)` at `@sc`**                    | **304** |

With `FIXPT_PERF_MAP=1 perf record`, s7st running a named-`let` loop
spends about 12% of its time in `fixpt_native::direct::callout` and the
`%region-make-array` primitive under it (`Heap::make_bloblet`). That is
after the interpreter's own allocation of wrappers has been removed.
Programs that build lists spend more, since each `cons` is two `rnew`s.

## Why it matters

R7RS's conformance tests (Larceny's `(scheme time)`) count down a
million in a loop between clock readings, and allow 0.1 s of slack. So
they need 10 million loop iterations a second. s7st does 8 million; each
iteration makes one frame. The frame's `make-array` alone is ~47 ns of
the ~125 ns each iteration takes.

## What we ask

In `crates/fixpt-native/src/direct/x64.rs`, do `%region-new` and
`%region-make-array` (and, for arm64, the same in its direct back end) as
`%region-cons` is done there already. That is: bump the region's current
chunk through `region_table`, and call out only when the chunk is full or
the region has no slot. `docs/performance.md` ("The call-outs left hot,
inline") says register code already does `rnew` this way; the direct
convention, the default, does not.

`%region-make-array` has a length known only at run time. An inline path
for small lengths, with the fill stored by a short loop and a call-out
above some size, would cover s7st's frames (nearly all under 8 slots).

No syscall is needed: this is a code-generation change only.

## What we have done meanwhile

s7st no longer wraps quick values in sums, and calls the commonest
built-ins with no argument list (`s7st/machine.fx`, `s7st/prims.fx`). That
was a 35–45% gain on calls and loops. What's left of its allocation is
mostly the region allocations above, which it cannot avoid: mutable
arrays and cells exist only in regions.
