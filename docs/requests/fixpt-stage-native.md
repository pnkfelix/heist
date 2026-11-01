# A request to the Fixpt team: staged code compiled as a program's is

Status: worked around in Heist's `fixpt/` (FIXPT-CHANGES.md F8), unsafely;
for Fixpt to do properly. Drafted 2026-10-31 by Heist, for the user to
take to the Fixpt team. Measured at Fixpt main 71de5b88 (Heist's
`fixpt/` subtree), x86_64 Linux, the default machine (`fast`,
`fx-regs-rsjit-nativecc`).

---

s7st, Heist's R7RS Scheme in FX-26, now compiles Scheme instead of
interpreting it. Each batch of top-level forms is lowered to an FX-26
datum and `stage`d against a module of s7st's runtime, then called
(`s7st/lower.fx`). A Scheme procedure becomes an FX-26 procedure, and a
Scheme call an FX-26 call through the runtime (`s7-call1` and its kin,
program code). For that to pay, staged code must run as fast as the
program's own code, and the two must call each other in tail position.
On Fixpt 71de5b88 neither held.

## What we found

1. **Staged code is cellular code on the native machines.** `stage`
   compiles the code to a word and runs it (`stage.rs`'s `made`). The
   procedures it makes are cellular closures. On `fx-regs-*` and
   `*-nativecc`, the program's own procedures are register code made
   native. A loop of 10⁷ steps, `(go (- n 1) (+ acc (modulo n 7)))`:

   | machine                   | as the program's code | staged  |
   | ------------------------- | --------------------: | ------: |
   | `fx-cells-rsjit-cellcc`   |                709 ms |  674 ms |
   | `fx-regs-rsjit-cellcc`    |                 55 ms |  664 ms |
   | `fx-regs-fxjit-nativecc`  |                 55 ms | 1445 ms |
   | `fx-regs-rsjit-nativecc`  |                 55 ms | 1423 ms |

2. **No tail call between staged code and the program's, on the native
   machines.** A staged loop that recurs through a procedure of the
   program, `(%apply1 go (- n 1))` with `apply1` being
   `(lambda (f n) (f n))`, overflows the stack on the three
   `*-nativecc` machines. It runs on every cellular-convention machine.
   Staged code calling staged code, and program code calling program
   code, are both fine. The crossing goes through the foreign
   convention (`common_foreign`), and the cellular machine runs nested
   under Rust's frames.

3. **The native compiler cannot compile while native code runs.**
   `with_machine` refuses ("native code called from code native code
   called"). A `stage` is always made while native code runs, since
   `main` is native, so even with (1) fixed in `stage.rs` the compile is
   declined. The same check makes `native_code_of` decline whenever the
   machine is busy (`adapt`).

4. **A sealed module cannot be staged against.** When a stage's module
   is a global whose type seals it, `(the (moduleof (abs t type) …)
   (module …))`, the FX-26 checker prints its abstract types as the
   global's, `m..t`. The staged checker then refuses: "`s7-rt..%value`
   is not a type".

5. **A stage costs in proportion to the types it is checked against.**
   Every type in M, E and R is printed whole and read again. With
   s7st's value type in them (some 20 KB of text printed), a stage of
   `(define x 1)` took 49 ms. Sealed (4), with the result type no longer
   naming s7st's types, it takes 8 ms. Of that, a quarter of a
   millisecond is the form's own code.

## What Heist did (F8), and what we ask

- **(1):** `stage.rs` compiles the maker natively through a new
  `Runtime::stage_native`, which the session sets to its native
  compiler. What the compiler declines stays cellular.
  *Ask:* staged code compiled exactly as the program's procedures are,
  on every machine, `fx-regs-fxjit-nativecc` included.
- **(2):** follows from (1): native to native, the calls are tail calls.
  *Ask:* a test that a staged loop through a program procedure runs in
  constant space on every machine.
- **(3):** `with_machine_compiling` borrows the running machine through
  a raw pointer, for `compile_closure` only, and the call-out table is
  made with room for 2¹⁶ entries so that it never moves under running
  code. This is unsafe aliasing: sound in practice only because the run
  uses its runner's copies until the call-out returns.
  *Ask:* a real design for compiling while code runs. For instance,
  split the compile-time state (call-out table, slot facts) from the
  run-time state behind their own cells.
- **(4):** `k-note-staged` binds a module's opened abstract types under
  their own names again (`k-rebind-opened`).
  *Ask:* review it; the Rust checker prints them right already.
- **(5):** worked around in s7st, by sealing and by staging up to a
  hundred forms at once.
  *Ask:* a stage of a module's type that does not print and re-check
  it each time (a module checked once, kept by the front end), so that
  `eval` in a loop is cheap.

## A smaller thing seen on the way

A closure is made in line only with at most six free values on x86_64
(the inline path's registers). With more, it is made by a call-out
(`Callout::ClosureAny`), at about a microsecond. s7st's lowered code put
each constant its code names in a variable of its own, and leak 7 of
R7RS's `lazy` test made 16 closures an element by call-out. s7st now
passes one table instead. A note in `docs/performance.md`, or a larger
inline limit, would save the next program the search.
