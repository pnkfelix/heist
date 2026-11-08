# casing: Alloy's semantics in FX-26

casing is a relational model finder written in FX-26, after Alloy 6. It
keeps Alloy's semantic model and not its syntax:
- everything is a relation over atoms;
- a model is checked within a bounded scope;
- relations that change make a trace, an infinite lasso of states.

A model is a file of S-expressions, and casing's solver is combo's SAT
solver (`combo/sat.fx`). Started 2026-11-07, from Alloy at
AlloyTools/org.alloytools.alloy ed89fdb (cloned to
`~/Dev/LangPlay/alloy`; its analyzer is Pardinus, which is Kodkod with
temporal logic).

    bin/casing MODEL.cs      every command of the model, in order

## Files

| file | what | after |
| --- | --- | --- |
| `casing/circuit.fx` | Boolean circuits: hash-consed n-ary AND gates over signed ids, Tseitin-encoded into combo's solver lazily, only what an assertion reaches | Kodkod's `engine.bool` (`CBCFactory`, `Bool2CNFTranslator`) |
| `casing/matrix.fx` | A relation as a dense matrix of circuits, one cell per tuple (tuple index = its atoms in base n). Union, intersection, difference, product, join (an (∨, ∧) matrix product), transpose, closure by squaring, override, restriction, `iden`/`univ`/`none`; subset, equality, `some`/`no`/`one`/`lone`; counts in unary | `BooleanMatrix`, which is sparse |
| `casing/model.fx` | A model's forms read; a scope made into bounds; formulas translated at each position of a trace; instances shown | Alloy's `translator/` (A4) and Pardinus's `ltl2fol` |
| `casing/casing.fx` | The command line, reading with Fixpt's own reader (`fx26:eager-reader.fx`) | |
| `casing/tests/` | Models (`.cs`) and their answers; `run.sh` (`cargo nextest run` runs each as `casing::FILE`) | |

## The language

```scheme
(sig Node (edges (set Node)))                       ; sig Node { edges: set Node }
(sig Animal abstract (owner (lone Person)))
(sig Dog (extends Animal))  (sig Rex one (extends Dog))
(sig Light (var on (lone Light)))                   ; a field that changes
(sig Lamp (var @lamp on (lone Lamp)))               ; …in region @lamp
(sig Guest var @door)                               ; a sig that changes, in @door
(sig Tmp (in Node))                                 ; a subset sig
(fact (all ((n Node)) (not (in n (join n (^ edges))))))
(pred (two-cats (p Person)) (= (size (inter (join p owns) Cat)) 2))
(fun (kids (p Person)) (join p owns))
(assert acyclic (no (inter (^ edges) iden)))
(run two-cats 3)                                    ; default scope 3
(check acyclic 5 (Node 4) (exactly Dog 2) (steps 1 8))
```

- **Sig options:**
  - `abstract`, `one`, `lone`, `some`, `var` (or `var @r`, in region `r`);
  - `(extends P)`, `(in P)`;
  - fields, written `(f T)`, or `(var f T)` for one that changes, or
    `(var @r f T)` for one that changes in region `r`.
- **A field's type** is one of:
  - `T`, meaning `one T`, as in Alloy;
  - `(one T)`, `(lone T)`, `(some T)` or `(set T)`;
  - `(-> T U …)`, of higher arity, or `(m (-> T U …))`.

  The multiplicity applies to the last column: for each owner atom `x`,
  `(m (join x f))` holds.
- **Expressions:**
  - a name (a relation, a variable, `univ`, `iden`, `none`, or a function of
    no parameters);
  - joins and products: `(join a b …)`, `(-> a b …)`;
  - set operations: `(union …)`, `(inter …)`, `(diff a b)`, `(++ a b)`,
    `(<: s r)`, `(:> r s)`;
  - binary-relation operators: `(~ r)`, `(^ r)`, `(* r)`;
  - `(if f a b)`, `(let ((x e) …) e)`;
  - comprehension: `(set ((x y T)) f)`;
  - the next state's value: `(prime e)`, also written `'e`;
  - a function call: `(f e …)`.
- **Formulas:**
  - comparisons: `(in a b)`, `(= a b)`, `(!= a b)`;
  - multiplicities: `(some e)`, `(no e)`, `(one e)`, `(lone e)`;
  - quantifiers: `(all ((x y T) (z U)) f)`, and `some`, `no`, `one` and
    `lone` with declarations. A declaration may name those before it.
  - connectives: `not`, `and`, `or`, `implies` (or `=>`), `iff`,
    `(if f g h)`, `let`, `true`, `false`;
  - predicate calls.
- **Integers:**
  - expressions: `(size e)` (Alloy's `#`, which FX-26's reader reserves),
    numerals, `(+ i j)`, `(- i j)`;
  - comparisons: `=`, `<`, `<=`, `>`, `>=`.
- **Time:**
  - future: `after`, `always`, `eventually`, `until`, `releases`;
  - past: `before`, `historically`, `once`, `since`, `triggered`;
  - `(then f g)`, which is Alloy's `f ; g`.
- **Events:** an event is a predicate that says which changing relations,
  and which regions, it may write. The FX-flavoured part is below.
  - `(unchanged r …)`: the named relations are the same in the next state;
    a region `@r` names every relation that changes in it.
  - `(stutter)`: nothing that changes, changes.

## Semantics: as Alloy 6, and where not

**As Alloy.**
- **Bounds.**
  - Each top-level sig gets its own atoms, named `Sig$i`.
  - A `one` part of a sig gets one of its parent's atoms, named after it.
  - Other parts may hold any of the parent's atoms that are left.
  - A subset sig may hold any of its parent's.
- **Constraints the bounds don't give** become facts:
  - each sig is within its parent;
  - parts are pairwise disjoint;
  - an abstract sig is the union of its parts;
  - sig multiplicities, and a scope smaller than the atoms a sig may hold;
  - each field is within its columns, with its multiplicity.
- **Formulas.**
  - Quantifiers are grounded over a declaration's tuples, as Kodkod does.
  - A predicate's arguments, and a `let`'s, are passed by name. So a
    parameter used under `prime`, or in another state, is its expression
    there.
- **Time.**
  - Traces are lassos: k states, with one loop input per state the last
    one may go back to, and exactly one of them true.
  - Steps run from the scope's least to its greatest, stopping at the
    first instance. As in Alloy, a fact holds in the first state only
    unless it says `always`. The declarations' facts hold in every state.
  - **Past operators need the loop unrolled to be exact.** A formula is
    evaluated at positions `p = j·k + s`: state `s` in copy `j`. Copy 0 is
    the trace from its start; each later copy is the loop again. A past
    formula nested `d` deep needs `d+1` copies (`model-past-depth`), as
    Pardinus unrolls (Latvala et al., "Simple is better", 2005).
  - Each temporal operator walks the positions in their order for each loop
    the trace may have (`future-seq`, `past-seq`), under that loop's input.
    `tests/past-loop.cs` checks this on formulas that need it.
- **A run with parameters.** Each parameter is a fresh relation, `one` of
  its type, and is shown as `$name`, as Alloy skolemizes.

**Not as Alloy.**
- **Integers are naturals, in unary.** A count is a list of circuits, the
  j-th saying "at least j+1". Sums and differences are exact, and a
  difference stops at 0. Nothing wraps and nothing overflows. Alloy's
  integers are two's complement of a bitwidth, and wrap; its `noOverflow`
  option makes formulas depend on context. casing has no `Int` atoms, no
  `sum` and no negative numbers. Those would need their own design.
- **A relation's matrix is dense:** n^arity cells. That is fine at the
  scopes casing runs today, and too costly for arity 3 or more at large n.
- **`univ` is every atom.** Alloy's `univ` also holds its Int atoms, which
  casing has none of.

## FX's flavour: events say what they write

Alloy 6 makes the modeller write each event's frame conditions by hand:
everything the event does not change stays as it was. casing's `event`
says which changing relations it may write, as an FX procedure's effect
says which regions it may write. The rest are unchanged, by construction:

```scheme
(event (toggle (l Light)) (writes on)
  (if (some (join l on)) (no (join l (prime on))) (= (join l (prime on)) l)))
(fact (always (or (stutter) (some ((l Light)) (or (toggle l) (press l))))))
```

`toggle` leaves `pressed` as it is without saying so (`tests/light.cs`).

**Regions.** As an FX procedure's effect names regions rather than each
location it writes, a relation that changes may say the region it
changes in, and an event may write the region:

```scheme
(sig Lamp (var @lamp on (lone Lamp)) (var @lamp level (set Lamp)))
(sig Door (var @door open (lone Door)))
(sig Guest var @door)
(event (switch (l Lamp)) (writes @lamp) …)          ; on and level
(event (prop (l Lamp) (d Door)) (writes @lamp open) …)  ; both kinds at once
(assert enter-alone (always (implies (enter) (unchanged @lamp))))
```

Regions are declared by use: a region is the relations that name it.
A relation is in at most one region, and need not be in any. Naming
relations in `writes` still works, as above. casing refuses a `writes`
that names a relation that does not change, or a region nothing changes
in (`tests/regions.cs`).

An FX-style effect discipline goes further than this:
- events whose writes are disjoint commute, which partial-order reduction
  could use;
- a predicate typed `pure` cannot mention `prime`;
- a check could say which relations a property reads.

## Not yet

- **Symmetry breaking.** Kodkod's lex-leader predicates over
  interchangeable atoms. Without them, an unsatisfiable check explores
  every permutation of each instance.
- **Memoizing translations.** A subformula is translated again for each
  loop and position that reaches it. The circuits are hash-consed, so the
  formula is the same, but the time grows with temporal nesting.
- **More instances**, by blocking each one found: Alloy's "next".
- **Alloy's type system.** casing checks arity only, not that a join
  relates the sigs it should, and it gives no relevance warnings.
- **The rest:** decls of `set`, `some` or `lone` multiplicity, `disj`,
  `seq`, `util/ordering`, strings, modules.
- **Cross-checking against Alloy itself.** Run the same models in Alloy 6
  and compare the answers. This needs a JDK newer than this machine's 11.
