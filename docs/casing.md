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
| `casing/matrix.fx` | A relation as a dense matrix of circuits, one cell per tuple (tuple index = its atoms in base n). Union, intersection, difference, product, join (an (∨, ∧) matrix product), transpose, closure by squaring, override, restriction, `iden`/`univ`/`none`; subset, equality, `some`/`no`/`one`/`lone`; exact integers in two's complement, as wide as each value needs | `BooleanMatrix`, which is sparse |
| `casing/model.fx` | A model's forms read; a scope made into bounds; formulas translated at each position of a trace; instances shown | Alloy's `translator/` (A4) and Pardinus's `ltl2fol` |
| `casing/casing.fx` | The command line, reading with Fixpt's own reader (`fx26:eager-reader.fx`) | |
| `casing/tests/` | Models (`.cs`) and their answers; `run.sh` (`cargo nextest run` runs each as `casing::FILE`) | |

## The language

```scheme
(sig Node (edges Node #:set))                       ; sig Node { edges: set Node }
(sig Animal #:abstract (owner Person #:lone))
(sig Dog #:extends Animal)  (sig Rex #:one #:extends Dog)
(sig Light (on Light #:lone #:var))                 ; a field that changes
(sig Lamp (on Lamp #:lone #:var @lamp))             ; …in region @lamp
(sig Guest #:var @door)                             ; a sig that changes, in @door
(sig Tmp #:in Node)                                 ; a subset sig
(fact (all ((n Node)) (not (in n (join n (^ edges))))))
(pred (two-cats (p Person)) (= (size (inter (join p owns) Cat)) 2))
(fun (kids (p Person)) (join p owns))
(assert acyclic (no (inter (^ edges) iden)))
(run two-cats 3)                                    ; default scope 3
(check acyclic 5 (Node 4) (exactly Dog 2) (steps 1 8))
```

Every declaration is its kind, its name, what it needs, and then its
options, each a keyword (FX-26's `#:name`), in any order. Alloy writes
the same modifiers before the declaration (`abstract sig`, `var sig`,
`f: lone T`); here they follow the name, so a declaration's name is
always where a reader looks for it, and a modifier can never be taken
for a name.
- **A sig:** `(sig S option… field…)`, its options:
  - `#:abstract`;
  - a multiplicity, `#:one`, `#:lone`, `#:some` or `#:set` (the default);
  - `#:extends P` (a part of `P`) or `#:in P` (a subset of `P`);
  - `#:var`, or `#:var @r` for one that changes in region `r`;
  - `#:ordered`: Alloy's `util/ordering` (below);
  - `#:fact F`, any number: `F` holds of each atom `this` of the sig, in
    every state, as Alloy's sig facts (`sig S {…} { F }`) do. Alloy
    rewrites a field `f` in `F` to `this.f`, and writes the relation
    itself `@f`; casing does not rewrite (`@` names a region), so `F`
    says `(join this f)`.
- **A field:** `(f T option…)`, `T` a sig (or an expression) or
  `(-> T U …)`, its options:
  - a multiplicity: `#:one` (the default for `T`), `#:lone`, `#:some` or
    `#:set` (the default for an arrow). As in Alloy, it applies to the
    last column: for each owner atom `x`, `(m (join x f))` holds. A sig's
    multiplicity and a field's are the same kind of thing, a constraint on
    the relation declared, so both are options. Alloy's per-column
    multiplicities, `A one -> lone B`, are not here yet; they would belong
    in the arrow, `(-> (one A) (lone B))`.
  - `#:var`, or `#:var @r`;
  - `#:disj`: distinct owners' values are disjoint (Alloy's `f: disj T`).

  `T` may mention `this`, the owner, and the other fields:
  `(best (join this likes) #:lone)` is Alloy's `best: lone likes`.

  No field may be named after an option (`(extends P)` is refused, with
  the keyword to write instead).
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
- **Declarations** (of quantifiers, comprehensions and parameters):
  `(x y T option…)`, the names, the type, then options:
  - a multiplicity: `#:one` (the default for a set), `#:lone`, `#:some`
    or `#:set` (the default for a relation, as in Alloy). Any but `one`
    makes the variable higher-order: it ranges over sets of `T`'s tuples.
  - `#:disj`: the names are bound to disjoint values, as Alloy's
    `all disj x, y: S`: a guard, implied under `all`, conjoined under the
    others.

  A comprehension's variables are each one atom.
  - connectives: `not`, `and`, `or`, `implies` (or `=>`), `iff`,
    `(if f g h)`, `let`, `true`, `false`;
  - predicate calls.
- **Integers** (below, "Integers never wrap"):
  - `Int`, the sig of integer atoms, for fields and declarations:
    `(age Int)`, `(all ((i Int)) …)`;
  - expressions: numerals; `(size e)` (Alloy's `#`, which FX-26's reader
    reserves); `(+ i j)`, `(- i j)`, `(- i)` or `(neg i)`, `(* i j)`,
    `(div i j)`, `(rem i j)`, `(mod i j)`; `(sum ((x S)) i)`; `(int e)`,
    the sum of a set's Int atoms (Alloy's `int[e]`), which a set in an
    integer's place means anyway; `if` and `let`;
  - wrapping, only when said: `(+% i j)`, `(-% i j)`, `(*% i j)`,
    `(neg% i)`;
  - comparisons: `=`, `!=`, `<`, `<=`, `>`, `>=`. `=` compares integers
    when either side is one, and sets otherwise.

  `(* r)` of one operand is the reflexive closure; of two, a product.
- **Time:**
  - future: `after`, `always`, `eventually`, `until`, `releases`;
  - past: `before`, `historically`, `once`, `since`, `triggered`;
  - `(then f g)`, which is Alloy's `f ; g`.
- **Events:** `(event (e (x T) …) #:writes w body…)`, an event a predicate
  that says which changing relations, and which regions, it may write:
  `w` is one, or a list of them. Only an event writes. The FX-flavoured
  part is below.
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
- **A run with parameters.** Each parameter is a fresh relation of its
  type, with its multiplicity (and apart from the others of a `#:disj`
  declaration), shown as `$name`, as Alloy skolemizes.
- **`one` and `lone` over several variables** count the bindings
  together, as Alloy's comprehension does: `(one ((a b S)) f)` says one
  pair.

**`util/ordering`, as a sig's option.** `(sig State #:ordered)` is
Alloy's `open util/ordering[State]` (`util/ordering.als`):
- its scope is exact, as the module's `exactly elem` makes it;
- a relation `next` puts each ordered sig's atoms in a line;
- the module's functions and predicates, written in casing
  (`ordering-defs`), over `next`: `prev`, `(first S)`, `(last S)`,
  `(nexts e)`, `(prevs e)`, `lt`, `lte`, `gt`, `gte`, `larger`,
  `smaller`, `max`, `min`. A model's own definition of one of these names
  wins over the module's.

Alloy opens the module once per ordered sig, with names qualified as the
model opens it (`so/next`); casing has one `next` for every ordered sig,
which is sound because an ordered sig is top-level (so their atoms are
apart), and `first` and `last` take the sig. An ordered sig does not
change.

**`next` fixed, as Kodkod's symmetry breaking fixes it.** When the
ordered sigs' atoms are interchangeable, any line of them is a permutation
away from `S$0 → S$1 → …`, so casing fixes `next` to that, with no
inputs to the solver. They are not interchangeable when a `one` part of an
ordered sig has an atom of its own: then `next` is the solver's to pick,
within each ordered sig, with facts that make it a line
(`tests/ordering-free.cs`, where Monday may be last).

**More than Alloy: higher-order quantifiers.** Alloy translates a
higher-order quantifier only when Kodkod can skolemize it; otherwise
"Analysis cannot be performed since it requires higher-order
quantification that could not be skolemized". casing knows, as it
translates, each formula's polarity: positive, negative, or both (under
`iff`, an `if`'s condition, `one`/`lone`, and in an expression).
- **Where a quantifier is existential** (`some` positively, `all` or `no`
  negatively), its variable is a set of fresh inputs to the solver, with
  its multiplicity: skolemization done during the translation. Each
  translation of the quantifier gets its own set, so this holds under
  `all` (as a skolem function would, one set for each binding outside)
  and under temporal operators (one for each position), which Kodkod
  skolemizes only at the top.
- **Elsewhere**, a universal over sets in a fact, say, the variable is
  bound to each set of its type's tuples in turn, up to `most-sets`
  (1024) of them: so `(all ((s Node #:some)) …)`, which says a graph is
  strongly connected, works at small scopes (`tests/decls.cs`).

**Not as Alloy.**
- **Integers never wrap** (decided 2026-11-08: "Arithmetic should never
  wrap; we should have explicit modular atomic operations for the cases
  where that is desired"). Alloy's integers are two's complement of the
  scope's bitwidth, and every operation wraps: `7 + 1` is `-8` at
  bitwidth 4, so `all i: Int | i + 1 > i` has a counterexample. Its
  `noOverflow` option instead drops instances that overflow, which makes
  a formula's meaning depend on where it stands. casing separates two
  things Alloy joins:
  - **an integer's value** is exact. Each operation's result is as wide as
    it needs (`matrix.fx`: a sum one bit wider than its operands, a
    product as wide as both), so `(all ((i Int)) (> (+ i 1) i))` holds,
    a sum of prices may pass 7, and `(* -8 -8)` is 64;
  - **Int's atoms** are a bounded set: `-2^(b-1)` to `2^(b-1) - 1` for
    the scope's bitwidth `b` (`(Int b)`, 4 if not said, 1 to 8). An
    integer where a set is expected is its atom, or none if no atom has
    its value. So an event that sets a counter to `(+ n 1)` cannot happen
    at the top (`tests/ints-time.cs`), where Alloy's would go to `-8`.

  `+%`, `-%`, `*%` and `neg%` are the explicit modular operations: the
  exact value, wrapped to the bitwidth, as Zig's `+%`. `mod`'s remainder
  is never negative (Euclidean); `div` truncates toward zero and `rem`
  takes the dividend's sign, as Alloy's (and Java's) do.
- **Dividing by zero is not said.** Alloy (Kodkod) defines `x / 0`; casing
  leaves its quotient and remainder to the solver, as SMT-LIB leaves them,
  so a model that depends on them has a counterexample that shows it
  (`tests/ints.cs`, `by-zero`).
- **Int's atoms are in the universe only when a model mentions `Int`**
  (or its scope does). Alloy's `univ` always holds them; casing's matrices
  have a cell for each tuple of atoms, and 16 more atoms would make every
  binary relation's matrix of a 3-atom model 40 times larger. A sig may not
  be named `Int`.
- **A relation's matrix is dense:** n^arity cells. That is fine at the
  scopes casing runs today, and too costly for arity 3 or more at large n.

## FX's flavour: events say what they write

Alloy 6 makes the modeller write each event's frame conditions by hand:
everything the event does not change stays as it was. casing's `event`
says which changing relations it may write, as an FX procedure's effect
says which regions it may write. The rest are unchanged, by construction:

```scheme
(event (toggle (l Light)) #:writes on
  (if (some (join l on)) (no (join l (prime on))) (= (join l (prime on)) l)))
(fact (always (or (stutter) (some ((l Light)) (or (toggle l) (press l))))))
```

`toggle` leaves `pressed` as it is without saying so (`tests/light.cs`).

**Regions.** As an FX procedure's effect names regions rather than each
location it writes, a relation that changes may say the region it
changes in, and an event may write the region:

```scheme
(sig Lamp (on Lamp #:lone #:var @lamp) (level Lamp #:set #:var @lamp))
(sig Door (open Door #:lone #:var @door))
(sig Guest #:var @door)
(event (switch (l Lamp)) #:writes @lamp …)            ; on and level
(event (prop (l Lamp) (d Door)) #:writes (@lamp open) …)  ; both kinds at once
(assert enter-alone (always (implies (enter) (unchanged @lamp))))
```

Regions are declared by use: a region is the relations that name it.
A relation is in at most one region, and need not be in any. An event
may name relations as well as regions, as above. casing refuses a `writes`
that names a relation that does not change, or a region nothing changes
in (`tests/regions.cs`).

An FX-style effect discipline goes further than this:
- events whose writes are disjoint commute, which partial-order reduction
  could use;
- a predicate typed `pure` cannot mention `prime`;
- a check could say which relations a property reads.

## Not yet: what Alloy 6 can say that casing cannot

Taken from Alloy 6's grammar (`org.alloytools.alloy.core/parser/Alloy.cup`
at ed89fdb) against what casing reads, 2026-11-08. Most of Alloy's
relational and temporal logic is here: relations of any arity, every
relational operator, the five quantifiers, `let`, `if`, predicates and
functions, every temporal operator past and future, `prime` and `then`,
`var` sigs and fields, subset and abstract sigs. What is missing is mostly
the declaration layer and the library. In order of how much each limits what
a model can say:

1. **Integers.** casing has Alloy's, exact (above). Not yet: shifts
   (`<<`, `>>`, `>>>`) and `util/integer`'s `min`, `max`, `next`, `prev`
   over Int.
2. **Declarations.**
   - **Per-column multiplicities** in an arrow, all sixteen of
     `A m -> n B` (`ONE_ARROW_LONE` and the rest). casing has only the
     last column's, as a field's option. They would be written in the
     arrow: `(-> (one A) (lone B))`.
   - **`disj f, g: T`**, two fields disjoint as relations (a fact says
     it). `f: disj T` is `#:disj`.
   - **`enum`.**
   - **Overloading and the receiver call** `x.p[y]`: sugar for `(p x y)`.
3. **The library and modules.**
   - **`util/integer`, `util/boolean`, `util/relation`, `util/graph`.**
     (`util/ordering` is `#:ordered`. An ordered sig must be top-level;
     Alloy also orders subsigs.)
   - **`seq`** and `util/sequniv`, which are indexed by Int (item 1).
   - **`String`** and string literals.
   - **Modules:** `open`, parameterized modules, `private`, top-level
     `let` macros.
4. **Commands.**
   - **`expect 0` / `expect 1`.**
   - **Scopes:** `but`, a `seq` length. (`(Int b)` is the bitwidth.)
   - **Unbounded traces** (`1..` steps). With its nuXmv or NuSMV back end,
     Alloy 6 checks temporal properties of traces of any length. That is
     another decision procedure, not a missing piece of the translation.
5. **Sugar.** The implicit `this.f` in sig facts and field types, and
   `@f`; the box join `e[x]`; the negated comparisons `!in` and `!<`;
   `else` after `=>`. casing has an equivalent of each (`(join this f)`
   for the first); they matter only for transliterating Alloy's models.

**Checks Alloy makes that casing does not** (`parser/CompModule.java`):
- errors: an exact scope on a `var` sig, and a scope on a `var` sig that
  is not top-level;
- warnings: a static part of a `var` sig, `var` on a part of a static sig
  (redundant), a static field inside a `var` sig, and a static field whose
  type mentions a `var` sig;
- Alloy's type system: casing checks arity only, not that a join relates
  the sigs it should, and gives no relevance warnings.

**Not of expressive power, but of the analysis:**
- **Symmetry breaking.** Kodkod's lex-leader predicates over
  interchangeable atoms. Without them, an unsatisfiable check explores
  every permutation of each instance.
- **Memoizing translations.** A subformula is translated again for each
  loop and position that reaches it. The circuits are hash-consed, so the
  formula is the same, but the time grows with temporal nesting.
- **More instances**, by blocking each one found: Alloy's "next".
- **Cross-checking against Alloy itself.** Run the same models in Alloy 6
  and compare the answers. This needs a JDK newer than this machine's 11.

The list suggested on 2026-11-08 (`#:disj` and declarations'
multiplicities, `util/ordering`, sig facts with `this`, integers) is done.
