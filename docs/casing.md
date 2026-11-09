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
    bin/casing --instances N MODEL.cs   up to N instances of each
    bin/casing --count [--limit N] MODEL.cs   how many each has
    bin/casing --symmetry N MODEL.cs    symmetry breaking (20; 0: none)

## Files

| file | what | after |
| --- | --- | --- |
| `casing/circuit.fx` | Boolean circuits: hash-consed n-ary AND gates over signed ids, Tseitin-encoded into combo's solver lazily, only what an assertion reaches | Kodkod's `engine.bool` (`CBCFactory`, `Bool2CNFTranslator`) |
| `casing/matrix.fx` | A relation as a dense matrix of circuits, one cell per tuple (tuple index = its atoms in base n). Union, intersection, difference, product, join (an (∨, ∧) matrix product), transpose, closure by squaring, override, restriction, `iden`/`univ`/`none`; subset, equality, `some`/`no`/`one`/`lone`; exact integers in two's complement, as wide as each value needs | `BooleanMatrix`, which is sparse |
| `casing/model.fx` | A model's forms read; a scope made into bounds; formulas translated at each position of a trace; instances shown | Alloy's `translator/` (A4) and Pardinus's `ltl2fol` |
| `casing/casing.fx` | The command line, reading with Fixpt's own reader (`fx26:eager-reader.fx`) | |
| `casing/tests/` | Models (`.cs`) and their answers; `run.sh` (`cargo nextest run` runs each as `casing::FILE`) | |
| `casing/xcheck/` | The test models in Alloy (`.als`) and `xcheck.sh`, which runs both and compares each command's verdict (below) | |

## The language

```scheme
(sig Node (edges Node #:set))                       ; sig Node { edges: set Node }
(sig Animal #:abstract (owner Person #:lone))
(sig Dog #:extends Animal)  (sig Rex #:one #:extends Dog)
(sig Light (on Light #:lone #:var))                 ; a field that changes
(sig Lamp (on Lamp #:lone #:var @lamp))             ; …in region @lamp
(sig Guest #:var @door)                             ; a sig that changes, in @door
(sig Tmp #:in Node)                                 ; a subset sig
(enum Color Red Green Blue)                         ; enum Color { Red, Green, Blue }
(fact (all ((n Node)) (not (in n (join n (^ edges))))))
(pred (two-cats (p Person)) (= (size (inter (join p owns) Cat)) 2))
(fun (kids (p Person)) (join p owns))
(assert acyclic (no (inter (^ edges) iden)))
(run two-cats 3)                                    ; default scope 3
(check acyclic 5 (Node 4) (exactly Dog 2) (steps 1 8))
(run two-cats 3 #:instances 5)                      ; the first 5 instances
(run two-cats 3 #:count #:limit 1000 #:symmetry 0)  ; how many, up to 1000
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
- **A field:** `(f g … T option…)`, one or more names, `T` a sig (or an
  expression) or an arrow `(-> T U …)`, its options:
  - a multiplicity: `#:one` (the default for `T`), `#:lone`, `#:some` or
    `#:set` (the default for an arrow). As in Alloy, it applies to the
    last column: for each owner atom `x`, `(m (join x f))` holds. A sig's
    multiplicity and a field's are the same kind of thing, a constraint on
    the relation declared, so both are options.
  - `#:var`, or `#:var @r`;
  - `#:disj`: the names are disjoint relations (Alloy's `disj f, g: T`),
    as the names of a quantifier's declaration are disjoint values;
  - `#:apart`: distinct owners' values are disjoint (Alloy's `f: disj T`).

  `T` may mention `this`, the owner, and the other fields:
  `(best (join this likes) #:lone)` is Alloy's `best: lone likes`.

  No field may be named after an option (`(extends P)` is refused, with
  the keyword to write instead).
- **An arrow's multiplicities**, wherever an arrow is a type (a field's, a
  declaration's) or the right of `in`: an operand may say its
  multiplicity as a column of the arrow, `(col X #:m)`.
  `(-> (col A #:one) (col B #:lone))` is Alloy's `A one -> lone B`: each
  tuple of A maps to `lone` of B's, each of B's to `one` of A's. Several
  operands nest to the right, as Alloy's `->` does:
  `(-> A (col B #:one) (col C #:one))` is
  `(-> A (-> (col B #:one) (col C #:one)))`, for each a a bijection of B
  and C. An operand of several columns is one group: `(col (-> B C)
  #:lone)` is Alloy's `lone (B -> C)`, at most one pair.

  Why `col`, a word at the head (2026-11-08): `(one B)` already says, as
  a formula, that B has one atom, and `(B #:one)` would read as a call;
  a relation is columns, as its instances show (`a->b->c`), so the
  operand is named as one, its multiplicity its option, as everywhere
  else. `(one B)` in an arrow is refused, with the `col` to write; a
  multiplicity outside an arrow is an option (`#:lone`), and `col`
  outside one is refused.
- **`(enum E v …)`**: Alloy's `enum`, an abstract sig `E` with a `one` part
  for each value, `#:ordered`; its scope is its values, and its order is
  as written, fixed (Alloy fixes it so, `BoundsComputer`).
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
- **More instances** (`#:instances n`, `#:count`, `#:limit n` on a
  command, or `--instances N`, `--count`, `--limit N` for every command),
  as Alloy's "next": each found, the solver is told it is not to be found
  again, and asked again (combo's solver is incremental, so the problem is
  not made again).
  - Instances are told apart by every relation's tuples and every
    witness's, as Alloy tells them: two that differ only in a skolem's
    value are two.
  - A model that changes: more traces of the first's configuration (its
    static relations and witnesses as they are), as Alloy's "next" is
    Pardinus's `nextP` ("New config" in Alloy's window, `nextC`, is not
    here). When no other trace of k states is left, traces of k+1 are
    sought, up to the scope's most steps; each a trace not found before,
    whatever lasso spells it. Two lassos, of k and k' states looping back
    p and p' states, spell one trace when they agree at its first max(k,
    k') + lcm(p, p') positions; so the block is a circuit over the new
    problem's states and its loop's inputs (`block-snapshot!`).
- **Symmetry breaking** (`#:symmetry n`, `--symmetry N`; 20 if not said,
  as Alloy's; 0, none), Kodkod's lex-leader (`break-symmetry!`):
  - swapping two neighbouring atoms is a symmetry when it maps every
    relation's cells, in every state, and every witness's, to cells of the
    same kind (true, false, or an input): a formula names relations, not
    atoms. Int's atoms never are (arithmetic reads their values); nor are a
    `one` sig's atom, or an ordered sig's when its order is fixed, as the
    bounds say;
  - for each such swap: the cells it moves, read as a word, true before
    false, are no greater than their images; only the first n cells. Of
    each set of instances that differ by renaming such atoms, the least
    satisfies it. True first puts an instance in the first atoms;
  - so a check with no counterexample tries fewer permutations, and
    `#:count` counts fewer instances: with `#:symmetry 0` the count is of
    every instance, which is what can be compared with Alloy's (below).

**Libraries: `(open util/relation)`, `(open util/graph S)`.** Alloy's
`util/relation` and `util/graph[node]`, written in casing
(`relation-defs`, `graph-defs`), their names in kebab-case:

| Alloy | casing |
| --- | --- |
| `dom`, `ran`, `total`, `functional`, `function`, `surjective`, `injective`, `bijective`, `bijection`, `reflexive`, `irreflexive`, `symmetric`, `antisymmetric`, `transitive`, `acyclic`, `complete`, `preorder`, `equivalence` | the same |
| `partialOrder`, `totalOrder` | `partial-order`, `total-order` |
| `undirected`, `ring`, `dag`, `forest`, `tree`, `roots`, `leaves` | the same |
| `noSelfLoops`, `weaklyConnected`, `stronglyConnected`, `rootedAt`, `treeRootedAt`, `innerNodes` | `no-self-loops`, `weakly-connected`, `strongly-connected`, `rooted-at`, `tree-rooted-at`, `inner-nodes` |

`util/graph` is opened on a sig, which stands for its `node`; it uses
util/relation's definitions as `relation/…`, as Alloy's opens it `as rel`,
so opening the graph library does not open the relation library's names.
`#:as a` names a library's definitions `a/…`, so a model may open
util/graph on two sigs (`(open util/graph P #:as pg)`, `(pg/dag le)`). A
model's own definitions win over a library's, wherever they are written.
casing has no modules of a model's own (below).

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

**Types, as Alloy's warnings.** Before its commands' answers, casing
says where Alloy's types show a mistake (`tests/types.cs`):

    warning: in fact 1: (join owns owns): the join always yields an empty set

An expression's type is a union of tuples of sigs: each a top-level sig
or a part of one (a subset sig is typed by its parent), `univ`, or `Int`.
Two sigs overlap when one is the other or below it. casing warns of a
join, `inter`, `<:` or `:>` that is always empty, and of `in`, `=` or
`!=` whose sides are always disjoint, in facts, sig facts, fields' types,
definitions (their parameters typed as declared), assertions and
commands. A function's call is typed by its body, its parameters by the
arguments. A type casing cannot tell says nothing. As in Alloy, these are
warnings: what is found is the same.

**Witnesses, as Alloy's skolems.** An existential at the top of a
command's formula (not under a universal, a temporal operator, or
`one`/`lone`; through `and`, `or`, `not` and calls), first-order or not,
is skolemized there, and its set is shown with what is found, `$x`; for a
check, it is the counterexample's (`$p = {Person$0}`: the person who owns
nothing). Two of one name are `$x` and `$x_1`. Below the top, a
quantifier is translated once for each binding or state, and its sets are
not shown.

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
   - **Overloading and the receiver call** `x.p[y]`: sugar for `(p x y)`.
     (Arrow multiplicities, fields declared together and disjoint, and
     `enum` were done 2026-11-08.)
3. **The library and modules.**
   - **`util/integer`, `util/boolean`.** (`util/relation` and `util/graph`
     are opened with `open`.)
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
- Alloy's type errors (as opposed to its warnings, which casing gives):
  casing reports a wrong arity as it translates, not before; and Alloy's
  "redundant" warnings (a subexpression that is always empty, an `=`
  whose sides are always equal) and unused variables.

**Not of expressive power, but of the analysis:**
- **Symmetry breaking beyond neighbouring atoms.** Kodkod's detector
  partitions the atoms into classes from the bounds; casing tries only
  each atom and the next. Its universe puts each sig's atoms together,
  but a class whose atoms are not next to each other would be missed
  (not broken, never wrongly broken).
- **Memoizing translations.** A subformula is translated again for each
  loop and position that reaches it. The circuits are hash-consed, so the
  formula is the same, but the time grows with temporal nesting.
- **New config and new fork** (Pardinus's `nextC` and `nextS`): more
  instances of a model that changes are only more traces of the first's
  configuration.
- **Witnesses below the top.** An existential under a universal or in a
  state is translated once for each binding or state; its sets are not
  shown (Alloy shows skolem functions of the bindings outside).

The list suggested on 2026-11-08 (`#:disj` and declarations'
multiplicities, `util/ordering`, sig facts with `this`, integers) is done.

## Cross-checked against Alloy

`casing/xcheck/xcheck.sh [--count] [NAME …]` runs each test model `NAME.cs` and its
Alloy version `xcheck/NAME.als` (and any `NAME.*.als`) in Alloy 6.2.0's
command line, and compares the verdicts command by command: an instance
or counterexample found, or not. Before each Alloy command a marker
`--# i` names the casing command it stands for. `--# i differs: why`
marks one meant to differ, and `--# i skip: why` one Alloy cannot say.
It needs Alloy's jar (`$ALLOY_JAR`, by default
`~/Dev/LangPlay/alloy-6.2.0/org.alloytools.alloy.dist.jar`, from the
v6.2.0 release) and Java 17 or later (`$JAVA`, by default the snap's
`openjdk.java`). It is not among `cargo nextest`'s tests, since it needs
Java.

On 2026-11-08, for all 19 models (90 commands, in 17 s):
- **82 agree**, temporal ones among them (lassos, past operators over the
  loop, var sigs, regions written out as frame conditions);
- **2 differ, as meant:** `1 div 0` (Alloy defines it; casing leaves it to
  the solver), and a sum past 7 (Alloy's noOverflow drops the instance;
  casing's sum is exact);
- **6 are not said in Alloy:** universal, `one` and `lone` quantifiers
  over sets, which Alloy cannot skolemize; values out of range; `mod`.

Alloy's warnings on `types.als` are casing's on `types.cs`, one for one.

**Counts.** With `--count`, the instances (or counterexamples) of each
command are counted by both, with no symmetry broken, up to 2000
(`$XCHECK_CAP`), and the numbers must agree, or both reach the cap. A
command marked `differs` is not counted, nor one marked
`--# i uncounted: why`. With symmetry broken the counts are not
comparable: Kodkod's breaking and casing's need not remove the same
instances (on small models they do: `tests/instances.cs`'s 27 of 56).

On 2026-11-09 (42 s): **81 agree**, 39 of them not 0 (from 1 to 1216,
and 8 that reach the cap), the temporal ones among them (39 traces of
`light`'s first command); 3 are not counted (`1 div 0`, the sum past 7,
and `ints.wrap.als`, a smaller model than `ints.cs`).

The counts found what the verdicts had not: `regions.als`'s `enter`
kept the door's `opened` unchanged, but casing's writes `@door`, which
holds `open` as well as `Guest`. The verdicts agreed by chance; the
counts (16 against 12, 33 against 10) did not.

Alloy's command line reads no `-y` (its symmetry setting): `CLI.java`
sets the symmetry from `-d`, the skolem depth (`opt.symmetry =
options.depth(opt.symmetry)`, at ed89fdb). So `-d 0` is how to turn
symmetry breaking off (and skolemize only at the top, as casing's
witnesses are). Alloy's "next" for a model that changes keeps the
configuration (`TemporalPardinusSolver`'s `next` is `nextP`), and casing
does the same.

Writing the models in Alloy showed two differences of syntax, not of
meaning:
- in a sig fact Alloy reads a field `f` as `this.f`, so `this.f` there is
  `this.this.f`, a type error; casing's `(join this f)` is fine;
- `next` and `prev` of `util/ordering` clash with `util/integer`'s
  unless qualified (casing's `Int` has neither).
