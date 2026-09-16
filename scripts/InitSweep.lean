/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import Lean

/-!
# Init sweep: whole-library accounting of what a module costs when it is loaded

Walks the compiled environment and flags every constant whose module initialiser evaluates
something — before any `main` runs — when the value that runs materialises an enumeration of
a type.

The predicate, in one sentence: *a constant is flagged when loading its module evaluates a
value on its behalf — its own, because its compiled declaration takes no parameters, or an
`initialize` body registered for it — and that value either names one of
`enumerationEntryPoints` or names a *builder* of an `enumerationClasses` member.* A module's
initialiser also evaluates declarations that are **not**
environment constants — specialisations the compiler lifts out of functions, and boxed
numeric constants — which have no value to read; those are counted separately and tested by
the only thing they carry, their mangled name.

Every clause is load-bearing; `scripts/test-initsweep.sh` carries the fixtures that
falsify each one. Numeric censuses and C-emission comparisons below record the original
pre-stack build. They are measurements, not invariants of later heads: use the report from
the exact head being validated for current counts. The declaration fixtures and baseline
matching rules, rather than a fixed whole-library count, establish the gate's contract.

* **the module initialiser evaluates something for it.**
  `Lean.Compiler.LCNF.emitDeclInit`
  (`Lean/Compiler/LCNF/EmitC.lean:986`) has exactly three sites that emit work into the
  module initialisation function: the bare call for an `initialize do` block (988-991), the
  call-and-assign for the initialiser registered for an `initialize x : T ← e` (992-1002),
  and `x = _init_x();` for a parameterless declaration that is neither a lifted closed term
  nor a simple ground expression (1003-1005). `loadTimeSource` mirrors those three branches
  and nothing else. A declaration without parameters is a value whose cost is paid at load
  time whether or not anything reads it.

  A declaration *with* parameters is not itself initialised — but that is not the same as
  costing nothing at load, and the difference is a real hazard rather than a technicality.
  The compiler may lift a parameterless **specialisation** out of a monomorphic function's
  body, and when the specialisation's result is a ground value the backend assigns it in the
  module initialiser like any other value. Measured, with the emitted C as ground truth:
  `def carrierCount (_u : Unit) : Nat := Fintype.card (Fin 3 → Bool)` declares no
  parameterless constant, and its module's initialiser nevertheless runs
  `_init_…Fintype_card___at___00….carrierCount_spec__0()`, which forces a closed term built
  by `Fintype.piFinset` — the function this gate exists for. Two neighbouring shapes are
  genuinely free, and the difference is worth knowing: `def mkY (_u : Unit) : Fintype T :=
  inferInstance` returns an already-initialised pointer, and
  `def elemsY (_u : Unit) : Finset T := Finset.univ` keeps its closed term behind a
  `lean_obj_once` cell that is forced on the first call.
  `VCVioInitSweepTestFixtures.Hazard.Specialised` is the first shape; the two controls in
  `Clean/Negatives.lean` are polymorphic, so nothing can be specialised at a fixed carrier,
  and they are safe for that reason rather than for the reason a reader might assume.

  The LLVM backend's `Lean.IR.EmitLLVM.emitDeclInit` (`Lean/Compiler/IR/EmitLLVM.lean:1282`)
  makes the same parameterless decision (`d.params.size == 0`, line 1294) and is **strictly
  more eager**: its `| none =>` branch (1329) calls the pure initialiser unconditionally,
  with no closed-term or ground-expression exemption, so on that backend all 511 value-route
  constants of this tree are evaluated at load. (`EmitLLVM.lean:1239`, which tests
  `xs.size == 0` inside `emitDeclAux`, is a symbol-visibility decision and not this one.)

  One deliberate difference from the emitter: its `getInitFnNameFor?` test is nested inside
  `decl.params.isEmpty` and `loadTimeSource`'s is not. Measured over the 27172 constants of
  the seven swept libraries: 531 parameterless compiled declarations = 511 on the value
  route + 20 `initialize x : T ← e`, and **no** constant satisfies both the `initialize` and
  the `isIOUnitInitFn` test, so the nesting cannot change a verdict on this tree.

  That correspondence is checked against emitted code rather than only read off the
  compiler source. Over the seven swept libraries the predicate names 27 constants on the
  `initialize` route and 511 on the value route; the C under `.lake/build/ir/` for the same
  634 modules contains 27 initialiser calls, 20 of which assign a result (the 20
  `initialize x : T ← e` declarations, the other 7 being `initialize do` blocks), and 496
  `_init_` assignments. The last pair is **not** a subset relation, and the honest
  comparison is by C symbol (`Lean.getSymbolStem`):

  * **218** are in both: value-route constants the C really does assign from `_init_`;
  * **293** are predicted only, and every one of the 293 is emitted as a static literal
    instead — see `isCompiledValue`;
  * **278** are emitted only, and every one of the 278 is a `___boxed__const__N` symbol — a
    boxed numeric constant, not an environment constant, and so unnameable by a sweep of the
    environment. That population is not left at that: it is what the compiled-declaration
    walk below covers, and 0 of the 496 assignments is a lifted closed term (`___closed__N`),
    which is the measurement `isLiftedClosedTerm` rests on.

  218 + 293 = 511 and 218 + 278 = 496. For one module the correspondence was also checked
  name by name: for `VCVio.Prelude` the predicate names 9 constants and
  `.lake/build/ir/VCVio/Prelude.c` performs exactly those 9 evaluations — four `_init_`
  assignments, four initialiser calls assigning a result, one bare initialiser call.

  This is where a `noncomputable` marker acts, and why a source-level rule is the wrong
  instrument: marking an instance `noncomputable` removes the instance's own compiled code
  and leaves the compiled auxiliary that carries the work, so the two spellings differ in
  source and not in effect. `@[extern]` declarations are excluded in the other direction:
  the emitter calls the foreign symbol, and the Lean-side value is dead.

  The clause is also strictly narrower than "its type is not a `∀`", which the shape of
  the hazard suggests and which would be wrong: 531 constants of the swept libraries have
  a parameterless compiled declaration, while 867 have a compiled declaration and a
  non-`∀` type, the extra 336 being values whose type unfolds to a function type.
* **that value materialises an enumeration of a type.** The load-time population is 538
  constants, and the rest of it is parser descriptors, macro expanders, attribute and
  environment-extension registrations, `IO.Ref` cells and small closed values; a ceiling
  on *that* number would be noise. Two disjuncts do the narrowing, and the second is the
  one that makes the clause a class test rather than a spelling test:
  `enumerationEntryPoints` names the library functions that enumerate, and
  `enumerationClasses` catches any *builder* of an enumeration class — which is what
  `Pi.instFintype`, `Fin.fintype`, `Fintype.mk` and `FinEnum.ofList` are, however the author
  spelled the instance that uses them.
* **and the same test on the compiled declarations that have no constant.** The module
  initialiser assigns compiler-generated parameterless declarations beside the constants:
  specialisations (`Fintype.card._at_.<caller>.spec_0`) and boxed numeric constants. They are
  not in the environment, so there is no value to read and the name is all there is;
  `irDeclEvidence` tests the functions the specialiser recorded in it — by name against the
  entry points, and by what they consume, which is what survives the instance being
  specialised away. Measured over the seven default roots: 1473 such declarations, 0 of
  which carry evidence of either kind. 278 of the
  1473 are assigned in the emitted C and the rest are laid out as literals, and — the
  direction that matters — **all 278** of the `_init_` assignments that are not environment
  constants are inside the 1473, checked by C symbol. So the two halves of the sweep between
  them name every constant and every compiled declaration the 634 modules' initialisers
  assign.

Compiler-internal names are deliberately **not** skipped. The hazard this gate exists for
is carried by an auxiliary — in the fixtures, `….instFintypeYBundle._aux_1`, and the
instance that motivated the gate produced one of the same shape — and not by the
user-written instance; skipping internal names would make the gate blind to every spelling
of it.

Modes (run after `lake build`):

```
lake exe initsweep                     # summary only
lake exe initsweep --out report.json   # also write the whole load-time population
lake exe initsweep --check             # gate against scripts/init_sweep_baseline.json
lake exe initsweep --update-baseline   # rewrite the baseline from the current build
```

The committed baseline (`scripts/init_sweep_baseline.json`) is a **list of constant names**
with the entry points each one is accepted for, rather than a per-library count: accepting
one benign instance costs exactly that one name and leaves every other constant of its
library at zero. It is the `scripts/axiom_baseline.json` idea — an
allowlist keyed by declaration, argued row by row in review — with a scope attached, which
`axiom_baseline.json`'s flat name lists do not have: a row covers one constant *under one
library* and exactly the entry points it lists, so `--update-baseline` over a partial
`--root` set rewrites only those libraries' rows and preserves the rest, and a row written
for one sweep cannot green the same name in another.

Its nine rows, read off the emitted C rather than off their names:

* `SLHDSA.Security.instFintypeTargetRole` and `OneTimePad.Separated.instFintypeNode` —
  `Fintype` instances on 8- and 6-constructor enumerations with `elems` written out in
  source. Both are assigned in their module's initialiser: they really do build their
  `Finset` at load, and it is eight and six elements.
* `instFinEnumBool_toMathlib` — `FinEnum Bool` built by `FinEnum.ofList [true, false]`, so
  the two-element list really is materialised at load.
* `FinRatPMF.Demo.instFinEnumBool_vCVio`, `instFinEnumUSize_vCVio`,
  `instFinEnumISize_vCVio` — hand-written `FinEnum.mk` instances, initialised at load but
  materialising nothing: a numeral and two closures. The `USize` and `ISize` rows are the
  ones worth re-reading if `FinEnum`'s constructors ever change, since their `card` is
  `2 ^ System.Platform.numBits`.
* `VCVioTest.Computability.toyForkProb` — a load-time value that applies a parameterised
  `FinEnum` instance for a two-element coin spec.
* `SMDTOpenPREFinalValidityTest.instFintypeInput` (a one-element `Fintype`) and
  `VCVioTest.PFunctorFacade.instFintypeTriPFunctor` (a `PFunctor.Fintype`, a different class,
  whose `Fin 3` instance sits inside a lambda) — these two are **not** initialised at load at
  all: the emitter lays each of them out as a static literal
  (`LEAN_EXPORT const lean_object* … = (const lean_object*)&…___closed__0_value;`). They are
  the price of the over-approximation `isCompiledValue` documents, and they are why that
  docstring says what it costs.

Known limits, measured or constructed rather than assumed. The first two are about *size*,
which this gate cannot see at all; the next three about what it can and cannot name; the
rest about reach.

* It says nothing about how **large** an enumeration is, only that one is built. A `Fintype`
  on an eight-element type is flagged exactly like a `Fintype` on `Bytes 16`; that is what
  the baseline rows are for.
* A value whose size is given as an **argument** rather than by a type is deliberately out
  of scope: `List.range n`, `Finset.range n`, `Multiset.range n`, `List.finRange n`,
  `Array.replicate n x`, `List.replicate n x`. The gate's subject is a cost fixed by a
  *type*, because that is the cost a reviewer cannot see at the site — `bundle.Y` says
  nothing about `2 ^ 128` — whereas `Finset.range (2 ^ 40)` carries its size in the diff
  that introduces it. This is a boundary, not a claim of safety: `Finset.range (2 ^ 40)` is
  the same hazard, and `def n := 2 ^ 40` in another file hides its numeral just as well.
  Measured over the load-time population today: `List.range` occurs once
  (`SLHDSA.Concrete.Keccak.piLUT`, `List.range 5`), `Array.replicate` three times
  (`SLHDSA.Concrete.zeros48`, `SLHDSA.C13.Concrete.zeros16`, `SLHDSA.C13.Concrete.ffWord`),
  and `Finset.range`, `Multiset.range`, `List.finRange`, `List.replicate` not at all.
  Gating that class would mean enumerating every size-taking constructor in the library,
  which has no principled boundary; the four occurrences above would be its first four
  baseline rows.

  One family sits on the line and is settled here rather than left implicit: `Array.ofFn`,
  `Vector.ofFn` and `List.ofFn` take their size from a `Fin n` **type index**, so by the
  letter of "fixed by a type" they would be in scope. They are out, on the rationale rather
  than the letter — the `n` is written at the application and is as visible as
  `Array.replicate`'s — and the measurement says what that costs: over the load-time
  population `Array.ofFn` occurs once (`Extern.Falcon.Instance`'s `sampleSamplerSeed`),
  `Vector.ofFn` twice (`MLDSA.Concrete.rqEquivCoeffFun`, `MLKEM.Concrete.rqEquivCoeffFun`)
  and `List.ofFn` not at all, so gating them would cost three baseline rows for three
  constants whose size is a literal at the site.
* It reads the value that runs, and only that value. A helper **function** that enumerates
  and is *called* from an initialiser is the same hazard and is not flagged — constructed:
  `def h (u : Unit) : Nat := (Finset.univ : Finset (Fin 3 → Bool)).card` with
  `def top : Nat := h ()` is accepted, because `top`'s value names only `h`, whose type is a
  `∀`. The class disjunct closes the *polymorphic* version of this (a helper that takes or
  returns a `Fintype` names one in the elaborated term), not the monomorphic one.
  Following the compiled code instead does not help: by the time the IR exists the
  enumeration has been folded into closed terms whose names carry no signal at all
  (measured — the fixture's flagged auxiliary reaches `Fintype.piFinset._redArg` through
  its IR and no `Finset.univ` anywhere).
* A hand-rolled enumerator that names nothing from the library is not flagged — constructed:
  a `List (Fin 3 → Bool)` built by nested `List.flatMap` over `[true, false]` is accepted.
  The gate keys on named entry points and on types, so an enumeration written from scratch
  is invisible to it.
* A **closure** carries the enumeration past all three compiled-declaration tests, because
  the specialised function then consumes no enumeration class at all. Constructed:

  ```lean
  @[specialize] def applyIt (f : Unit → Nat) : Nat := f ()
  def topApply (_u : Unit) : Nat := applyIt (fun _ => (Finset.univ : Finset P8).card)
  ```

  The module's initialiser assigns exactly one thing, `applyIt._at_.topApply.spec_1`, whose
  chain forces a closed term built by `Fintype.piFinset`; the gate reports the module clean.
  The declarations that *do* carry `Fintype.piFinset` in their names are lifted closed terms,
  which this clause excludes by construction. Three measurements bound it: `@[specialize]`
  occurs **0** times in the nine swept libraries; without the attribute the same module's
  initialiser is **empty**; and `List.map`, `List.foldl` and `Option.map` over the same
  closure each produce **no** eager assignment at all. Closing it would mean testing the
  lifted closed terms by name, which is measurable and was measured: 3 of the 10864 closed
  terms in the seven roots carry an entry point, all three under `Fischlin.smallSumCount`,
  and the emitted C shows none of the three is ever initialised — so that change would buy
  this route at the price of flagging any module that merely *contains* a monomorphic call to
  an enumeration function, whether or not anything runs at load. The route is left open and
  named rather than closed at that price.
* A **specialisation** is caught only by what its name records, which is the chain of
  functions and not the instance. Three kinds are caught, each constructed and each in the
  fixture: a specialisation of an entry point (`Fintype.card._at_.f.spec_0`), of the other
  class's accessor (`FinEnum.toList._at_.f.spec_0`, whose result type is a `List` and which a
  test on what a segment returns cannot see), and of a *user* helper that takes an
  enumeration-class instance (`count._at_.f.spec_0`, where `count (α) [Fintype α]`). What is
  not caught is a specialisation of a function that consumes an enumeration **class the list
  does not name**: constructed, `class MyEnum (α) where all : List α` with
  `instance : MyEnum C8 := ⟨FinEnum.toList C8⟩` and `useMine (α) [MyEnum α]` — the
  specialisation `useMine._at_.topMine.spec_0` is accepted. The instance itself is flagged
  where it is defined, so the module is not reported clean; a `MyEnum` instance defined in a
  library the sweep does not cover would be missed entirely, which is the import-scope limit
  below reached one step further out.
* Conversely, the values it reads are the kernel's, and it reads the whole value: an entry
  point that occurs only in a position the initialiser never evaluates is a false positive
  rather than a false negative. Two kinds exist. An entry point under a proof argument (none
  in this tree), and an entry point under a lambda the initialiser only allocates a closure
  for — constructed:
  `def t : Thunk (Finset (Fin 3 → Bool)) := Thunk.mk (fun _ => Finset.univ)` is flagged, and
  its initialiser allocates a thunk and enumerates nothing. No row of the committed baseline
  is of that kind, and separating them would mean deciding which binders the initialiser
  forces, which is the emitter's job rather than a name test's. The summary reports the whole
  load-time population, so the margin between what is tested and what is flagged stays
  visible.
* `@[implemented_by f]` moves the hazard rather than hiding it: the attributed declaration
  is not compiled at all (so it never enters the load-time population), and `f` — which must
  have the same type, hence is itself a parameterless value — is flagged in its place.
  Constructed and measured.
* It sees only what the swept roots transitively import — the same blind spot
  `scripts/AxiomSweep.lean` documents, with the same mitigation (pair it with the
  import-completeness gate).
* Of the three test libraries, `VCVioTest` and `LatticeCryptoTest` have umbrella modules and
  **are** swept, by the `--root VCVioTest --root LatticeCryptoTest` invocation
  `scripts/validate.sh` and `.github/workflows/build.yml` run after `lake test` builds their
  oleans: 1570 constants, 79 modules, 282 load-time, three flagged and baselined today.
  `HashSigTest` is not,
  and precisely: (a) `HashSigTest.lean` does not exist, so the library name is not an
  importable module; (b) its `lean_exe` roots *are* importable one at a time
  (`--root HashSigTest.SLHDSA.Sha2KAT` sweeps 5 constants across 1 module and exits 0), but
  two of them cannot be imported together — `environment already contains 'main'`, exit 2;
  (c) `census` counts only modules whose name has a root as a prefix, so one exe root covers
  its own module and not the closure it imports. Closing it needs either a generated
  `HashSigTest.lean` umbrella (and its `main`-free equivalent) or a `census` that separates
  the import root from the attribution prefix, plus one invocation per executable root.
* It is a static check on the environment: it imports with `loadExts := false` and
  does not enable initializer execution. Lean can execute an imported initializer through
  its interpreter even when no swept-library native code is linked, so linking only the
  tool is insufficient. The gate reads serialized constant and compiler-extension data
  without loading environment extensions. The side-effect fixture first proves its
  initializer executes in a normal Lean import, then verifies that the sweep leaves its
  marker absent. Enumeration fixtures independently check that this import mode still
  exposes registered initializer bodies and compiler-generated declarations.

Exit codes are a contract with CI — `1` is a ratchet verdict, anything else an
infrastructure failure — which is why `main` traps uncaught exceptions into `2`. The
`opaqueValues` line of the summary is the gate's own completeness claim: it counts
load-time constants whose value could not be read, and therefore were accepted without
being looked at.

`scripts/test-initsweep.sh` exercises all of this against the `VCVioInitSweepTestFixtures`
library, whose `Hazard` root carries seven modules — the plain instance and the
`noncomputable` spelling that flags the same auxiliary, the named instance no entry-point
test can see, the `initialize` body, the `decide` over a bounded quantifier that writes no
instance at all, the `opaque` value the kernel hides, and the specialisations with no
environment constant to read — against one negative control per clause and the baseline's
accept / drop / narrow / widen / re-scope / preserve behaviour.
-/
open Lean

namespace InitSweep

/-- Root modules swept when no `--root` is given: the same seven non-test libraries
`scripts/AxiomSweep.lean` sweeps, and for the same reason — `Interop` is the declared TCB,
bounded by its import-isolation gate, and is not built by the main CI build job. The two
test libraries that have umbrella modules are swept by an explicit `--root` pair after
`lake test` has built them; see the module docstring. -/
def defaultRoots : Array Name :=
  #[`VCVio, `ToMathlib, `Extern, `LatticeCrypto, `HashSig, `Examples, `VCVioWidgets]

/-- The constants whose appearance in an eagerly-initialised value means the initialiser
enumerates a type. Listed in source, with the reason each one is here, so the gate's reach
is auditable where the gate is rather than in a data file.

Each reason below is what the **emitted C** does for a load-time constant that names it, not
what its declaration looks like: `lean … -c` over one constant per name, with the initialiser
chain read. That matters because two of these were first excluded on a reading of the
declaration — `FinEnum.toList` because it "returns a `List`", `FinEnum.card` because it "is a
field, so reading it costs a pointer" — and the emitted C contradicted both.

* `Finset.univ` — the enumeration itself; the elements of a type as a `Finset`. Its constant's
  `_init_` forces a closed term that builds the `Finset`.
* `Fintype.elems` — compiles to exactly the same thing: the projection is folded through the
  instance and the constant forces the same closed term `Finset.univ` does (measured, same
  symbol).
* `Fintype.card` — forces the enumeration in order to count it; its `_init_` chain ends in a
  `Fintype.card._at_.…` specialisation of the carrier.
* `Fintype.piFinset` — the product enumeration; this is what the `2 ^ 128` initialiser
  that motivated this gate actually built.
* `Fintype.ofFinite` — the noncomputable route from a `Finite` proof to a `Fintype`. A
  constant naming it *and* carrying compiled code means the route that was supposed to
  erase the enumeration did not. It is the one name here that no other test would catch on
  the compiled-declaration route: its type takes no enumeration-class instance.
* `Fintype.ofEquiv` — transports an enumeration along an equivalence, so it inherits the
  size of the source type.
* `Set.toFinset` — enumerates the ambient type in order to filter it.
* `FinEnum.toList` — materialises the list of every element of a `FinEnum`, through
  `List.finRange` and `List.mapTR`. It is needed for the case the class test cannot see:
  `def xs : List Bool := FinEnum.toList Bool` uses an instance the defining module already
  materialised, so the builder filter in `entryPointsOf` drops the instance and this call is
  all that is left.
* `FinEnum.card` and `FinEnum.equiv` — the class's two fields, and **not** pointer reads. The
  compiler inlines the instance (`instance : FinEnum Bool := .ofList [true, false] _`) and
  constant-folds the projection through it, so `def n : Nat := FinEnum.card Bool` emits an
  `_init_` that re-runs `FinEnum.ofList`'s `xs.dedup` (`List.pwFilter`, quadratic) and
  `xs.length` over the element list, and never references the instance symbol at all;
  `FinEnum.equiv` is the same chain with the deduplicated list captured in both closures of
  the equivalence. `Fintype`'s counterpart of this shape is `Fintype.elems`, above.

The list is an occurrence test on the elaborated term, and on its own it is a test of how

the hazard was *spelled*: `instance : Fintype bundle.Y := inferInstanceAs (Fintype (Bytes 16))`
names `Finset.univ` and `Fintype.piFinset` only because `inferInstanceAs` forces an
auxiliary that unfolds the instance. `enumerationClasses` is what makes the clause a class
test. -/
def enumerationEntryPoints : List Name :=
  [`Finset.univ, `Fintype.elems, `Fintype.card, `Fintype.piFinset, `Fintype.ofFinite,
    `Fintype.ofEquiv, `Set.toFinset, `FinEnum.toList, `FinEnum.card, `FinEnum.equiv]

/-- Classes an instance of which can materialise a collection of the type's elements, so
that naming one of their *builders* in a load-time value means the collection is built then.

* `Fintype` qualifies unconditionally: `Fintype.elems : Finset α` is the collection, so
  every instance carries one.
* `FinEnum` qualifies through its constructors rather than its signature. Its fields are
  `card : ℕ` and `equiv : α ≃ Fin card`, which a hand-written instance can fill with a
  numeral and two closures (`instance : FinEnum USize where card := 2 ^ …; equiv := ⟨…⟩`
  materialises nothing) — but every Mathlib instance for a composite type is built by
  `FinEnum.ofList xs h = ofNodupList xs.dedup …`, which takes a **materialised list of every
  element**, deduplicates it, sets `card := xs.length` and captures the list in both
  directions of the equivalence. `FinEnum.prod`, `sum`, `fin`, `Finset.finEnum`,
  `Subtype.finEnum`, `instSigma` and `Quotient.enum` all go through it, and Mathlib's emitted
  C for `FinEnum.prod` calls `toList`, `productTR` and `ofList` in sequence. A `FinEnum` on a
  composite carrier is therefore the same hazard as a `Fintype` on one, and
  `def p : FinEnum (Fin 2 × Fin 2 × Fin 2) := inferInstance` is flagged.
* `Encodable` and `Denumerable` are **out on their instance population, not on their
  fields.** The fields look innocent — `encode : α → ℕ`, `decode : ℕ → Option α`, and
  `Denumerable` adds a proof — but that is the same argument that fails for `FinEnum`, and it
  fails here too: `Encodable.encodableOfList l H = ⟨fun a => idxOf a l, (l[·]?), …⟩`
  (`Mathlib/Logic/Equiv/List.lean:110`) holds the materialised list in both closures, and
  `Fintype.truncEncodable` (`:115`) feeds `Finset.univ.1` into it. What keeps them out is
  what is built from those: `encodableOfList` is a `def` and not an instance,
  `Fintype.toEncodable` (`:123`) is `noncomputable` and deliberately not global, and every
  constructive route to an `Encodable` on a finite carrier names a `Fintype` or `Finset.univ`
  that the value clause already flags. Measured over the load-time population:
  `Encodable.encodableOfList`, `Fintype.truncEncodable` and `Fintype.toEncodable` occur 0
  times each. This is a cost decision about which classes are worth their baseline rows, like
  the one below about size, and not a claim that no `Encodable` instance can hold a
  collection.

The clause closes every respelling of the instance that motivated the gate —
`instance : Fintype bundle.Y := Pi.instFintype`, the `abbrev` route, field-by-field
construction, `Fintype.ofBijective`, a helper that returns the instance, and
`def ok : Bool := decide (∀ x : T, p x)`, which enumerates `T` at load through
`Fintype.decidableForallFintype` — none of which names any of `enumerationEntryPoints`. All
six were constructed and measured; each is flagged by this clause and by nothing else.

Its cost on this tree is nine baseline rows, seven of which the emitted C confirms are
assigned in a module initialiser. -/
def enumerationClasses : List Name := [`Fintype, `FinEnum]

/-- The entry points and classes are written as unchecked name literals because this tool
imports only `Lean` — linking Mathlib into a gate that has to run after every build is not
worth it — so nothing at elaboration time checks that they exist. `checkEntryPoints` does it
instead, against the environment actually swept, and fails the run as an infrastructure
error rather than reporting a clean verdict. The gate therefore fails **closed**: if one of
these is renamed upstream, `--check` goes red until someone re-derives the list, instead
of silently matching nothing. -/
def checkEntryPoints (env : Environment) : Except String Unit := do
  let missing := (enumerationEntryPoints ++ enumerationClasses).filter fun n =>
    (env.find? n).isNone
  if !missing.isEmpty then
    throw s!"entry point(s) not present in the swept environment: {missing} \
      (they were renamed upstream, or the swept roots do not reach Mathlib; \
      re-derive `enumerationEntryPoints` / `enumerationClasses` in scripts/InitSweep.lean)"
  return ()

/-- Whether the backend emits `n`'s own value into its module's initialisation function:
a compiled function declaration with no parameters. `@[extern]` declarations are excluded,
because the emitter calls the foreign symbol and the Lean-side value is dead code. The
exclusion decides nothing on this tree either way: of the 28 `@[extern]` declarations in the
swept libraries, **0** are parameterless, and a parameterless one would not link — the C
backend emits a call to an `_init_` function it never defines for it (constructed and read
off the emitted C).

This over-approximates, deliberately and in the harmless direction. `emitDeclInit` skips a
parameterless declaration whose value is a simple ground expression or a lifted closed
term, laying it out as a static literal instead; both of those caches are non-persistent
environment extensions (`Lean/Compiler/ClosedTermCache.lean:22`,
`Lean/Compiler/LCNF/SimpleGroundExpr.lean:89`), so neither survives the olean import this
tool does and neither can be consulted from here. Measured over the seven swept libraries:
511 constants take this route, 218 of them are assigned from `_init_` in the emitted C, and
the other **293 are every one of them emitted as a static literal** —
`LEAN_EXPORT const lean_object* X = (const lean_object*)&X___closed__N_value;`, checked by
C symbol for all 293, and mostly notation constants. A literal cannot enumerate a type, so
the surplus can only cost a false positive — and it costs exactly two, both in the test
libraries: `SMDTOpenPREFinalValidityTest.instFintypeInput` and
`VCVioTest.PFunctorFacade.instFintypeTriPFunctor` are baseline rows for constants the
emitter proves are never evaluated at load. The LLVM backend has no such exemption at all,
so there the mirror is exact and neither row is a false positive. -/
def isCompiledValue (env : Environment) (n : Name) : Bool :=
  match Lean.IR.findEnvDecl env n with
  | some (.fdecl (xs := xs) ..) => xs.isEmpty
  | some (.extern ..) => false
  | none => false

/-- What loading a module makes `n` cost, and which constant holds the code that runs.
`none` when `n` costs nothing at load time.

`Lean.Compiler.LCNF.emitDeclInit` has exactly three emission sites and this mirrors them in
the emitter's own order: an `initialize do` block is called bare, an `initialize x : T ← e`
is called through its registered initialiser and assigned, and a parameterless declaration
is assigned from its `_init_` function. `initialize x : T ← e` stores `e` in a separate
constant and leaves `x` itself valueless, which is why the source of the value is reported
separately from the declaration that carries it — reading `x` alone would accept every
`initialize` in the repository without looking at anything. -/
def loadTimeSource (env : Environment) (n : Name) : Option (String × Name) :=
  if Lean.isIOUnitInitFn env n then
    some ("initialize", n)
  else if let some initFn := Lean.getInitFnNameFor? env n then
    some ("initialize", initFn)
  else if isCompiledValue env n then
    some ("value", n)
  else
    none

/-- Whether `n`'s type, after stripping `∀`s, is an application of one of
`enumerationClasses` — i.e. whether `n` *is* an enumeration of a type, or a function that
builds one. -/
def namesEnumerationClass (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some ci =>
    match ci.type.getForallBody.getAppFn with
    | .const c _ => enumerationClasses.contains c
    | _ => false
  | none => false

/-- The evidence that the value of `n` builds an enumeration: the `enumerationEntryPoints`
it names, in list order, followed by the constants it names whose type is an application of
an `enumerationClasses` member *and* which are not themselves parameterless compiled values,
sorted so the report and the baseline are deterministic.

The second half of that condition is what separates building an enumeration from mentioning
one. `Pi.instFintype`, `Fin.fintype`, `Fintype.mk` and `Fintype.ofBijective` all take
arguments, so naming one means this value applies it and pays for the result. `Bool.fintype`
takes none: its enumeration was built by the module initialiser of the module that defines
it, whoever mentions it afterwards, so a value that names it copies a pointer. Measured, that
distinction removes three baseline rows that only ever read `lp_mathlib_Bool_fintype` and
allocate a closure. It costs nothing in reach: a parameterless enumeration inside a swept
library is itself in the load-time population and is flagged on its own account; one inside
Mathlib is paid for when Mathlib's module is loaded and is outside what this gate governs.
`#[]` if it names none or has no readable value. An `opaque` declaration is read like a
`def`: `opaque x : T := v` hides `v` from unification and not from the backend, which
compiles `v` and assigns it in the module initialiser like any other parameterless value
(checked in the emitted C). -/
def entryPointsOf (env : Environment) (n : Name) : Array String := Id.run do
  let some ci := env.find? n | return #[]
  let some value := ci.value? (allowOpaque := true) | return #[]
  let used := value.getUsedConstants
  let mut hits : Array String := #[]
  for e in enumerationEntryPoints do
    if used.contains e then hits := hits.push e.toString
  let classHits := (used.filter (fun u => namesEnumerationClass env u && !isCompiledValue env u))
    |>.map (·.toString) |>.qsort (· < ·)
  for c in classHits do
    if !hits.contains c then hits := hits.push c
  return hits

/-- Whether `n` is a closed term the compiler lifted out of a declaration's body.
`Lean.Compiler.LCNF.ExtractClosed` names every one of them `<parent>._closed_<n>` and
registers it in `closedTermCacheExt`, and `emitDeclInit` skips exactly the names in that
cache — so the name is the emitter's own exemption, recovered without the cache, which does
not survive an olean import. Checked on this tree: of the 496 `_init_` assignments emitted
for the 634 swept modules, **0** is a lifted closed term (218 are environment constants and
278 are boxed numeric constants). -/
def isLiftedClosedTerm (n : Name) : Bool :=
  match n.eraseMacroScopes with
  | .str _ s => s.startsWith "_closed_"
  | _ => false

/-- The functions a compiler-generated name was specialised from. The specialiser writes
`<specialised>._at_.<caller>.spec_<n>`, nesting as it goes, so cutting the name at its `_at_`
components gives one segment per function in the chain, each with that function at its head.

Two details, both measured rather than assumed. The cut is structural rather than textual —
`n.toString.splitOn "._at_."` and `String.toName` agree with it on all 1473 declarations this
is applied to today, so that is not a correctness argument; it is kept because it does not
depend on `toString` printing what `toName` can parse back, which fails on macro-scoped names
(15 of the 538 load-time *constants* are macro-scoped and do not survive the round trip;
none of this population is, because all 507 macro-scoped compiled declarations here are
lifted closed terms and therefore excluded). And the concatenation is `Name.appendCore`
rather than `++`: `Name.append` is macro-scope-aware, so on a name carrying `_hyg` it drops
the hygiene marker and panics through `extractMacroScopes` while the tool still exits `0`
(constructed and reproduced). These are compiler-generated names being taken apart, not
hygienic names being re-scoped. -/
def specialisationSegments (n : Name) : Array Name := Id.run do
  let mut segments : Array Name := #[]
  let mut current : Name := .anonymous
  for c in n.components do
    if c == `_at_ then
      segments := segments.push current
      current := .anonymous
    else
      current := current.appendCore c
  return segments.push current

/-- Whether the telescope of `e` binds an argument whose type is an application of an
`enumerationClasses` member. -/
partial def bindsEnumerationClass : Expr → Bool
  | .forallE _ t b _ =>
    (match t.getAppFn with
      | .const c _ => enumerationClasses.contains c
      | _ => false) || bindsEnumerationClass b
  | _ => false

/-- Whether `n` *takes* an enumeration-class instance, so that applying it materialises that
instance's collection. This is the test that survives specialisation: the specialiser records
the function chain in the mangled name and specialises the instance away, so what a compiled
declaration returns says little, while what the function it came from consumes is a signal
that survives. It is a sufficient condition and not a complete one — an enumeration can enter
a specialised function through a **closure** instead, and then no segment consumes a class at
all; see the `@[specialize]` bullet in the known limits.

`Fintype.card`, `Fintype.piFinset`, `FinEnum.toList` and a user's `count (α) [Fintype α]` all
take one; `useFinset (s : Finset α)` does not, because its caller built the enumeration and
the caller is tested on its own account. -/
def takesEnumerationClassArg (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some ci => bindsEnumerationClass ci.type
  | none => false

/-- The evidence that a compiler-generated 0-arity declaration builds an enumeration: the
`enumerationEntryPoints` its mangled name was specialised from, any segment that is itself a
constant of an `enumerationClasses` type, and any segment that *takes* an enumeration-class
instance. There is no value to read — these declarations are not in the environment at all —
so the name is all there is, which is why this clause is an addition to the value test and
not a replacement for it.

The argument test is the one with reach, and on this route it is the only one whose reach can
be demonstrated. Of the ten entry points, nine also take an enumeration-class instance, so on
a segment the list finds nothing the argument test would not; the tenth, `Fintype.ofFinite`,
is `noncomputable` and has no compiled code, so it can never *be* a segment. The result test
covers a segment that builds an instance without consuming one (`FinEnum.ofList`,
`Fin.fintype`), which is a shape this compiler did not produce in any specialisation I could
construct — a `FinEnum.ofList` call, a wrapper around it, and a `@[specialize]` wrapper all
fold into lifted closed terms instead. Both are kept because they are sound and free, not
because a fixture pins them: `scripts/test-initsweep.sh`'s three compiled-declaration
witnesses pin the argument test only, which was measured by deleting each test in turn and
re-running the matrix (deleting either of the other two leaves the five offenders and their
evidence arrays byte-identical). The entry-point list and the builder test *are* pinned on the
value route, by the `Plain` / `Opaque` / `Initialize` fixtures and by `Named` respectively —
also measured by mutation.

Measured over this tree: 0 of the 1473 compiled declarations of the seven default roots and 0
of the 1 in the test libraries carry evidence of any kind, so all three tests ship at no
baseline cost. -/
def irDeclEvidence (env : Environment) (n : Name) : Array String := Id.run do
  let segments := specialisationSegments n
  let mut hits : Array String := #[]
  for e in enumerationEntryPoints do
    if segments.any (e.isPrefixOf ·) then hits := hits.push e.toString
  for seg in segments do
    if (namesEnumerationClass env seg || takesEnumerationClassArg env seg)
        && !hits.contains seg.toString then
      hits := hits.push seg.toString
  return hits

/-- One constant the module initialiser evaluates. `library` is the swept root the
constant's module sits under, which is the scope a baseline row carries. `via` is `value`
when the declaration is itself the parameterless value the initialiser assigns,
`initialize` when the code that runs is an initialiser body registered for it, and
`ir-only` when the declaration is compiler-generated and has no environment constant at
all; `source` is the constant whose value was read; `entryPoints` is empty for everything
the gate accepts without a baseline row. -/
structure Entry where
  name : String
  module : String
  library : String
  via : String
  source : String
  entryPoints : Array String
  deriving ToJson

/-- What one sweep of the environment found. `loadTime` is the whole population the
entry-point test narrows: every constant whose module initialiser evaluates something. It
is reported in full under `--out` and deliberately not gated on. -/
structure Census where
  constants : Nat
  modules : Nat
  /-- Load-time constants whose value the sweep could not read, and which the name test
  therefore accepted without looking at anything. This is the gate's own blind spot; it is
  reported on every run so it cannot grow unnoticed. `definition`s, `theorem`s and `opaque`
  declarations all have a readable value, so what is left here is the kernel's valueless
  kinds — an axiom, or a constructor or recursor — reaching a parameterless compiled
  declaration. None does today. -/
  opaqueValues : Nat
  loadTime : Array Entry
  /-- Compiler-generated parameterless declarations that are not environment constants:
  specialisations, boxed numeric constants and their like, which the backend assigns in the
  module initialiser exactly as it assigns a constant's own value — unless the same
  closed-term and ground-expression exemptions apply, so this over-approximates in the same
  harmless direction as `isCompiledValue` does. Measured over the seven default roots: 1473
  such declarations, of which the emitted C assigns **278**, and every one of those 278 is in
  this population (checked by C symbol, both directions). The environment sweep cannot name
  any of them — that is what made them a blind spot before they were counted here and tested
  by name. -/
  irLoadTime : Nat
  /-- Those of `irLoadTime` whose mangled name carries an enumeration entry point, a
  constant of an enumeration-class type, or a function that takes an enumeration-class
  instance. -/
  irOffenders : Array Entry

/-- The load-time constants whose value builds an enumeration of a type, and the
compiler-generated declarations whose name says they do. -/
def Census.offenders (c : Census) : Array Entry :=
  c.loadTime.filter (!·.entryPoints.isEmpty) ++ c.irOffenders

/-- Enumerate every constant of every module under one of `roots` and apply the predicate.
A constant realised on demand can appear in several modules' `constNames`; it is counted
once, under the first module that carries it. -/
def census (roots : Array Name) : CoreM Census := do
  let env ← getEnv
  let mut seen : Std.HashSet Name := {}
  let mut constants := 0
  let mut modules := 0
  let mut opaqueValues := 0
  let mut loadTime : Array Entry := #[]
  let mut irLoadTime := 0
  let mut irOffenders : Array Entry := #[]
  for i in [0:env.header.moduleNames.size] do
    let mname := env.header.moduleNames[i]!
    let mdata := env.header.moduleData[i]!
    -- A module is attributed to the root it was swept under, not to its own first
    -- component, so `--root Foo.Bar` and the baseline agree on one key.
    if let some root := roots.find? (·.isPrefixOf mname) then
      modules := modules + 1
      -- The compiler-generated half of the module's initialisation work, which has no
      -- environment constant to read: parameterless IR declarations the backend assigns
      -- from `_init_` exactly as it assigns a constant's own value.
      for d in Lean.IR.declMapExt.getModuleIREntries env i do
        if let .fdecl (f := f) (xs := xs) .. := d then
          if xs.isEmpty && (env.find? f).isNone && !isLiftedClosedTerm f then
            irLoadTime := irLoadTime + 1
            let hits := irDeclEvidence env f
            if !hits.isEmpty then
              irOffenders := irOffenders.push {
                name := f.toString
                module := mname.toString
                library := root.toString
                via := "ir-only"
                source := f.toString
                entryPoints := hits }
      for c in mdata.constNames do
        if seen.contains c then continue
        seen := seen.insert c
        constants := constants + 1
        let some (via, source) := loadTimeSource env c | continue
        if ((env.find? source).bind (·.value? (allowOpaque := true))).isNone then
          opaqueValues := opaqueValues + 1
        loadTime := loadTime.push {
          name := c.toString
          module := mname.toString
          library := root.toString
          via := via
          source := source.toString
          entryPoints := entryPointsOf env source }
  return { constants, modules, opaqueValues, irLoadTime,
           loadTime := loadTime.qsort (fun a b => a.name < b.name),
           irOffenders := irOffenders.qsort (fun a b => a.name < b.name) }

/-- One accepted constant: a name, the library it was swept under, and the entry points it
is accepted for. Accepting a constant is not accepting its library — every other constant of
`library` stays at zero — and it is not accepting more than what was reviewed: a row covers
exactly the entry points it lists, so the same constant gaining a new one is a regression. -/
structure Accepted where
  name : String
  library : String
  entryPoints : Array String
  deriving FromJson, ToJson, Inhabited

/-- The committed baseline: the constants whose load-time enumeration has been reviewed and
accepted, in the shape of `scripts/axiom_baseline.json`. -/
structure Baseline where
  accepted : Array Accepted
  deriving FromJson, ToJson

/-- Project the current census into baseline form, deterministically sorted. -/
def currentBaseline (offenders : Array Entry) : Baseline where
  accepted := (offenders.map fun e =>
    { name := e.name, library := e.library, entryPoints := e.entryPoints }).qsort
      (fun a b => a.name < b.name)

/-- Read and parse a baseline file. `none` means the file does not exist. -/
def readBaseline (basePath : String) : IO (Except String (Option Baseline)) := do
  if !(← System.FilePath.pathExists basePath) then
    return .ok none
  match Json.parse (← IO.FS.readFile basePath) >>= fromJson? (α := Baseline) with
  | .ok b => return .ok (some b)
  | .error e => return .error e

/-- Compare the current census against the committed baseline. Returns the exit code: `1`
iff some flagged constant is not covered by a row of the baseline — either because it is not
named there, or because it names an entry point the row does not list. A constant the
baseline does not mention is not accepted, so a hazard cannot be greened by deleting a row.
Rows scoped to a library outside `roots` are left alone: they belong to a sweep this run did
not perform. -/
def runCheck (cur : Census) (roots : Array Name) (basePath : String) : IO UInt32 := do
  let base ← match ← readBaseline basePath with
    | .error e =>
      IO.eprintln s!"initsweep: cannot parse baseline {basePath}: {e}"
      return 2
    | .ok none =>
      IO.eprintln s!"initsweep: baseline {basePath} not found; \
        create it with `lake exe initsweep --update-baseline`"
      return 2
    | .ok (some b) => pure b
  let inScope (lib : String) : Bool := roots.any (·.toString == lib)
  let offenders := cur.offenders
  let uncovered := offenders.filter fun o =>
    match base.accepted.find? (fun a => a.name == o.name && a.library == o.library) with
    | none => true
    | some a => o.entryPoints.any (!a.entryPoints.contains ·)
  if !uncovered.isEmpty then
    IO.eprintln s!"initsweep: {uncovered.size} constant(s) build an enumeration of a type \
      when their module is loaded and are not accepted in {basePath}:"
    for o in uncovered do
      IO.eprintln s!"  {o.name}  ({o.module})  via {o.via} {o.source}  \
        names {o.entryPoints}"
    IO.eprintln "initsweep: a top-level constant of non-function type is evaluated when its \
      module is loaded, before any `main` runs. Route the finiteness argument through \
      `Fintype.ofFinite`: its `Prop`-valued `Finite` argument leaves no compiled code at \
      all, which is the only fix here that removes the work rather than moving it."
    IO.eprintln s!"initsweep: `noncomputable` is not a fix — it removes the instance's own \
      code and leaves the compiled auxiliary that carries the work. Adding a parameter is \
      not reliably a fix either: the compiler can lift a parameterless specialisation out \
      of a function whose result is a ground value, and that specialisation is initialised \
      at load like any other value — `def cardY (_u : Unit) : Nat := Fintype.card T` emits \
      one. Check the emitted C under `.lake/build/ir/` if you take that route."
    IO.eprintln s!"initsweep: if the enumeration is genuinely small, record it with \
      `lake exe initsweep --update-baseline` and argue the row — one constant, not one \
      library — in review."
    return 1
  let stale := base.accepted.filter fun a =>
    inScope a.library &&
      (match offenders.find? (fun o => o.name == a.name && o.library == a.library) with
        | none => true
        | some o => a.entryPoints.any (!o.entryPoints.contains ·))
  if !stale.isEmpty then
    IO.println s!"initsweep: good news — {stale.size} baseline entr(y/ies) no longer build \
      what they were accepted for; run `lake exe initsweep --update-baseline` to shrink the \
      baseline:"
    for a in stale do IO.println s!"  {a.name}"
  IO.println s!"initsweep: check passed ({offenders.size} flagged, all accepted in \
    {basePath})."
  return 0

/-- Rewrite the baseline from the current build. Rows scoped to a library this run did not
sweep are preserved verbatim, so `--update-baseline` with a partial `--root` set cannot
silently drop another library's accepted constants; refusing rather than guessing is why an
unparsable existing file is an error here. Adding a row is the escape hatch, and the diff is
one constant per line, to be argued in review. -/
def runUpdate (cur : Census) (roots : Array Name) (basePath : String) : IO UInt32 := do
  let preserved ← match ← readBaseline basePath with
    | .error e =>
      IO.eprintln s!"initsweep: cannot parse baseline {basePath}: {e}"
      IO.eprintln "initsweep: refusing to overwrite it — rows for libraries outside this \
        run's roots would be lost."
      return 2
    | .ok none => pure #[]
    | .ok (some b) => pure (b.accepted.filter fun a => !roots.any (·.toString == a.library))
  let rows := (preserved ++ (currentBaseline cur.offenders).accepted).qsort
    (fun a b => a.name < b.name)
  IO.FS.writeFile basePath ((toJson ({ accepted := rows } : Baseline)).pretty ++ "\n")
  IO.println s!"initsweep: wrote baseline to {basePath} \
    ({rows.size} accepted constant(s), {preserved.size} preserved from libraries not swept)"
  return 0

structure Config where
  roots : Array Name := #[]
  out? : Option String := none
  check : Bool := false
  update : Bool := false
  baseline : String := "scripts/init_sweep_baseline.json"

def parseArgs : List String → Config → Except String Config
  | [], cfg => .ok cfg
  | "--check" :: rest, cfg => parseArgs rest { cfg with check := true }
  | "--update-baseline" :: rest, cfg => parseArgs rest { cfg with update := true }
  | "--out" :: path :: rest, cfg => parseArgs rest { cfg with out? := some path }
  | "--baseline" :: path :: rest, cfg => parseArgs rest { cfg with baseline := path }
  | "--root" :: mod :: rest, cfg =>
    parseArgs rest { cfg with roots := cfg.roots.push mod.toName }
  | arg :: _, _ => .error s!"initsweep: unknown or incomplete argument: {arg}\n\
      usage: lake exe initsweep [--out FILE] [--check] [--update-baseline] \
      [--baseline FILE] [--root MOD]*\n      (--check and --update-baseline are mutually exclusive)"

end InitSweep

open InitSweep in
/-- Tool body. Exit codes are a contract with CI, which reads `1` as a ratchet verdict and
anything else as an infrastructure failure; `main` wraps this so an uncaught exception
cannot masquerade as the former. -/
unsafe def run (args : List String) : IO UInt32 := do
  let cfg ← match parseArgs args {} with
    | .ok cfg => pure cfg
    | .error e => IO.eprintln e; return 2
  if cfg.check && cfg.update then
    IO.eprintln "initsweep: --check and --update-baseline are mutually exclusive"
    return 2
  let roots := if cfg.roots.isEmpty then defaultRoots else cfg.roots
  initSearchPath (← findSysroot)
  let env ← try
      importModules (roots.map ({ module := · })) {} (trustLevel := 1024)
        (loadExts := false)
    catch e =>
      IO.eprintln s!"initsweep: cannot import root modules {roots}: {e.toString}"
      IO.eprintln "initsweep: roots are module names built by `lake build`, not library \
        names — a `submodules` glob with no umbrella module has no importable library name \
        — and two roots that each define `main` cannot be imported into one environment."
      return (2 : UInt32)
  match checkEntryPoints env with
    | .ok _ => pure ()
    | .error e => IO.eprintln s!"initsweep: {e}"; return (2 : UInt32)
  let (cur, _) ← (census roots).toIO { fileName := "<initsweep>", fileMap := default } { env }
  IO.println s!"initsweep: {cur.constants} constants across {cur.modules} modules \
    under {roots}"
  IO.println s!"  evaluated when their module is loaded: {cur.loadTime.size}"
  IO.println s!"  of those, with no readable value (blind spot): {cur.opaqueValues}"
  IO.println s!"  compiler-generated declarations beside them, initialised or laid out as \
    literals: {cur.irLoadTime}"
  IO.println s!"  building an enumeration of a type: {cur.offenders.size}"
  if let some out := cfg.out? then
    let report := Json.mkObj [
      ("roots", toJson (roots.map (·.toString))),
      ("constantCount", toJson cur.constants),
      ("loadTimeCount", toJson cur.loadTime.size),
      ("opaqueValueCount", toJson cur.opaqueValues),
      ("irLoadTimeCount", toJson cur.irLoadTime),
      ("irOffenders", toJson cur.irOffenders),
      ("loadTime", toJson cur.loadTime)]
    IO.FS.writeFile out (report.pretty ++ "\n")
    IO.println s!"initsweep: wrote report to {out}"
  if cfg.update then
    return (← runUpdate cur roots cfg.baseline)
  if cfg.check then
    return (← runCheck cur roots cfg.baseline)
  return 0

open InitSweep in
unsafe def main (args : List String) : IO UInt32 := do
  try
    run args
  catch e =>
    IO.eprintln s!"initsweep: internal error: {e}"
    return 2
