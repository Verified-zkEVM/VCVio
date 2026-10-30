/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import PolyFun.IPFunctor.Free.Indexed
public import PolyFun.IPFunctor.Free.Bound
public import VCVio.Quantum.Comp.LocalSig
public import QuantumFoundations.SubInstrument

/-!
# Quantum oracle programs

This file defines the syntax of quantum algorithms that query oracles. A program holds a finite
quantum register, applies local operations to it, and calls oracles on part of it. Measurement
outcomes and oracle results are classical, and select what the program does next. Amplitudes live
in the state of the register, not in the branching of the program.

## Commands

A program is a tree of two kinds of command.

* `prim o`: a local operation `o : L.Op A` on the current register `A`, named by a *primitive
  signature* `L` (`Quantum.LocalSig`). It reports an outcome `b`, and the program continues on the
  register `L.next o b`, which may depend on `b`: a measurement may keep a qubit on one outcome and
  discard it on another.
* `query i E ℓ`: a call of port `i` of an *oracle signature* `spec` (`Quantum.QuantumOracleSpec`).
  The port takes the register `In i`, leaves `Out i` and reports a classical result in
  `Result i`. The equivalence `ℓ : A ≃ In i × E` exposes `In i` as a tensor factor of the current
  register; the rest `E` is carried through the call untouched, even when it is entangled with
  `In i`, and the register afterwards is `Out i × E`.

A program says neither what its local operations do nor how the oracle answers. An
interpretation of `L` (`Quantum.LocalSig.Interp`) gives each operation a dependent subinstrument,
and a runtime (`Quantum.QuantumRuntime`) answers the calls; `Quantum.QuantumRuntime.run`, in
`VCVio.Quantum.Comp.Runtime`, combines them.

## Which program type to use

* `Quantum.QuantumComp L spec X A` is the general program. Its leaves `x : X u` each sit on their
  own final register `u`, so different branches may end on different registers.
* `Quantum.QuantumComp₂ L spec A B α` is the case in which every branch ends on `B` and returns a
  value in `α`. Intermediate registers may still depend on outcomes. It is a lawful monad when
  `A = B`, and a lawful indexed monad in general.
* `Quantum.QComp spec A B α` is `QuantumComp₂` over the signature of all instruments
  (`Quantum.LocalSig.instruments`), in which a local step is any subinstrument
  (`Quantum.QComp.act`). Use it to build programs from arbitrary quantum operations, and a named
  signature to reason about a specific gate set.

Fixed-slot strategies (`Quantum.QuantumComb`) embed as straight-line programs
(`Quantum.QuantumComb.toComp`, in `VCVio.Quantum.Oracle.Comb`). Query budgets are properties of
the tree (`Quantum.QuantumComp.IsQueryBound`), not type indices.

## What the model covers

* **Adaptive.** Every continuation sees all classical outcomes so far, so the number of calls,
  their ports and their order, the registers allocated, and the point at which the program stops
  may all depend on them.
* **Multi-port.** A signature has any type of ports, each with its own registers and result type.
* **Stateful oracles.** A runtime has a private register that persists across calls; the program
  has no command on it.
* **Gate sets.** Local operations are named by a signature and interpreted separately, so the
  tree records the number and cost of named local operations
  (`Quantum.QuantumComp.IsCostBound`). Basis equivalences at calls and classical continuation
  computation are uncharged.

## What it does not cover

* **Coherent choice of port.** The port of a call is classical. A call whose port is selected by a
  quantum register needs a single port acting on `ι × X × Y`, implemented by its own runtime; the
  runtimes of the separate ports do not determine it.
* **Loops.** Program trees are well founded: every path is finite, although path lengths need not
  be bounded when an operation has infinitely many outcomes. A loop that terminates only with
  probability one has an infinite path, and needs a coinductive tree and execution as a limit.
* **Infinite dimension.** Registers are finite-dimensional. Outcome and result types may be
  infinite, but only countably many outcomes of an operation have nonzero weight, so measurements
  with continuous outcomes are not modelled.

## Implementation: PolyFun's free indexed monad

`QuantumComp L spec X A` is PolyFun's `IPFunctor.IFreeM`, the free monad in McBride's indexed
style, on the commands `prim` and `query`. Sequencing (`Quantum.QuantumComp.bind`) replaces each
leaf `x : X u` by a continuation that starts on the same register `u`. `QuantumComp₂` is PolyFun's
`IPFunctor.FreeM₂`. PolyFun supplies only the trees; the quantum meaning comes from the
interpretation and the runtime. The command equations, induction principle
(`Quantum.QuantumComp.inductionOn`) and sequencing laws here let clients work without PolyFun's
internals.

## Universes

Every type a user supplies may lie in any universe. For `L : Quantum.LocalSig.{u, v}` (operations
in `Type u`, outcomes in `Type v`), `spec : Quantum.QuantumOracleSpec.{u₁, v₁}` (ports in
`Type u₁`, results in `Type v₁`) and `X : QReg → Type w`, the program type lies in
`Type (max u v u₁ v₁ (w + 1))`, and `bind` may change the universe of the leaves.

Registers (`Quantum.QReg`) are finite types with carriers in `Type`. This loses nothing, since
every finite type is equivalent to some `Fin n`, and puts `QReg` in `Type 1`. PolyFun's indexed
functors have one universe of responses, so `Quantum.QuantumComp.Cmd.Resp` lifts outcomes and
results to `Type (max v v₁)` with `ULift`, and `Quantum.QuantumComp.onDown` adapts continuations.
That is the only lift: `primBind`, `queryBind`, `prim`, `query`, execution and every statement
about them take unlifted outcomes and results.

`QuantumComp₂` keeps all these universes independent. The alias `QComp spec A B α` with
`α : Type w` uses instruments with outcomes in the same `Type w`
(`Quantum.LocalSig.instruments.{w}`); write `QuantumComp₂ LocalSig.instruments.{v} spec A B α` to
separate them.

## Main definitions

* `Quantum.QuantumOracleSpec`, with the commands `Quantum.QuantumComp.Cmd L spec` and the indexed
  polynomial functor `Quantum.QuantumComp.toIPFunctor L spec`.
* `Quantum.QuantumComp L spec X A`, with `pure`, `bind`, the commands followed by continuations
  `primBind` and `queryBind`, the generic commands `prim` and `query`, and the induction principle
  `Quantum.QuantumComp.inductionOn`.
* `Quantum.QuantumComp₂ L spec A B α`, with its `Monad`, `LawfulMonad`, `IndexedMonad` and
  `LawfulIndexedMonad` instances.
* `Quantum.QComp spec A B α`, with `Quantum.QComp.act`.
* `Quantum.QuantumComp.Lossless I x`: every local operation on every path is interpreted by a
  lossless dependent subinstrument.
-/

public section

open IPFunctor

universe u v u₁ v₁ w w₁ w₂

namespace Quantum

/-- The interface of quantum oracle calls: a type of ports, each with an input register
`In i`, an output register `Out i`, and a classical result type `Result i`.

A runtime implements port `i` by a subinstrument on the input and its private memory.
`Result i = Unit` means that the call reports no classical information. Unitary oracle
calls have this form, as do channels that measure internally and discard the report;
the result type alone does not assert coherence or losslessness.

A call may act on a superposition within one port's input register. The choice of port is
classical. The signature specifies types only, and ports and results have independent
universes. See `QuantumRuntime` for the physical implementation. -/
structure QuantumOracleSpec where
  /-- The oracle ports. -/
  Port : Type u₁
  /-- The register a call of the port acts on. -/
  In : Port → QReg
  /-- The register a call of the port leaves in place of its input register. -/
  Out : Port → QReg
  /-- The classical result of a call of the port. -/
  Result : Port → Type v₁

namespace QuantumComp

/-- The commands available to a program over the primitive signature `L` and the oracle
signature `spec` whose current register is `A`. -/
inductive Cmd (L : LocalSig.{u, v}) (spec : QuantumOracleSpec.{u₁, v₁}) (A : QReg) :
    Type (max 1 u u₁)
  /-- A local operation on the program's register. -/
  | prim (o : L.Op A)
  /-- A call of port `i`; `ℓ` splits the current register into the port's input register and a
  remainder `E` that the call leaves alone. -/
  | query (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)

variable {L : LocalSig.{u, v}} {spec : QuantumOracleSpec.{u₁, v₁}}

/-- The classical response of a command: the outcome of a local operation, or the result of a
call, lifted to their common universe `Type (max v v₁)`. This is the only place where outcomes and
results are lifted: `Quantum.QuantumComp.primBind` and `Quantum.QuantumComp.queryBind` take
continuations on the unlifted types. -/
@[expose]
def Cmd.Resp {A : QReg} : Cmd L spec A → Type (max v v₁)
  | .prim o => ULift.{v₁} (L.Outcome o)
  | .query i _ _ => ULift.{v} (spec.Result i)

/-- The register after a command, given its response. -/
@[expose]
def Cmd.next {A : QReg} : (c : Cmd L spec A) → c.Resp → QReg
  | .prim o, b => L.next o b.down
  | .query i E _, _ => QReg.of (spec.Out i × E)

/-- A continuation on a type, read as a continuation on its lift: `fun b ↦ k b.down`. The
continuations of `Quantum.QuantumComp.primBind` and `Quantum.QuantumComp.queryBind` take
unlifted outcomes and results, and this is how they meet the lifted responses of
`Quantum.QuantumComp.Cmd.Resp`. It is a regular definition rather than a lambda, so that
unifying two such continuations compares the continuations themselves. -/
@[expose]
def onDown {α : Type v} {β : α → Sort w} (k : (a : α) → β a) : (b : ULift.{v₁} α) → β b.down :=
  fun b ↦ k b.down

variable (L spec) in
/-- The commands as an indexed polynomial endofunctor on registers. Its index universe is that of
`Quantum.QReg`, its commands lie in `Type (max 1 u u₁)` and its responses in `Type (max v v₁)`. -/
@[expose]
def toIPFunctor : IPFunctor.Endo.{1, max 1 u u₁, max v v₁} QReg where
  A := Cmd L spec
  B _ c := c.Resp
  src _ c b := c.next b

end QuantumComp

/-- A quantum oracle program starting on the register `A`. Each node either applies a local
operation named by `L` or calls a port of `spec`; its classical outcome or result selects the next
subtree, and the register that subtree starts on. A leaf `x : X u` returns classical data on the
final register `u`, which may depend on earlier outcomes.

The tree contains commands, not states: `QuantumRuntime.run` gives it meaning from an
interpretation of `L` and a runtime for `spec`. Every path is finite, but path lengths need not be
bounded. Formally this is PolyFun's free indexed monad `IFreeM`. Use `QuantumComp₂` when every
branch ends on the same register, and `QComp` to supply local operations directly as
subinstruments. -/
@[expose]
def QuantumComp (L : LocalSig.{u, v}) (spec : QuantumOracleSpec.{u₁, v₁}) (X : QReg → Type w)
    (A : QReg) : Type (max u v u₁ v₁ (w + 1)) :=
  IFreeM (QuantumComp.toIPFunctor L spec) X A

namespace QuantumComp

variable {L : LocalSig.{u, v}} {spec : QuantumOracleSpec.{u₁, v₁}} {X : QReg → Type w}
  {Y : QReg → Type w₁} {Z : QReg → Type w₂} {A : QReg}

/-! ## Commands and sequencing -/

/-- The program that stops at once with the leaf `x` on its starting register. -/
@[expose]
protected def pure (x : X A) : QuantumComp L spec X A :=
  IFreeM.pure x

/-- The local operation `o`, followed by the continuation selected by its outcome. -/
@[expose]
def primBind (o : L.Op A) (k : (b : L.Outcome o) → QuantumComp L spec X (L.next o b)) :
    QuantumComp L spec X A :=
  IFreeM.liftBind (P := toIPFunctor L spec) (.prim o) (onDown k)

/-- A call of port `i` on the factor of the register that `ℓ` exposes, followed by the
continuation selected by its result. -/
@[expose]
def queryBind (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)
    (k : spec.Result i → QuantumComp L spec X (QReg.of (spec.Out i × E))) :
    QuantumComp L spec X A :=
  IFreeM.liftBind (P := toIPFunctor L spec) (.query i E ℓ) (onDown k)

/-- **Sequencing.** Run `x`, and at each leaf `y : X u` continue with `k u y` from the register
`u` on which the leaf sits. The leaf families of `x` and `k` may lie in different universes. -/
@[expose]
protected def bind (x : QuantumComp L spec X A) (k : ∀ u, X u → QuantumComp L spec Y u) :
    QuantumComp L spec Y A :=
  IFreeM.bind x k

/-- Sequencing is PolyFun's `IPFunctor.IFreeM.bind`, also across leaf universes. -/
theorem bind_eq_iFreeM_bind (x : QuantumComp L spec X A)
    (k : ∀ u, X u → QuantumComp L spec Y u) : x.bind k = IFreeM.bind x k :=
  rfl

/-- The local operation `o`, stopping with its outcome on the register it leaves. -/
@[expose]
def prim (o : L.Op A) : QuantumComp L spec (L.OutcomeAt o) A :=
  primBind o fun b ↦ QuantumComp.pure ⟨b, rfl⟩

/-- A call of port `i`, stopping with its result on the register `Out i × E`. -/
@[expose]
def query (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E) :
    QuantumComp L spec (fun u ↦ PSigma fun _ : u = QReg.of (spec.Out i × E) ↦ spec.Result i) A :=
  queryBind i E ℓ fun r ↦ QuantumComp.pure ⟨rfl, r⟩

/-- Left unit law. -/
@[simp]
protected theorem pure_bind (x : X A) (k : ∀ u, X u → QuantumComp L spec Y u) :
    (QuantumComp.pure x).bind k = k A x :=
  rfl

/-- Sequencing after a local operation sequences each continuation. -/
@[simp]
theorem primBind_bind (o : L.Op A) (k : (b : L.Outcome o) → QuantumComp L spec X (L.next o b))
    (g : ∀ u, X u → QuantumComp L spec Y u) :
    (primBind o k).bind g = primBind o fun b ↦ (k b).bind g :=
  rfl

/-- Sequencing after a call sequences each continuation. -/
@[simp]
theorem queryBind_bind (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)
    (k : spec.Result i → QuantumComp L spec X (QReg.of (spec.Out i × E)))
    (g : ∀ u, X u → QuantumComp L spec Y u) :
    (queryBind i E ℓ k).bind g = queryBind i E ℓ fun r ↦ (k r).bind g :=
  rfl

/-- A local operation followed by a continuation is the command with that continuation. -/
theorem prim_bind (o : L.Op A) (k : ∀ u, L.OutcomeAt o u → QuantumComp L spec Y u) :
    (prim o).bind k = primBind o fun b ↦ k _ ⟨b, rfl⟩ :=
  rfl

/-- A call followed by a continuation is the command with that continuation. -/
theorem query_bind (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)
    (k : ∀ u, (PSigma fun _ : u = QReg.of (spec.Out i × E) ↦ spec.Result i) →
      QuantumComp L spec Y u) :
    (query i E ℓ).bind k = queryBind i E ℓ fun r ↦ k _ ⟨rfl, r⟩ :=
  rfl

/-! ## Induction -/

/-- Induction on programs: a property of every program follows from the property of every leaf,
and its preservation by prefixing a local operation or a call to a family of programs. -/
@[elab_as_elim]
protected theorem inductionOn {motive : ∀ A : QReg, QuantumComp L spec X A → Prop}
    (pure : ∀ (A : QReg) (x : X A), motive A (QuantumComp.pure x))
    (primBind : ∀ (A : QReg) (o : L.Op A)
      (k : (b : L.Outcome o) → QuantumComp L spec X (L.next o b)), (∀ b, motive _ (k b)) →
        motive A (primBind o k))
    (queryBind : ∀ (A : QReg) (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)
      (k : spec.Result i → QuantumComp L spec X (QReg.of (spec.Out i × E))),
      (∀ r, motive _ (k r)) → motive A (queryBind i E ℓ k))
    {A : QReg} (x : QuantumComp L spec X A) : motive A x :=
  IFreeM.inductionOn (P := toIPFunctor L spec) (C := motive) pure
    (fun s c r ih ↦ by
      cases c with
      | prim o => exact primBind s o (fun b ↦ r (ULift.up b)) fun b ↦ ih (ULift.up b)
      | query i E ℓ => exact queryBind s i E ℓ (fun b ↦ r (ULift.up b)) fun b ↦ ih (ULift.up b))
    x

/-! ## Monad laws -/

/-- Right unit law. -/
@[simp]
protected theorem bind_pure (x : QuantumComp L spec X A) :
    x.bind (fun _ y ↦ QuantumComp.pure y) = x :=
  IFreeM.bind_pure_right x

/-- Sequencing of programs is associative. -/
protected theorem bind_assoc (x : QuantumComp L spec X A) (k : ∀ u, X u → QuantumComp L spec Y u)
    (l : ∀ u, Y u → QuantumComp L spec Z u) :
    (x.bind k).bind l = x.bind fun u y ↦ (k u y).bind l :=
  IFreeM.bind_assoc x k l

end QuantumComp

/-! ## Programs on a fixed final register -/

/-- The leaf family of programs that end on the register `B` with a value of type `α`. -/
abbrev QuantumComp₂.Leaf (B : QReg) (α : Type w) (u : QReg) : Type w :=
  PSigma fun _ : u = B ↦ α

/-- A quantum oracle program from the register `A` that ends on the register `B` on every branch
and returns a value in `α`. Intermediate registers may still depend on outcomes; only the final one
is fixed.

It is `QuantumComp` with the leaf family `fun u ↦ PSigma fun _ : u = B ↦ α`, whose leaves are
identified with values in `α` by `QuantumComp₂.leafEquiv`, and its execution is the general one
read at those leaves (`QuantumRuntime.branch_run₂`). It is PolyFun's `FreeM₂`, a lawful indexed
monad, and a lawful monad when `A = B`. Use `QuantumComp` when branches end on different
registers. -/
@[expose]
def QuantumComp₂ (L : LocalSig.{u, v}) (spec : QuantumOracleSpec.{u₁, v₁}) (A B : QReg)
    (α : Type w) : Type (max u v u₁ v₁ (w + 1)) :=
  QuantumComp L spec (QuantumComp₂.Leaf B α) A

namespace QuantumComp₂

variable {L : LocalSig.{u, v}} {spec : QuantumOracleSpec.{u₁, v₁}} {A B C D : QReg} {α : Type w}
  {β : Type w₁} {γ : Type w₂}

/-- The fixed-register programs are PolyFun's free indexed monad. -/
theorem eq_freeM₂ :
    QuantumComp₂ L spec A B α = FreeM₂ (QuantumComp.toIPFunctor L spec) A B α :=
  rfl

/-- The leaves of a program that ends on `B`, collected over all registers, are the values of
type `α`. -/
@[expose]
def leafEquiv (B : QReg) (α : Type w) : α ≃ Σ u : QReg, Leaf B α u where
  toFun a := ⟨B, rfl, a⟩
  invFun p := p.2.2
  left_inv _ := rfl
  right_inv := by
    rintro ⟨_, rfl, _⟩
    rfl

/-- The leaf of a fixed-register program that carries `a`. -/
@[simp]
theorem leafEquiv_apply (B : QReg) (a : α) : leafEquiv B α a = ⟨B, rfl, a⟩ :=
  rfl

/-! ### Commands and the indexed monad structure -/

/-- The program that returns `a` without a command. -/
@[expose]
protected def pure (a : α) : QuantumComp₂ L spec A A α :=
  FreeM₂.pure a

/-- Sequencing: run `x`, then the program selected by its return value. It is the general
sequencing `Quantum.QuantumComp.bind` at the leaves `⟨B, rfl, a⟩`, and the value types may lie in
different universes. -/
@[expose]
protected def bind (x : QuantumComp₂ L spec A B α) (k : α → QuantumComp₂ L spec B C β) :
    QuantumComp₂ L spec A C β :=
  QuantumComp.bind x fun _ p ↦ p.casesOn fun h a ↦ h ▸ k a

/-- Apply `f` to the return value of a program. -/
@[expose]
protected def map (f : α → β) (x : QuantumComp₂ L spec A B α) : QuantumComp₂ L spec A B β :=
  x.bind fun a ↦ QuantumComp₂.pure (f a)

/-- The local operation `o`, followed by the continuation selected by its outcome. -/
@[expose]
def primBind (o : L.Op A) (k : (b : L.Outcome o) → QuantumComp₂ L spec (L.next o b) B α) :
    QuantumComp₂ L spec A B α :=
  QuantumComp.primBind o k

/-- A call of port `i`, followed by the continuation selected by its result. -/
@[expose]
def queryBind (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)
    (k : spec.Result i → QuantumComp₂ L spec (QReg.of (spec.Out i × E)) B α) :
    QuantumComp₂ L spec A B α :=
  QuantumComp.queryBind i E ℓ k

/-- Call port `i` on the factor of the register that `ℓ` exposes, and return its result. -/
@[expose]
def query (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E) :
    QuantumComp₂ L spec A (QReg.of (spec.Out i × E)) (spec.Result i) :=
  QuantumComp.query i E ℓ

/-- The return value of `pure` as a leaf. -/
theorem pure_eq_pure (a : α) :
    (QuantumComp₂.pure a : QuantumComp₂ L spec A A α) = QuantumComp.pure ⟨rfl, a⟩ :=
  rfl

/-! ### Induction -/

/-- Induction on fixed-register programs: a property of every program follows from the property
of `pure a`, and its preservation by prefixing a local operation or a call to a family of
programs. -/
@[elab_as_elim]
protected theorem inductionOn {motive : ∀ A B : QReg, QuantumComp₂ L spec A B α → Prop}
    (pure : ∀ (A : QReg) (a : α), motive A A (QuantumComp₂.pure a))
    (primBind : ∀ (A B : QReg) (o : L.Op A)
      (k : (b : L.Outcome o) → QuantumComp₂ L spec (L.next o b) B α), (∀ b, motive _ B (k b)) →
        motive A B (primBind o k))
    (queryBind : ∀ (A B : QReg) (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)
      (k : spec.Result i → QuantumComp₂ L spec (QReg.of (spec.Out i × E)) B α),
      (∀ r, motive _ B (k r)) → motive A B (queryBind i E ℓ k))
    {A B : QReg} (x : QuantumComp₂ L spec A B α) : motive A B x :=
  FreeM₂.inductionOn (P := QuantumComp.toIPFunctor L spec) (C := motive) (fun s a ↦ pure s a)
    (fun s t c r ih ↦ by
      cases c with
      | prim o => exact primBind s t o (fun b ↦ r (ULift.up b)) fun b ↦ ih (ULift.up b)
      | query i E ℓ =>
        exact queryBind s t i E ℓ (fun b ↦ r (ULift.up b)) fun b ↦ ih (ULift.up b)) x

/-! ### Monad laws -/

/-- Left unit law. -/
@[simp]
protected theorem pure_bind (a : α) (k : α → QuantumComp₂ L spec A B β) :
    (QuantumComp₂.pure a).bind k = k a :=
  rfl

/-- Right unit law. -/
@[simp]
protected theorem bind_pure (x : QuantumComp₂ L spec A B α) : x.bind QuantumComp₂.pure = x :=
  ibind_ipure (M := FreeM₂ (QuantumComp.toIPFunctor L spec)) x

/-- Sequencing of programs is associative. -/
protected theorem bind_assoc (x : QuantumComp₂ L spec A B α) (k : α → QuantumComp₂ L spec B C β)
    (l : β → QuantumComp₂ L spec C D γ) :
    (x.bind k).bind l = x.bind fun a ↦ (k a).bind l := by
  refine (IFreeM.bind_assoc x _ _).trans (congrArg (IFreeM.bind x) ?_)
  funext u ⟨h, a⟩
  cases h
  rfl

/-- On value types in one universe, sequencing is PolyFun's `IPFunctor.FreeM₂.bind`. -/
theorem bind_eq_freeM₂_bind {β : Type w} (x : QuantumComp₂ L spec A B α)
    (k : α → QuantumComp₂ L spec B C β) : x.bind k = FreeM₂.bind x k :=
  rfl

/-- Applying `f` to the return value is sequencing with `fun a ↦ pure (f a)`. -/
theorem map_eq_bind_pure (f : α → β) (x : QuantumComp₂ L spec A B α) :
    x.map f = x.bind fun a ↦ QuantumComp₂.pure (f a) :=
  rfl

/-- On value types in one universe, applying `f` to the return value is PolyFun's
`IPFunctor.FreeM₂.map`. -/
theorem map_eq_freeM₂_map {β : Type w} (f : α → β) (x : QuantumComp₂ L spec A B α) :
    x.map f = FreeM₂.map f x := by
  induction x using IFreeM.inductionOn with
  | pure _ y =>
    obtain ⟨rfl, _⟩ := y
    rfl
  | liftBind _ c r ih => exact congrArg (IFreeM.liftBind c) (funext ih)

/-- Applying the identity to the return value changes nothing. -/
@[simp]
protected theorem map_id (x : QuantumComp₂ L spec A B α) : x.map id = x :=
  QuantumComp₂.bind_pure x

/-- Sequencing after a local operation sequences each continuation. -/
@[simp]
theorem primBind_bind (o : L.Op A) (k : (b : L.Outcome o) → QuantumComp₂ L spec (L.next o b) B α)
    (g : α → QuantumComp₂ L spec B C β) :
    (primBind o k).bind g = primBind o fun b ↦ (k b).bind g :=
  rfl

/-- Sequencing after a call sequences each continuation. -/
@[simp]
theorem queryBind_bind (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)
    (k : spec.Result i → QuantumComp₂ L spec (QReg.of (spec.Out i × E)) B α)
    (g : α → QuantumComp₂ L spec B C β) :
    (queryBind i E ℓ k).bind g = queryBind i E ℓ fun r ↦ (k r).bind g :=
  rfl

/-- A call followed by a continuation is the command with that continuation. -/
theorem query_bind (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)
    (k : spec.Result i → QuantumComp₂ L spec (QReg.of (spec.Out i × E)) C α) :
    (query i E ℓ).bind k = queryBind i E ℓ k :=
  rfl

/-- Programs that end on the register they start on form a monad. -/
instance : Monad (QuantumComp₂ L spec A A) where
  pure := QuantumComp₂.pure
  bind := QuantumComp₂.bind
  map := QuantumComp₂.map

/-- Monadic `pure` on programs is `Quantum.QuantumComp₂.pure`. -/
@[simp]
theorem pure_eq (a : α) : (pure a : QuantumComp₂ L spec A A α) = QuantumComp₂.pure a :=
  rfl

/-- Monadic bind on programs is `Quantum.QuantumComp₂.bind`. -/
@[simp]
theorem bind_eq {β : Type w} (x : QuantumComp₂ L spec A A α)
    (k : α → QuantumComp₂ L spec A A β) : x >>= k = x.bind k :=
  rfl

/-- Functorial map on programs is `Quantum.QuantumComp₂.map`. -/
@[simp]
theorem map_eq {β : Type w} (f : α → β) (x : QuantumComp₂ L spec A A α) : f <$> x = x.map f :=
  rfl

/-- The monad of programs on a fixed register is lawful. -/
instance : LawfulMonad (QuantumComp₂ L spec A A) :=
  LawfulMonad.mk' _
    (id_map := QuantumComp₂.map_id)
    (pure_bind := QuantumComp₂.pure_bind)
    (bind_assoc := QuantumComp₂.bind_assoc)
    (bind_pure_comp := fun f x ↦ (map_eq_bind_pure f x).symm)

/-- Fixed-register programs form an indexed monad over registers. -/
instance : IndexedMonad QReg (QuantumComp₂ L spec) where
  ipure := QuantumComp₂.pure
  ibind := QuantumComp₂.bind

/-- The indexed monad of fixed-register programs is lawful. -/
instance : LawfulIndexedMonad QReg (QuantumComp₂ L spec) where
  ipure_ibind := QuantumComp₂.pure_bind
  ibind_ipure := QuantumComp₂.bind_pure
  ibind_assoc := QuantumComp₂.bind_assoc

end QuantumComp₂

/-! ## Programs over instruments -/

/-- Quantum oracle programs whose local steps are given directly as dependent subinstruments:
`QuantumComp₂ LocalSig.instruments spec A B α`, interpreted by `LocalSig.Interp.instruments`.
`QComp.act p` inserts a subinstrument `p` with a fixed output register.

Use it to build programs from arbitrary quantum operations. A local step here can be any
subinstrument, so the number of steps says nothing about efficiency; use a named signature with
`QuantumComp₂ L spec` to count named local operations. For `α : Type w` the local outcomes are
also in `Type w`; write `QuantumComp₂ LocalSig.instruments.{v} spec A B α` to separate the two
universes. -/
abbrev QComp (spec : QuantumOracleSpec.{u₁, v₁}) (A B : QReg) (α : Type w) :
    Type (max u₁ v₁ (w + 1)) :=
  QuantumComp₂ LocalSig.instruments.{w} spec A B α

namespace QComp

variable {spec : QuantumOracleSpec.{u₁, v₁}} {A B C : QReg} {α β : Type w}

/-- Run a local subinstrument on the program's register and return its outcome: the operation of
the signature of instruments with constant output register. -/
@[expose]
def act (p : SubInstrument A B α) : QComp spec A B α :=
  QuantumComp₂.primBind (L := LocalSig.instruments) ⟨α, fun _ ↦ B, p⟩
    fun a ↦ QuantumComp₂.pure a

/-- A local subinstrument followed by a continuation is the command with that continuation. -/
theorem act_bind (p : SubInstrument A B β) (k : β → QComp spec B C α) :
    (act p).bind k =
      QuantumComp₂.primBind (L := LocalSig.instruments) ⟨β, fun _ ↦ B, p⟩ k :=
  rfl

end QComp

/-! ## Lossless programs -/

namespace QuantumComp

variable {L : LocalSig.{u, v}} {spec : QuantumOracleSpec.{u₁, v₁}} {X : QReg → Type w}
  {Y : QReg → Type w₁} {A : QReg}

/-- A program is lossless under the interpretation `I` when every local operation on every
branch of its tree, including branches that are reached with weight zero, is interpreted by a
lossless dependent subinstrument. Against a runtime whose steps are lossless, a lossless program
runs to a lossless dependent subinstrument (`Quantum.QuantumRuntime.lossless_run`). -/
@[expose]
def Lossless (I : L.Interp) (x : QuantumComp L spec X A) : Prop :=
  IFreeM.IsRollBound x ()
    (fun _ a _ ↦ match a with | .prim o => (I o).Lossless | .query _ _ _ => True)
    (fun _ _ b ↦ b)

variable {I : L.Interp}

/-- A program that stops at once is lossless. -/
@[simp]
theorem lossless_pure (x : X A) : (QuantumComp.pure x : QuantumComp L spec X A).Lossless I :=
  trivial

/-- A local operation followed by a continuation is lossless when the operation is interpreted
by a lossless dependent subinstrument and every continuation is lossless. -/
@[simp]
theorem lossless_primBind_iff (o : L.Op A)
    (k : (b : L.Outcome o) → QuantumComp L spec X (L.next o b)) :
    (primBind o k).Lossless I ↔ (I o).Lossless ∧ ∀ b, (k b).Lossless I :=
  and_congr Iff.rfl ULift.forall

/-- A call followed by a continuation is lossless when every continuation is. -/
@[simp]
theorem lossless_queryBind_iff (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)
    (k : spec.Result i → QuantumComp L spec X (QReg.of (spec.Out i × E))) :
    (queryBind i E ℓ k).Lossless I ↔ ∀ r, (k r).Lossless I :=
  ⟨fun h r ↦ h.2 ⟨r⟩, fun h ↦ ⟨trivial, fun r ↦ h r.down⟩⟩

/-- A call is a lossless program. -/
theorem lossless_query (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E) :
    (query (L := L) (spec := spec) i E ℓ).Lossless I :=
  ⟨trivial, fun _ ↦ trivial⟩

/-- Under a lossless interpretation, every program is lossless. -/
theorem lossless_of_interp (hI : I.Lossless) (x : QuantumComp L spec X A) : x.Lossless I := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ => trivial
  | primBind _ o k ih => exact (lossless_primBind_iff o k).mpr ⟨hI o, ih⟩
  | queryBind _ i E ℓ k ih => exact (lossless_queryBind_iff i E ℓ k).mpr ih

/-- Sequencing lossless programs is lossless. -/
theorem Lossless.bind {x : QuantumComp L spec X A} {k : ∀ u, X u → QuantumComp L spec Y u}
    (hx : x.Lossless I) (hk : ∀ u y, (k u y).Lossless I) : (x.bind k).Lossless I :=
  IFreeM.isRollBound_bind (fun _ _ ↦ ()) (fun _ _ _ _ _ h ↦ ⟨h, h⟩)
    (fun _ _ _ _ _ _ ↦ ⟨rfl, rfl⟩) hx hk

end QuantumComp

namespace QuantumComp₂

variable {L : LocalSig.{u, v}} {spec : QuantumOracleSpec.{u₁, v₁}} {A B C : QReg} {α : Type w}
  {β : Type w₁} {I : L.Interp}

/-- Returning a value is lossless. -/
@[simp]
theorem lossless_pure (a : α) : (QuantumComp₂.pure a : QuantumComp₂ L spec A A α).Lossless I :=
  trivial

/-- Sequencing lossless fixed-register programs is lossless. -/
theorem lossless_bind {x : QuantumComp₂ L spec A B α} {k : α → QuantumComp₂ L spec B C β}
    (hx : x.Lossless I) (hk : ∀ a, (k a).Lossless I) : (x.bind k).Lossless I :=
  QuantumComp.Lossless.bind hx fun _ ⟨h, a⟩ ↦ by
    subst h
    exact hk a

/-- A call is a lossless program. -/
theorem lossless_query (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E) :
    (query (L := L) (spec := spec) i E ℓ).Lossless I :=
  ⟨trivial, fun _ ↦ trivial⟩

end QuantumComp₂

namespace QComp

variable {spec : QuantumOracleSpec.{u₁, v₁}} {A B C : QReg} {α β : Type w}

/-- A local subinstrument followed by a continuation is lossless when the subinstrument and
every continuation are. -/
@[simp]
theorem lossless_act_bind_iff (p : SubInstrument A B β) (k : β → QComp spec B C α) :
    ((act p).bind k).Lossless .instruments ↔
      p.Lossless ∧ ∀ b, (k b).Lossless .instruments :=
  QuantumComp.lossless_primBind_iff _ _

/-- A lossless local subinstrument is a lossless program. -/
theorem lossless_act {p : SubInstrument A B α} (hp : p.Lossless) :
    (act (spec := spec) p).Lossless .instruments :=
  ⟨hp, fun _ ↦ trivial⟩

end QComp

end Quantum
