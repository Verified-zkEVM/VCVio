/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import PolyFun.IPFunctor.Free.Indexed
public import VCVio.Quantum.Comp.LocalSig

/-!
# Quantum programs

A quantum program is a tree of commands over a primitive signature `L` (`Quantum.LocalSig`) and
a quantum oracle signature `spec` (`Quantum.QuantumOracleSpec`). The oracle signature names a
type of ports; port `i` takes an input register `In i`, leaves an output register `Out i`, and
returns a classical result of type `Result i`. A program has two kinds of command:

* `prim o`: a local operation `o : L.Op A` on the program's own register `A`. Its outcome `b`
  selects the continuation, which runs on the register `L.next o b`.
* `query i E ℓ`: a call of port `i`. The equivalence `ℓ : A ≃ In i × E` exposes the port's input
  register as a tensor factor of the current register; the rest `E` is carried through the call
  untouched, and the register afterwards is `Out i × E`. The result `r : Result i` selects the
  continuation.

Programs mention neither the meaning of the local operations nor any oracle: an interpretation
of `L` (`Quantum.LocalSig.Interp`) and a runtime (`Quantum.QuantumRuntime`) supply them when the
program is run (`Quantum.QuantumRuntime.run`).

## The general model

`Quantum.QuantumComp L spec X A` is the free monad on these commands in McBride's style
(PolyFun's `IPFunctor.IFreeM`): a program from the register `A` over the leaf family
`X : QReg → Type w` is a tree whose leaves `x : X u` each sit on their own final register `u`.
This is the general model of quantum oracle programs with a definite causal order:

* **Adaptive.** Every continuation sees all classical outcomes so far, so the number of queries,
  their ports and their order, and the point at which the program stops all depend on them.
* **Multi-port.** A signature has any type of ports, each with its own registers and classical
  result type.
* **Register-changing.** Each command changes the register, and the register after a local
  operation may depend on its outcome: programs allocate, discard and reshape registers between
  queries, and different branches may end on different registers.
* **Parametric in the primitives.** Local operations are drawn from a signature and interpreted
  separately, so the same tree can be read as a circuit over a gate set, with its gate count read
  off the tree, or as a program over arbitrary instruments.
* **Stateful oracles.** An oracle is a runtime with a private register that persists across
  calls (`Quantum.QuantumRuntime`); the program has no command acting on it.

The other forms are abbreviations of this one:

* `Quantum.QuantumComp₂ L spec A B α`: every leaf sits on the register `B` and carries a value of
  type `α`. This is the leaf family `fun u ↦ PSigma fun _ : u = B ↦ α`, that is PolyFun's
  `IPFunctor.FreeM₂`, a lawful indexed monad.
* `Quantum.QComp spec A B α`: the fixed-register form over the signature of instruments
  (`Quantum.LocalSig.instruments`), where a local step is any subinstrument
  (`Quantum.QComp.act`).

Query budgets are read off the tree (`Quantum.QuantumComp.IsQueryBound`) rather than fixed by a
type index. Fixed-slot adversaries (`Quantum.QuantumComb`) are a further derived form: they embed
as straight-line programs (`Quantum.QuantumComb.toComp`).

## Universes

Every type a user supplies may lie in any universe:

* a primitive signature `L : Quantum.LocalSig.{u, v}` has operations in `Type u` and outcomes in
  `Type v`;
* an oracle signature `spec : Quantum.QuantumOracleSpec.{u₁, v₁}` has ports in `Type u₁` and
  results in `Type v₁`;
* the leaf family is `X : QReg → Type w`.

Then `Quantum.QuantumComp L spec X A : Type (max u v u₁ v₁ (w + 1))`, and sequencing
(`Quantum.QuantumComp.bind`) may move to a leaf family in another universe. A command responds
with either an outcome (in `Type v`) or a result (in `Type v₁`), and PolyFun's indexed polynomial
functors have one universe of responses, so `Quantum.QuantumComp.Cmd.Resp` lifts both to
`Type (max v v₁)` with `ULift`, and the continuations of `primBind` and `queryBind` meet the
lifted responses through `Quantum.QuantumComp.onDown`. That is the only lift: `primBind`,
`queryBind`, `prim`, `query`, execution and every statement about them take unlifted outcomes
and results.

The one fixed level is the index universe. Registers (`Quantum.QReg`) are finite types with
carriers in `Type`, which loses nothing because every finite type is equivalent to some `Fin n`;
this puts `QReg` in `Type 1`, so the commands are indexed by `Type 1` and contain registers (the
remainder `E` of a call), which is why `Quantum.QuantumComp.Cmd` lies in `Type (max 1 u u₁)`. The
`w + 1` in the universe of programs is the bound PolyFun's `IPFunctor.IFreeM` declares; it does
not restrict the leaves.

The derived forms take the universes they inherit: `Quantum.QuantumComp₂ L spec A B α` takes
`α : Type w` for any `w`, and `Quantum.QComp spec A B α` takes `α : Type w` together with the
signature of instruments whose outcomes lie in the same `Type w`
(`Quantum.LocalSig.instruments.{w}`).

## Not covered

* **Coherent port choice.** The port of a query is classical. A query whose port is chosen by a
  quantum register is expressed through a single sum port acting on `ι × X × Y`, which is a
  different resource from one call to each port. An isometric layer of programs, in which this
  choice is coherent, is left to later work.
* **Unbounded loops.** Program trees are well founded, so every path is finite. Unbounded or
  expected-time programs need a coinductive tree and execution as a limit.
* **Infinite dimension.** Registers are finite-dimensional (`Quantum.QReg`); the outcome types of
  operations and the result types of ports may be infinite.

## Main definitions

* `Quantum.QuantumOracleSpec`, with the commands `Quantum.QuantumComp.Cmd L spec` and the indexed
  polynomial functor `Quantum.QuantumComp.toIPFunctor L spec`.
* `Quantum.QuantumComp L spec X A`, with `pure`, McBride `bind`, the commands followed by
  continuations `primBind` and `queryBind`, the generic commands `prim` and `query`, and the
  induction principle `Quantum.QuantumComp.inductionOn`.
* `Quantum.QuantumComp₂ L spec A B α`, with its `Monad`, `LawfulMonad`, `IndexedMonad` and
  `LawfulIndexedMonad` instances.
* `Quantum.QComp spec A B α`, with `Quantum.QComp.act`.
* `Quantum.QuantumComp.Lossless I x`: every local operation on every branch is interpreted by a
  lossless dependent subinstrument.
-/

public section

open IPFunctor

universe u v u₁ v₁ w w₁ w₂

namespace Quantum

/-- A quantum oracle signature: a type of ports, and for each port an input register, an output
register and a classical result type. Ports lie in `Type u₁` and results in `Type v₁`. -/
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

/-- **Quantum programs.** A program over the primitive signature `L` and the oracle signature
`spec` that starts on the register `A`, whose leaves `x : X u` each sit on their own final
register `u`. The operations, outcomes, ports, results and leaves may lie in any universes. -/
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

/-- Sequencing on the underlying trees, by recursion on the first tree. Unlike PolyFun's
`IPFunctor.IFreeM.bind`, the two leaf families may lie in different universes. -/
@[expose]
def bindAux (k : ∀ u, X u → QuantumComp L spec Y u) :
    {A : QReg} → IFreeM (toIPFunctor L spec) X A → QuantumComp L spec Y A
  | _, .pure x => k _ x
  | _, .liftBind c r => IFreeM.liftBind c fun b ↦ bindAux k (r b)

/-- **Sequencing.** Run `x`, and at each leaf `y : X u` continue with `k u y` from the register
`u` on which the leaf sits. The leaf families of `x` and `k` may lie in different universes. -/
@[expose]
protected def bind (x : QuantumComp L spec X A) (k : ∀ u, X u → QuantumComp L spec Y u) :
    QuantumComp L spec Y A :=
  bindAux k x

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

/-- On programs whose leaf families share a universe, sequencing is PolyFun's
`IPFunctor.IFreeM.bind`. -/
theorem bind_eq_iFreeM_bind {Y : QReg → Type w} (x : QuantumComp L spec X A)
    (k : ∀ u, X u → QuantumComp L spec Y u) : x.bind k = IFreeM.bind x k := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => rfl
  | liftBind _ c r ih => exact congrArg (IFreeM.liftBind c) (funext ih)

/-! ## Monad laws -/

/-- Right unit law. -/
@[simp]
protected theorem bind_pure (x : QuantumComp L spec X A) :
    x.bind (fun _ y ↦ QuantumComp.pure y) = x := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ => rfl
  | primBind _ o k ih => exact congrArg (primBind o) (funext ih)
  | queryBind _ i E ℓ k ih => exact congrArg (queryBind i E ℓ) (funext ih)

/-- Sequencing of programs is associative. -/
protected theorem bind_assoc (x : QuantumComp L spec X A) (k : ∀ u, X u → QuantumComp L spec Y u)
    (l : ∀ u, Y u → QuantumComp L spec Z u) :
    (x.bind k).bind l = x.bind fun u y ↦ (k u y).bind l := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ => rfl
  | primBind _ o k' ih => exact congrArg (primBind o) (funext ih)
  | queryBind _ i E ℓ k' ih => exact congrArg (queryBind i E ℓ) (funext ih)

end QuantumComp

/-! ## Programs on a fixed final register -/

/-- The leaf family of programs that end on the register `B` with a value of type `α`. -/
abbrev QuantumComp₂.Leaf (B : QReg) (α : Type w) (u : QReg) : Type w :=
  PSigma fun _ : u = B ↦ α

/-- **Programs on a fixed final register.** A program over `L` and `spec` that starts on the
register `A`, ends on the register `B` on every branch and returns a value of type `α`: the leaf
family `Quantum.QuantumComp₂.Leaf B α`. The value type `α : Type w` may lie in any universe, and
`L` and `spec` keep theirs. It is PolyFun's free indexed monad
`IPFunctor.FreeM₂ (Quantum.QuantumComp.toIPFunctor L spec) A B α`, with the same `pure` and, on
value types in one universe, the same `bind` (`Quantum.QuantumComp₂.bind_eq_freeM₂_bind`). -/
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
protected theorem bind_pure (x : QuantumComp₂ L spec A B α) : x.bind QuantumComp₂.pure = x := by
  induction x using QuantumComp₂.inductionOn with
  | pure _ _ => rfl
  | primBind _ _ o k ih => exact congrArg (QuantumComp₂.primBind o) (funext ih)
  | queryBind _ _ i E ℓ k ih => exact congrArg (QuantumComp₂.queryBind i E ℓ) (funext ih)

/-- Sequencing of programs is associative. -/
protected theorem bind_assoc (x : QuantumComp₂ L spec A B α) (k : α → QuantumComp₂ L spec B C β)
    (l : β → QuantumComp₂ L spec C D γ) :
    (x.bind k).bind l = x.bind fun a ↦ (k a).bind l := by
  refine QuantumComp₂.inductionOn (motive := fun _ B x ↦ ∀ k : α → QuantumComp₂ L spec B C β,
    (x.bind k).bind l = x.bind fun a ↦ (k a).bind l) (fun _ _ _ ↦ rfl) ?_ ?_ x k
  · intro _ _ o _ ih k
    exact congrArg (QuantumComp₂.primBind o) (funext fun b ↦ ih b k)
  · intro _ _ i E ℓ _ ih k
    exact congrArg (QuantumComp₂.queryBind i E ℓ) (funext fun r ↦ ih r k)

/-- On value types in one universe, sequencing is PolyFun's `IPFunctor.FreeM₂.bind`. -/
theorem bind_eq_freeM₂_bind {β : Type w} (x : QuantumComp₂ L spec A B α)
    (k : α → QuantumComp₂ L spec B C β) : x.bind k = FreeM₂.bind x k := by
  induction x using IFreeM.inductionOn with
  | pure _ y =>
    obtain ⟨rfl, _⟩ := y
    rfl
  | liftBind _ c r ih => exact congrArg (IFreeM.liftBind c) (funext ih)

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

/-- **Programs over instruments.** The fixed-register programs over the signature of instruments
(`Quantum.LocalSig.instruments`): every local step is a dependent subinstrument. For a value type
`α : Type w`, the instruments have outcomes in the same universe `Type w`
(`Quantum.LocalSig.instruments.{w}`); programs whose instrument outcomes and values lie in
different universes are `Quantum.QuantumComp₂ LocalSig.instruments.{v} spec A B α`. -/
abbrev QComp (spec : QuantumOracleSpec.{u₁, v₁}) (A B : QReg) (α : Type w) :
    Type (max u₁ v₁ (w + 1)) :=
  QuantumComp₂ LocalSig.instruments.{w} spec A B α

namespace QComp

variable {spec : QuantumOracleSpec.{u₁, v₁}} {A B C : QReg} {α β : Type w}

/-- Run a local subinstrument on the program's register and return its outcome: the operation of
the signature of instruments given by the dependent form `Quantum.SubInstrument.toD p`. -/
@[expose]
def act (p : SubInstrument A B α) : QComp spec A B α :=
  QuantumComp₂.primBind (L := LocalSig.instruments) ⟨α, fun _ ↦ B, SubInstrument.toD p⟩
    fun a ↦ QuantumComp₂.pure a

/-- A local subinstrument followed by a continuation is the command with that continuation. -/
theorem act_bind (p : SubInstrument A B β) (k : β → QComp spec B C α) :
    (act p).bind k =
      QuantumComp₂.primBind (L := LocalSig.instruments) ⟨β, fun _ ↦ B, SubInstrument.toD p⟩ k :=
  rfl

end QComp

/-! ## Lossless programs -/

namespace QuantumComp

variable {L : LocalSig.{u, v}} {spec : QuantumOracleSpec.{u₁, v₁}} {X : QReg → Type w}
  {Y : QReg → Type w₁} {A : QReg}

/-- Every local operation on every branch of the tree is interpreted by a lossless dependent
subinstrument. -/
@[expose]
def losslessAux (I : L.Interp) : {A : QReg} → IFreeM (toIPFunctor L spec) X A → Prop
  | _, .pure _ => True
  | _, .liftBind (.prim o) k => (I o).Lossless ∧ ∀ b, losslessAux I (k (ULift.up b))
  | _, .liftBind (.query _ _ _) k => ∀ r, losslessAux I (k (ULift.up r))

/-- A program is lossless under the interpretation `I` when every local operation on every
branch of its tree, including branches that are reached with weight zero, is interpreted by a
lossless dependent subinstrument. Against a runtime whose steps are lossless, a lossless program
runs to a lossless dependent subinstrument (`Quantum.QuantumRuntime.lossless_run`). -/
@[expose]
def Lossless (I : L.Interp) (x : QuantumComp L spec X A) : Prop :=
  losslessAux I x

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
  Iff.rfl

/-- A call followed by a continuation is lossless when every continuation is. -/
@[simp]
theorem lossless_queryBind_iff (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)
    (k : spec.Result i → QuantumComp L spec X (QReg.of (spec.Out i × E))) :
    (queryBind i E ℓ k).Lossless I ↔ ∀ r, (k r).Lossless I :=
  Iff.rfl

/-- A call is a lossless program. -/
theorem lossless_query (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E) :
    (query (L := L) (spec := spec) i E ℓ).Lossless I :=
  fun _ ↦ trivial

/-- Under a lossless interpretation, every program is lossless. -/
theorem lossless_of_interp (hI : I.Lossless) (x : QuantumComp L spec X A) : x.Lossless I := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ => trivial
  | primBind _ o k ih => exact ⟨hI o, ih⟩
  | queryBind _ i E ℓ k ih => exact ih

/-- Sequencing lossless programs is lossless. -/
theorem Lossless.bind {x : QuantumComp L spec X A} {k : ∀ u, X u → QuantumComp L spec Y u}
    (hx : x.Lossless I) (hk : ∀ u y, (k u y).Lossless I) : (x.bind k).Lossless I := by
  induction x using QuantumComp.inductionOn with
  | pure _ y => exact hk _ y
  | primBind _ o k' ih => exact ⟨hx.1, fun b ↦ ih b (hx.2 b)⟩
  | queryBind _ i E ℓ k' ih => exact fun r ↦ ih r (hx r)

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
  fun _ ↦ trivial

end QuantumComp₂

namespace QComp

variable {spec : QuantumOracleSpec.{u₁, v₁}} {A B C : QReg} {α β : Type w}

/-- A local subinstrument followed by a continuation is lossless when the subinstrument and
every continuation are. -/
@[simp]
theorem lossless_act_bind_iff (p : SubInstrument A B β) (k : β → QComp spec B C α) :
    ((act p).bind k).Lossless .instruments ↔
      p.Lossless ∧ ∀ b, (k b).Lossless .instruments :=
  and_congr_left' SubInstrument.lossless_toD_iff

/-- A lossless local subinstrument is a lossless program. -/
theorem lossless_act {p : SubInstrument A B α} (hp : p.Lossless) :
    (act (spec := spec) p).Lossless .instruments :=
  ⟨SubInstrument.lossless_toD_iff.mpr hp, fun _ ↦ trivial⟩

end QComp

end Quantum
