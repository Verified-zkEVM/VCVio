/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.DSubInstrument
public import VCVio.Quantum.Register

/-!
# Primitive signatures

A primitive signature (`Quantum.LocalSig`) names the local operations that a program may apply
to its own register, without saying what they do. For each register `A` it gives a type of
operations `Op A`; each operation `o` has a type of classical outcomes `Outcome o`, and on outcome
`b` the program holds the register `next o b`. The register after an operation may depend on its
outcome: a measurement may keep or discard a qubit according to what it reads.

An interpretation (`Quantum.LocalSig.Interp`) gives every operation its meaning, a dependent
subinstrument from `A` with outcomes in `Outcome o` and output register `next o b` on outcome
`b`. Syntax and meaning are kept apart: programs (`Quantum.QuantumComp`) are written over a
signature, and an interpretation is supplied when they are run
(`Quantum.QuantumRuntime.run`). The same program can therefore be read against several
interpretations, and properties of its tree, such as a count of its operations
(`Quantum.QuantumComp.IsCostBound`), do not depend on any of them.

* `Quantum.LocalSig.instruments`: every dependent subinstrument is an operation, and the
  interpretation `Quantum.LocalSig.Interp.instruments` sends it to itself. Programs over this
  signature (`Quantum.QComp`) may apply any subinstrument as one step.
* A gate set is a signature whose operations are finitely many named gates, interpreted by their
  channels; the tree records the cost of these named local operations. Basis equivalences at
  calls and classical continuation computation are uncharged.

## Universes

`Quantum.LocalSig.{u, v}` takes its operations in `Type u` and their outcomes in `Type v`, both
arbitrary. Registers are `Quantum.QReg : Type 1`, so an interpretation lives in
`Type (max 1 u v)`. The signature of instruments `Quantum.LocalSig.instruments.{v}` takes
dependent subinstruments with outcomes in any `Type v`; its operations, which quantify over such
outcome types, lie in `Type (v + 1)`.

## Main definitions

* `Quantum.LocalSig`, with `Quantum.LocalSig.OutcomeAt o u`, the outcomes of `o` that leave the
  register `u`.
* `Quantum.LocalSig.Interp L` and `Quantum.LocalSig.Interp.Lossless`.
* `Quantum.LocalSig.instruments`, whose operations are `Quantum.LocalSig.InstrumentOp`, and
  `Quantum.LocalSig.Interp.instruments`.
-/

public section

universe u v

namespace Quantum

/-- The names of the local operations a quantum program may apply to its own register. For each
register `A`, `Op A` is a type of operations; an operation `o` reports a classical outcome
`b : Outcome o` and leaves the register `next o b`, which may depend on `b`.

A signature is syntax: it gives no matrices, probabilities or physicality conditions. An
interpretation (`LocalSig.Interp`) supplies them. Use named operations for a gate set, or
`LocalSig.instruments` to allow every dependent subinstrument. Operations and outcomes lie in
independent universes `u` and `v`. -/
structure LocalSig where
  /-- The local operations on the register `A`. -/
  Op : QReg → Type u
  /-- The classical outcomes of an operation. -/
  Outcome : {A : QReg} → Op A → Type v
  /-- The register after an operation, as a function of its outcome. -/
  next : {A : QReg} → (o : Op A) → Outcome o → QReg

namespace LocalSig

variable (L : LocalSig.{u, v})

/-- The outcomes of the operation `o` that leave the register `u`. -/
abbrev OutcomeAt {A : QReg} (o : L.Op A) (u : QReg) : Type v :=
  {b : L.Outcome o // L.next o b = u}

/-- The physical meaning of the local operations in `L`. For each `o : L.Op A`, an
interpretation gives completely positive branch maps `Φ_b : M_A → M_{L.next o b}`, where
`M_A = Matrix A A ℂ`. For every positive semidefinite `ρ`,
`∑' b, tr (Φ_b ρ) ≤ tr ρ`.

The branch operator `Φ_b ρ` is unnormalized. On a normalized input its trace is the probability
of reporting `b`, and `1 - ∑' b, tr (Φ_b ρ)` is the failure probability. On a substate these
are weights; the trace deficit is additional lost weight. `Interp.Lossless` requires equality
in the trace bound for every operation.

Finite outcomes, a fixed output register and no loss give the instruments in Watrous,
The Theory of Quantum Information, §2.3.2, equations (2.258)–(2.261), printed p. 112
(PDF p. 120). Matrix and tensor conventions are fixed in `VCVio.Quantum.MatrixMap`. -/
@[expose]
def Interp : Type (max 1 u v) :=
  ∀ ⦃A : QReg⦄ (o : L.Op A), DSubInstrument A (L.Outcome o) fun b ↦ L.next o b

variable {L}

/-- An interpretation is lossless when it sends every operation to a lossless dependent
subinstrument. -/
@[expose]
def Interp.Lossless (I : L.Interp) : Prop :=
  ∀ ⦃A : QReg⦄ (o : L.Op A), (I o).Lossless

/-- The operations of the signature of instruments on `A`: a type of outcomes `ι : Type v`,
output registers `B : ι → QReg`, and a dependent subinstrument from `A` with these outcomes and
outputs. -/
abbrev InstrumentOp (A : QReg) : Type (v + 1) :=
  Σ (ι : Type v) (B : ι → QReg), DSubInstrument A ι fun i ↦ B i

/-- The outcomes of an operation of the signature of instruments. -/
abbrev InstrumentOp.Outcome {A : QReg} (o : InstrumentOp.{v} A) : Type v :=
  o.1

/-- The register an operation of the signature of instruments leaves on each outcome. -/
abbrev InstrumentOp.next {A : QReg} (o : InstrumentOp.{v} A) : o.Outcome → QReg :=
  o.2.1

/-- **The signature of instruments.** An operation on `A` is a dependent subinstrument from `A`,
with any type of outcomes `ι : Type v` and output registers `B : ι → QReg`
(`Quantum.LocalSig.InstrumentOp`). -/
@[expose, reducible]
def instruments : LocalSig.{v + 1, v} where
  Op := InstrumentOp
  Outcome := InstrumentOp.Outcome
  next := InstrumentOp.next

/-- The canonical interpretation of the signature of instruments: every operation means the
dependent subinstrument it is. -/
@[expose]
def Interp.instruments : Interp LocalSig.instruments.{v} :=
  fun _ o ↦ o.2.2

/-- The canonical interpretation sends an operation to the dependent subinstrument it is. -/
@[simp]
theorem Interp.instruments_apply {A : QReg} (o : (LocalSig.instruments.{v}).Op A) :
    Interp.instruments o = o.2.2 :=
  rfl

end LocalSig

end Quantum
