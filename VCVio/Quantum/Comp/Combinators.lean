/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Comp.Simulation

/-!
# Combinators on signatures and runtimes

Small constructions on oracle signatures and runtimes, used to build the emulated oracles of
ePrint 2025/2166, §4.1–4.2 (`VCVio.Quantum.Oracle.Emulated`) and their extensions.

* `Quantum.uSpec P In`: the signature of unitary ports. Port `i` acts on `In i`, returns it, and
  has no classical result. The emulated oracles of §4.1 (paper p. 28) answer this
  signature.
* `Quantum.QuantumOracleSpec.sum s t`: the disjoint union of two signatures.
* `Quantum.SubInstrument.reindex eA eB p`: transport a subinstrument along bijections of its
  input and output bases.
* `Quantum.QuantumRuntime.extend R step'`: add ports that act on the runtime's private register.
  This is the step from `EO` to `EO^(Ext)` (paper p. 50).
* `Quantum.QuantumRuntime.addRegister R G σ`: adjoin a register `G`, prepared in `σ`, that the
  existing ports leave alone (the step from `Init` to `Init′`, paper p. 51).

## Main statements

* `Quantum.QuantumRuntime.outcomeLawWith_addRegister`: a register that no port touches, prepared
  in a state of trace one, changes no law of any program. The proof is a simulation
  (`Quantum.QuantumRuntime.trace_jointPost_eq_of_simulation`) through the partial trace over the
  added register.
-/

public section

open MeasureTheory
open scoped Kronecker

universe u u₁ u₂ v₁ v w

namespace Quantum

/-! ## Signatures -/

/-- The signature of unitary ports: port `i` acts on the register `In i`, returns it, and has no
classical result. Emulated oracles (ePrint 2025/2166, §4.1, p. 28) answer this
signature. -/
@[expose, reducible]
def uSpec (P : Type u) (In : P → QReg) : QuantumOracleSpec.{u, 0} where
  Port := P
  In := In
  Out := In
  Result _ := Unit

/-- The disjoint union of two signatures: the ports of `s`, then the ports of `t`, each with its
registers and result type. The port types may live in different universes; the result types
share one, since `Result` is a single family on `s.Port ⊕ t.Port` and the results of each side
are kept as they are, without lifting. -/
@[expose, reducible]
def QuantumOracleSpec.sum (s : QuantumOracleSpec.{u₁, v₁}) (t : QuantumOracleSpec.{u₂, v₁}) :
    QuantumOracleSpec.{max u₁ u₂, v₁} where
  Port := s.Port ⊕ t.Port
  In := Sum.elim s.In t.In
  Out := Sum.elim s.Out t.Out
  Result := Sum.elim s.Result t.Result

/-! ## Transport of subinstruments along bases -/

namespace SubInstrument

variable {A A' B B' : Type*} [Fintype A] [Fintype A'] [Fintype B] [Fintype B'] [DecidableEq A]
  [DecidableEq A'] [DecidableEq B] [DecidableEq B'] {α : Type*}

/-- Transport a subinstrument `p` from `A` to `B` along bijections `eA : A ≃ A'` and
`eB : B ≃ B'`: relabel `A'` back to `A`, run `p`, and relabel `B` to `B'`. -/
@[expose]
noncomputable def reindex (eA : A ≃ A') (eB : B ≃ B') (p : SubInstrument A B α) :
    SubInstrument A' B' α :=
  (relabel eA.symm).bind fun _ ↦ p.bind fun a ↦ (relabel eB).bind fun _ ↦ SubInstrument.pure a

/-- The branch of a transported subinstrument: move the input back along `eA`, apply the branch
of `p`, and move the output along `eB`. -/
theorem branch_reindex_apply (eA : A ≃ A') (eB : B ≃ B') (p : SubInstrument A B α) (a : α)
    (ρ : Matrix A' A' ℂ) :
    (p.reindex eA eB).branch a ρ = (p.branch a (ρ.submatrix eA eA)).submatrix eB.symm eB.symm := by
  rw [reindex, branch_bind_unit, branch_bind_bind_unit_pure, LinearMap.comp_apply,
    LinearMap.comp_apply, relabel_branch_apply, relabel_branch_apply, Equiv.symm_symm]

/-- A transported lossless subinstrument is lossless. -/
theorem Lossless.reindex {p : SubInstrument A B α} (hp : p.Lossless) (eA : A ≃ A')
    (eB : B ≃ B') : (p.reindex eA eB).Lossless :=
  (lossless_relabel _).bind fun _ ↦ hp.bind fun _ ↦
    (lossless_relabel _).bind fun _ ↦ lossless_pure _

end SubInstrument

/-! ## Runtimes -/

namespace QuantumRuntime

variable {s : QuantumOracleSpec.{u₁, v₁}} {t : QuantumOracleSpec.{u₂, v₁}}

/-- Add ports `t` that act on the private register of `R`. The ports of `s` are answered by `R`
and the ports of `t` by `step'`. This is the step from `EO` to `EO^(Ext)` of ePrint 2025/2166
(p. 50), for general runtimes. -/
@[expose]
def extend (R : QuantumRuntime s)
    (step' : ∀ j : t.Port, SubInstrument (t.In j × R.D) (t.Out j × R.D) (t.Result j)) :
    QuantumRuntime (s.sum t) where
  D := R.D
  init := R.init
  step
    | .inl i => R.step i
    | .inr j => step' j

variable (R : QuantumRuntime s)
  (step' : ∀ j : t.Port, SubInstrument (t.In j × R.D) (t.Out j × R.D) (t.Result j))

/-- An extended runtime keeps the private register. -/
@[simp]
theorem extend_D : (R.extend step').D = R.D :=
  rfl

/-- An extended runtime keeps the initial substate. -/
@[simp]
theorem extend_init : (R.extend step').init = R.init :=
  rfl

/-- An extended runtime answers the old ports as before. -/
@[simp]
theorem extend_step_inl (i : s.Port) : (R.extend step').step (.inl i) = R.step i :=
  rfl

/-- An extended runtime answers the new ports by the added steps. -/
@[simp]
theorem extend_step_inr (j : t.Port) : (R.extend step').step (.inr j) = step' j :=
  rfl

/-- Adjoin a register `G` prepared in `σ` beside the private register of `R`; every port acts as
before and leaves `G` alone. This is the step from `Init` to `Init′` of ePrint 2025/2166
(p. 51), for general runtimes. -/
@[expose]
noncomputable def addRegister (G : QReg) (σ : SubState G) : QuantumRuntime s where
  D := QReg.of (R.D × G)
  init := R.init.prod σ
  step i := ((R.step i).frame G).reindex (Equiv.prodAssoc _ _ _) (Equiv.prodAssoc _ _ _)

variable (G : QReg) (σ : SubState G)

/-- The initial substate of a runtime with an added register. -/
@[simp]
theorem addRegister_init : (R.addRegister G σ).init = R.init.prod σ :=
  rfl

/-- The branches of a step of a runtime with an added register: the branch of the old step on
the factor `In i × D`, with `G` carried along. -/
theorem addRegister_step_branch_apply (i : s.Port) (r : s.Result i)
    (ρ : Matrix (s.In i × (R.addRegister G σ).D) (s.In i × (R.addRegister G σ).D) ℂ) :
    ((R.addRegister G σ).step i).branch r ρ =
      (((R.step i).branch r).amplify G
        (ρ.submatrix (Equiv.prodAssoc _ _ _) (Equiv.prodAssoc _ _ _))).submatrix
        (Equiv.prodAssoc _ _ _).symm (Equiv.prodAssoc _ _ _).symm :=
  SubInstrument.branch_reindex_apply _ _ _ r ρ

/-- A runtime with an added register has lossless steps when the original runtime does. -/
theorem lossless_addRegister_step {i : s.Port} (hi : (R.step i).Lossless) :
    ((R.addRegister G σ).step i).Lossless :=
  (hi.frame G).reindex _ _

/-- The partial trace over `G'` on `D × G'`, amplified by a left factor `B`, is the partial
trace over the last factor after reassociation. -/
private theorem amplifyLeft_traceRight_eq {B D G' : Type*} [Fintype G']
    (M : Matrix (B × (D × G')) (B × (D × G')) ℂ) :
    (MatrixMap.traceRight D G').amplifyLeft B M =
      MatrixMap.traceRight (B × D) G'
        (M.submatrix (Equiv.prodAssoc B D G') (Equiv.prodAssoc B D G')) := by
  ext x y
  simp

/-- A map on `In × D` commutes with the partial trace over `G'` when it is amplified by `G'` and
the registers are reassociated. -/
private theorem amplifyLeft_traceRight_comm {In Out D G' : Type*} [Fintype G']
    (Φ : MatrixMap (In × D) (Out × D)) (ρ : Matrix (In × (D × G')) (In × (D × G')) ℂ) :
    Φ ((MatrixMap.traceRight D G').amplifyLeft In ρ) =
      (MatrixMap.traceRight D G').amplifyLeft Out
        ((Φ.amplify G' (ρ.submatrix (Equiv.prodAssoc In D G') (Equiv.prodAssoc In D G'))).submatrix
          (Equiv.prodAssoc Out D G').symm (Equiv.prodAssoc Out D G').symm) := by
  rw [amplifyLeft_traceRight_eq, amplifyLeft_traceRight_eq, Matrix.submatrix_submatrix,
    Equiv.symm_comp_self, Matrix.submatrix_id_id,
    ← LinearMap.comp_apply (MatrixMap.traceRight _ G'), MatrixMap.traceRight_comp_amplify,
    LinearMap.comp_apply]

/-- The partial trace over the added register simulates the runtime with the added register by
the original runtime. -/
theorem simulation_addRegister (i : s.Port) (r : s.Result i) :
    (R.step i).branch r ∘ₗ (MatrixMap.traceRight R.D G).amplifyLeft (s.In i) =
      (MatrixMap.traceRight R.D G).amplifyLeft (s.Out i) ∘ₗ
        ((R.addRegister G σ).step i).branch r :=
  LinearMap.ext fun ρ ↦ (amplifyLeft_traceRight_comm ((R.step i).branch r) ρ).trans
    (congrArg ((MatrixMap.traceRight R.D G).amplifyLeft (s.Out i))
      (addRegister_step_branch_apply R G σ i r ρ).symm)

/-- The partial trace over the added register sends the initial operator of the runtime with
the added register to the initial operator of the original runtime. -/
theorem traceRight_addRegister_init (hσ : σ.matrix.trace = 1) :
    MatrixMap.traceRight R.D G (R.addRegister G σ).init.matrix = R.init.matrix := by
  change MatrixMap.traceRight R.D G (R.init.prod σ).matrix = R.init.matrix
  rw [SubState.matrix_prod, MatrixMap.traceRight_kronecker, hσ, one_smul]

/-- A register that no port touches, prepared in a state of trace one, changes no law: every
observation of every program has the same law against `R.addRegister G σ` as against `R`. -/
theorem outcomeLawWith_addRegister {L : LocalSig.{u, v}} (I : L.Interp) {X : QReg → Type w}
    {A : QReg} {γ : Type*} [MeasurableSpace γ] (hσ : σ.matrix.trace = 1)
    (x : QuantumComp L s X A) (ρ : SubState A) (f : (Σ u, X u) → γ) :
    (R.addRegister G σ).outcomeLawWith I x ρ f = R.outcomeLawWith I x ρ f := by
  have h := fun p ↦ (trace_jointPost_eq_of_simulation (R₁ := R.addRegister G σ) (R₂ := R)
    (V := MatrixMap.traceRight R.D G) I (simulation_addRegister R G σ)
    (fun M ↦ MatrixMap.trace_traceRight M) (R.traceRight_addRegister_init G σ hσ) x ρ p).symm
  simp only [outcomeLawWith, h]

/-- A register that no port touches, prepared in a state of trace one, changes no outcome law. -/
theorem outcomeLaw_addRegister {L : LocalSig.{u, v}} (I : L.Interp) {X : QReg → Type w}
    {A : QReg} [MeasurableSpace (Σ u, X u)] (hσ : σ.matrix.trace = 1)
    (x : QuantumComp L s X A) (ρ : SubState A) :
    (R.addRegister G σ).outcomeLaw I x ρ = R.outcomeLaw I x ρ :=
  (outcomeLaw_eq_of_simulation (R₁ := R.addRegister G σ) (R₂ := R)
    (V := MatrixMap.traceRight R.D G) I (simulation_addRegister R G σ)
    (fun M ↦ MatrixMap.trace_traceRight M) (R.traceRight_addRegister_init G σ hσ) x ρ).symm

end QuantumRuntime

end Quantum
