/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Squirrel.Rules.Rename
import VCVio.OracleComp.EvalDist.Measure
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Reusing encryption randomness: a countermodel

Encryption rules (BC14's EncCCA1, SP21's ENC-KP, LICS23's G.CCA1) require the randomness of the
challenge ciphertext to be fresh: it occurs nowhere else in the vectors. This file shows the
condition is needed, in a model where the scheme is perfectly secure for one use.

The scheme is the one-bit pad `enc m k = m xor k`, with pads the names `r` and `s : bool → bool`,
each reading its own uniform bit of the honest tape. Then:

* `TwoTimePad.valid_fresh`: `enc false r ∼ enc true r` holds against every class of
  distinguishers (the pad is fresh);
* `TwoTimePad.not_valid_reuse`: `enc false r, enc false r ∼ enc true r, enc false r` fails
  against the class of all machines (the pad is reused): the exclusive or of the two entries
  (`TwoTimePad.xorMachine`) has advantage one;
* `TwoTimePad.valid_swap`: `r false ∼ s false`, an instance of name renaming at the
  permutation exchanging `r` and `s`, which reads a different coordinate of the tape.

## References

* [BC14] Bana, Comon-Lundh, *A Computationally Complete Symbolic Attacker for Equivalence
  Properties*, CCS 2014: §7 and Fig. 2.
* [SP21] Baelde, Delaune, Jacomme, Koutsos, Moreau, *An Interactive Prover for Protocol
  Verification in the Computational Model*, S&P 2021: ENC-KP.
* [LICS23] Baelde, Koutsos, Lallemand, *A Higher-Order Indistinguishability Logic for
  Cryptographic Reasoning*, LICS 2023: Prop. 19.
-/

public section

namespace Interop.Squirrel.TwoTimePad

open IPFunctor IPFunctor.ScopedSignature

/-- Two names, the pads, indexed by a Boolean. -/
inductive Name : Ty Empty → Ty Empty → Type where
  /-- The pad `r : bool → bool`. -/
  | r : Name .bool .bool
  /-- The pad `s : bool → bool`. -/
  | s : Name .bool .bool

-- The decision procedure is exposed, so that `decide` evaluates it in other modules.
@[expose] public section

deriving instance DecidableEq for Name

end

/-- No base types, the two pads, one honest symbol of each type (the encryption at
`bool → bool → bool`) and no attacker symbols. -/
@[expose, reducible] def decl : Decl Empty where
  labels b := b.elim
  Name := Name
  nameDom_finite := fun n => match n with | .r | .s => nofun
  finite_names := Finite.of_injective (β := Bool)
    (fun n => match n with | ⟨_, _, .r⟩ => true | ⟨_, _, .s⟩ => false)
    fun | ⟨_, _, .r⟩, ⟨_, _, .r⟩, _ => rfl | ⟨_, _, .s⟩, ⟨_, _, .s⟩, _ => rfl
  Fn _ := Unit
  Att := Empty
  attTy f := f.elim

/-- Each name reads one bit, and a pad of type `bool` is that bit; encryption is `xor`. -/
@[expose] noncomputable def model : Model decl where
  lenA _ := 0
  carrier b := b.elim
  nonempty b := b.elim
  coinLen _ _ := 1
  sample η b := match b with
    | .bool => fun c => c 0
    | b => fun _ => Classical.choice (b.nonempty_value (fun b => b.elim) η)
  finite_index _ := fun n => match n with | .r | .s => inferInstanceAs (Finite Bool)
  fn η τ _ := match τ with
    | .arrow .bool (.arrow .bool .bool) => fun m k => xor m k
    | τ => Classical.choice (τ.nonempty_value (fun b => b.elim) η)
  att _ f := f.elim

theorem model_respectsLabels : model.RespectsLabels := fun b => b.elim

/-- The coordinate the pad `r` reads at index `false`. -/
abbrev slotR (η : ℕ) : model.Slot η := ⟨⟨.bool, .bool, Name.r⟩, false⟩

/-- The bit of the honest tape at a coordinate: every name reads one bit. -/
abbrev bit {η : ℕ} (ρh : model.TapeH η) (k : model.Slot η) : Bool := ρh k ⟨0, Nat.one_pos⟩

/-- A pad at index `false`. -/
@[expose] def pad (n : Name .bool .bool) : FTerm decl [] .bool :=
  FTerm.app (.node (.inl (.name (D := decl) n)) fun p => nomatch p) FTerm.ff

/-- Encryption of a message under the pad `r`. -/
@[expose] def enc (m : FTerm decl [] .bool) : FTerm decl [] .bool :=
  FTerm.app (FTerm.app (FTerm.fn (D := decl) (a := .arrow .bool (.arrow .bool .bool)) ()) m)
    (pad .r)

theorem denote_enc (C : AdvClass model) (m : FTerm decl [] .bool)
    (env : Env (Kind.Value model) []) (η : ℕ) (ρ : model.Tape η) :
    (enc m).denote (fullInterp model C) env η ρ =
      xor (m.denote (fullInterp model C) env η ρ) (bit ρ.2 (slotR η)) := rfl

/-- Flipping every bit of the honest tape. -/
@[expose] def flipTape (η : ℕ) : model.TapeH η ≃ model.TapeH η :=
  ⟨fun ρh k i => !ρh k i, fun ρh k i => !ρh k i,
    fun _ => funext fun _ => funext fun _ => Bool.not_not _,
    fun _ => funext fun _ => funext fun _ => Bool.not_not _⟩

/-- With a fresh pad, the two encryptions are indistinguishable for every class: flipping the
tape maps one to the other. -/
theorem valid_fresh (C : ∀ M : Model decl, AdvClass M) :
    Valid (fun M => M = model) C (Γ := []) []
      (.equiv (Env.cons (enc .ff) Env.empty) (Env.cons (enc .tt) Env.empty)) := by
  rintro M - rfl env -
  refine Form.holds_equiv.2 fun A _ => negligible_of_zero fun η => ENNReal.absDiff_eq_zero.2 ?_
  have he : ∀ ρ, Vec.rv model (C model) (Env.empty : Vec decl [] []) env η ρ = Env.empty :=
    fun _ => Env.eq_empty _
  simp only [Vec.rv_cons, VecRV.cons, denote_enc, FTerm.denote_tt, FTerm.denote_ff, he]
  refine Eq.trans ?_
    (SampleableType.prEvent_uniformSample_equiv ((Equiv.refl _).prodCongr (flipTape η)) _)
  refine prEvent_congr _ _ _ fun ρ => ?_
  change A.test η (Env.cons (xor false (bit ρ.2 (slotR η))) Env.empty) ρ.1 = true ↔
    A.test η (Env.cons (xor true (!bit ρ.2 (slotR η))) Env.empty) ρ.1 = true
  cases bit ρ.2 (slotR η) <;> rfl

/-- The machine returning the exclusive or of two Boolean inputs: a branch on the first. -/
@[expose] def xorMachine {B : Type} {D : Decl B} (M : Model D) : Machine M [.bool, .bool] .bool :=
  Machine.branch (Machine.branch (Machine.const false) (Machine.const true))
    (Machine.input .zero Ty.isGround_bool)

theorem xorMachine_test {B : Type} {D : Decl B} (M : Model D) :
    (xorMachine M).test = fun _ e _ => xor (e _ .zero) (e _ (.succ .zero)) := by
  funext η e ρa
  simp only [Machine.test, xorMachine, Machine.run_branch, Machine.run_const, Machine.run_input]
  cases e _ .zero <;> cases e _ (.succ .zero) <;> rfl

/-- The exclusive-or machine is built from branches, constants and an input projection, so it is
in every class, and in particular in `AdvClass.all`. -/
theorem xorMachine_mem {B : Type} {D : Decl B} {M : Model D} (C : AdvClass M)
    (hin : C.mem (Machine.input .zero Ty.isGround_bool : Machine M [.bool] .bool)) :
    C.mem (xorMachine M) :=
  C.branch_mem (C.branch_mem (C.const_mem _) (C.const_mem _)) hin

/-- With the pad reused, the exclusive or of the two entries tells the vectors apart with
advantage one. -/
theorem not_valid_reuse :
    ¬ Valid (fun M => M = model) (fun M => AdvClass.all M) (Γ := []) []
      (.equiv (Env.cons (enc .ff) (Env.cons (enc .ff) Env.empty))
        (Env.cons (enc .tt) (Env.cons (enc .ff) Env.empty))) := fun h => by
  have hM := Form.holds_equiv.1 (h model model_respectsLabels rfl Env.empty (by simp))
    (xorMachine model) (xorMachine_mem _ ((AdvClass.all _).input_mem _ _))
  rw [xorMachine_test] at hM
  refine not_negligible_one (negligible_of_le (fun η => le_of_eq ?_) hM)
  simp only [advantage, Vec.rv_cons, VecRV.cons, Env.cons_zero, Env.cons_succ, denote_enc,
    FTerm.denote_tt, FTerm.denote_ff]
  rw [prEvent_eq_zero_of_forall_not _ _ fun ρ h => by
      revert h; cases bit ρ.2 (slotR η) <;> simp,
    (prEvent_congr _ _ (fun _ => True) fun ρ => iff_true_intro (by
      cases bit ρ.2 (slotR η) <;> rfl)).trans (OracleComp.prEvent_true_eq_one _),
    ENNReal.absDiff_comm, ENNReal.absDiff_zero_right]

/-- The permutation of names exchanging the two pads. -/
@[expose] def swap : ∀ {a b : Ty Empty}, decl.Name a b ≃ decl.Name a b
  | .bool, .bool => ⟨fun | .r => .s | .s => .r, fun | .r => .s | .s => .r,
      fun n => by cases n <;> rfl, fun n => by cases n <;> rfl⟩
  | _, _ => Equiv.refl _

/-- Name renaming at the exchange of the pads, in every model: `r false ∼ s false`. -/
theorem valid_swap {R : Model decl → Prop} {C : ∀ M : Model decl, AdvClass M} :
    Valid R C (Γ := []) []
      (.equiv (Env.cons (pad .r) Env.empty) (Env.cons (pad .s) Env.empty)) := by
  intro M hl hR env hΘ
  have h := Form.holds_equiv.1 (Valid.equiv_renameNames_of_equiv (R := R) (C := C) (Θ := [])
    swap (Env.cons (pad .r) Env.empty) (ho := of_decide_eq_true rfl) M hl hR env hΘ)
  have hrv : Vec.rv M (C M) (Env.cons (pad .s) Env.empty) env =
      Vec.rv M (C M) (Vec.renameNames (fun n => swap n) (Env.cons (pad .r) Env.empty)) env := by
    funext η ρ τ x
    cases x with
    | zero => exact (denote_renameNames_closed (C M) (σ := M.tapePerm η swap)
        (fun _ _ _ => by rfl) ρ (pad .r) env).symm
    | succ x => exact nomatch x
  rw [Form.holds_equiv, hrv]
  exact h

end Interop.Squirrel.TwoTimePad
