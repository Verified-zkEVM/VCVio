/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Squirrel.Derivation
public import Interop.Squirrel.Test.TwoTimePad
import VCVio.OracleComp.EvalDist.Measure
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Checks of the encryption rule

The declaration is `TwoTimePad.decl`: two pads `r` and `s : bool → bool` and one honest symbol of
each type. `encSymbols nk` reads it as an encryption scheme with key name `nk` and coin name `r`,
both at index `false`; keys, coins, public keys, messages and ciphertexts are bits.
`encModel enc` interprets the public key of a key as the key, encryption as `enc`, and gives every
message the same length. The messages are `true` and `false` and the context is empty.

* `padInstance_syntactic`: the syntactic side conditions (`EncInstance.Syntactic`) of the
  instance with messages `true` and `false` and the empty context hold, by `decide`.
* `padInstance_holds`, `valid_enc_pad`: for the one-time pad `enc m r pk = m xor r`, the
  hypotheses of `Valid.equiv_enc` hold together against every machine, so the rule
  concludes `pk, enc(true; r, pk) ∼ pk, enc(false; r, pk)`. The IND-CPA hypothesis holds because
  the two branches of the game are equal in distribution (`pad_experiment_evalDistEq`), so every
  adversary has advantage zero (`pad_advantage_eq_zero`). `encDerivation` is the same conclusion
  as a one-step derivation, and `encDerivation_sound` discharges the hypothesis of
  `Derivation.sound`.
* `not_valid_enc_leaky`: for the scheme `enc m r pk = m`, which leaks the message, the conclusion
  fails against every machine, although the side conditions hold. So the IND-CPA hypothesis
  is needed.
* `not_valid_enc_keyIsCoin`: with the key name equal to the coin name, the conclusion fails for the
  one-time pad, although the IND-CPA hypothesis holds and the messages use neither name. So the
  names must be distinct: the coins must be fresh with respect to the key. `decide` rejects the
  instance (`not_keyIsCoin_syntactic`).
* `not_valid_enc_coinReused`: with the coins in the context, the conclusion fails for the one-time
  pad, although the names are distinct and the IND-CPA hypothesis holds. So the context must not
  use the coin name, and `decide` rejects the instance (`not_coinReused_syntactic`).
-/

public section

namespace Interop.Squirrel.EncExamples

open IPFunctor IPFunctor.ScopedSignature AsymmEncAlg TwoTimePad

/-- `TwoTimePad.decl` as an encryption scheme with key name `nk` and coin name `r`. Every type is
`bool`, both indices are the honest constant of type `bool`. -/
@[expose, reducible] def encSymbols (nk : Name .bool .bool) : EncSymbols decl where
  keyIdx := .bool
  keyTy := .bool
  coinIdx := .bool
  coinTy := .bool
  pkTy := .bool
  msgTy := .bool
  cTy := .bool
  lenTy := .arrow .bool .bool
  nk := nk
  ik := ()
  nr := Name.r
  ir := ()
  pkOf := ()
  encOf := ()
  lenOf := ()

/-- Each name reads one bit, and a pad of type `bool` is that bit; the honest constant of type
`bool` is
`false`, the public key of a key is the key, encryption is `enc`, and every message has the same
length. -/
@[expose] noncomputable def encModel (enc : Bool → Bool → Bool → Bool) : Model decl where
  lenA _ := 0
  carrier b := b.elim
  nonempty b := b.elim
  coinLen _ _ := 1
  sample η b := match b with
    | .bool => fun c => c 0
    | b => fun _ => Classical.choice (b.nonempty_value (fun b => b.elim) η)
  finite_index _ := fun n => match n with | .r | .s => inferInstanceAs (Finite Bool)
  fn η τ _ := match τ with
    | .bool => false
    | .arrow .bool .bool => id
    | .arrow .bool (.arrow .bool (.arrow .bool .bool)) => enc
    | .arrow .bool (.arrow .bool .bool) => fun _ => id
    | τ => Classical.choice (τ.nonempty_value (fun b => b.elim) η)
  att _ f := f.elim

/-- The bit of the honest tape at a coordinate: every name reads one bit. -/
abbrev encBit {enc : Bool → Bool → Bool → Bool} {η : ℕ} (ρh : (encModel enc).TapeH η)
    (k : (encModel enc).Slot η) : Bool :=
  ρh k ⟨0, Nat.one_pos⟩

theorem encModel_respectsLabels (enc : Bool → Bool → Bool → Bool) :
    (encModel enc).RespectsLabels := fun b => b.elim

/-- The one-time pad. -/
@[expose] def pad (m r _ : Bool) : Bool := xor m r

/-- A scheme that leaks the message. -/
@[expose] def leaky (m _ _ : Bool) : Bool := m

/-- Every message has the same length in these models. -/
theorem equalLength (nk : Name .bool .bool) (enc : Bool → Bool → Bool → Bool)
    (m₀ m₁ : FTerm decl [.loc .bool] .bool) : (encSymbols nk).EqualLength (encModel enc) m₀ m₁ :=
  fun _ _ => rfl

/-- For the one-time pad, the two branches of the one-time IND-CPA game are equal in
distribution, for every adversary and either key name: a uniform bit masks the message. -/
theorem pad_experiment_evalDistEq (nk : Name .bool .bool) (η : ℕ)
    (adv : IND_CPA_OneTime_Adversary ((encSymbols nk).scheme (encModel pad) η)) (b : Bool) :
    IND_CPA_OneTime_Experiment adv b =ᵈ IND_CPA_OneTime_Experiment adv true := by
  have hmask : ∀ pk m, ((encSymbols nk).scheme (encModel pad) η).encrypt pk m =ᵈ
      ($ᵗ Bool : ProbComp Bool) := fun pk m => by
    change (do let rc ← ($ᵗ (Fin 1 → Bool) : ProbComp (Fin 1 → Bool)); pure (xor m (rc 0))) =ᵈ _
    rw [bind_pure_comp]
    refine SampleableType.map_uniformSample_evalDistEq_of_bijective
      ⟨fun a c h => funext fun i => ?_, fun c => ⟨fun _ => xor m c, ?_⟩⟩
    · rw [Subsingleton.elim (α := Fin 1) i 0]
      cases m <;> cases ha : a 0 <;> cases hc : c 0 <;> simp_all
    · cases m <;> cases c <;> rfl
  unfold IND_CPA_OneTime_Experiment
  refine EvalDistEq.bind_right _ fun ⟨pk, _⟩ => EvalDistEq.bind_right _ fun ⟨m₁, m₂, st⟩ => ?_
  exact ((hmask pk _).trans (hmask pk _).symm).bind_left _

/-- The one-time pad is perfectly one-time IND-CPA secure: every adversary has advantage zero,
for either key name. -/
theorem pad_advantage_eq_zero (nk : Name .bool .bool) (η : ℕ)
    (adv : IND_CPA_OneTime_Adversary ((encSymbols nk).scheme (encModel pad) η)) :
    IND_CPA_OneTime_Advantage ((encSymbols nk).scheme (encModel pad) η)
      ProbCompRuntime.probComp adv = 0 := by
  rw [IND_CPA_OneTime_Advantage_eq_boolDist,
    evalDistEq_iff_evalDist_eq.1 (pad_experiment_evalDistEq nk η adv false),
    MeasureTheory.Measure.boolDist_self]

/-- The instance with key name `s`, messages `true` and `false`, and the empty context. -/
@[expose] def padInstance : EncInstance decl where
  E := encSymbols .s
  τs := []
  m₀ := .tt
  m₁ := .ff
  u := Env.empty
  order := by decide

/-- The syntactic side conditions of `padInstance` hold: the pads `s` and `r` are distinct, and
the messages and the context use neither. -/
theorem padInstance_syntactic : padInstance.Syntactic := by decide

/-- **Satisfiability.** For the one-time pad, the semantic hypotheses of `Valid.equiv_enc` hold
together against every machine. -/
theorem padInstance_holds :
    padInstance.Holds (fun M => M = encModel pad) fun M => AdvClass.all M :=
  ⟨fun M hM => hM ▸ equalLength .s pad _ _, fun M _ hM A _ => by
    subst hM
    exact negligible_of_zero fun η => pad_advantage_eq_zero .s η _⟩

/-- The rule at the one-time pad: `pk, enc(true; r, pk) ∼ pk, enc(false; r, pk)` against every
distinguisher. -/
theorem valid_enc_pad :
    Valid (fun M => M = encModel pad) (fun M => AdvClass.all M) (Γ := []) []
      (.equiv ((encSymbols .s).challenge .tt Env.empty)
        ((encSymbols .s).challenge .ff Env.empty)) :=
  padInstance.valid padInstance_syntactic padInstance_holds

/-- A one-step derivation by the encryption rule, admitting only `padInstance`. -/
@[expose] def encDerivation :
    Derivation decl (· = padInstance) (Γ := []) []
      (.equiv ((encSymbols .s).challenge .tt Env.empty)
        ((encSymbols .s).challenge .ff Env.empty)) :=
  .equivEnc padInstance rfl (by decide)

/-- `Derivation.sound` applies to `encDerivation`: its hypothesis is `padInstance_holds`. -/
theorem encDerivation_sound :
    Valid (fun M => M = encModel pad) (fun M => AdvClass.all M) (Γ := []) []
      (.equiv ((encSymbols .s).challenge .tt Env.empty)
        ((encSymbols .s).challenge .ff Env.empty)) :=
  encDerivation.sound _ _ fun _ he => he ▸ padInstance_holds

/-- **The IND-CPA hypothesis is needed.** For a scheme that leaks the message, the conclusion
fails against every machine, though the syntactic side conditions hold (`padInstance_syntactic`,
at the same instance) and the messages have equal length (`equalLength`): the ciphertext is the
message. -/
theorem not_valid_enc_leaky :
    ¬ Valid (fun M => M = encModel leaky) (fun M => AdvClass.all M) (Γ := []) []
      (.equiv ((encSymbols .s).challenge .tt Env.empty)
        ((encSymbols .s).challenge .ff Env.empty)) := fun h => by
  have hM := Form.holds_equiv.1 (h (encModel leaky) (encModel_respectsLabels _) rfl Env.empty
    (by simp)) (Machine.input (.succ .zero) Ty.isGround_bool)
    (AdvClass.all_mem_input _ _)
  rw [Machine.test_input] at hM
  refine not_negligible_one (negligible_of_le (fun η => le_of_eq ?_) hM)
  simp only [advantage, EncSymbols.rv_challenge, Env.cons_succ, Env.cons_zero]
  refine (ENNReal.absDiff_zero_right 1).symm.trans (congrArg₂ ENNReal.absDiff ?_ ?_)
  · exact (OracleComp.prEvent_eq_one_of_forall_mem_support _ _ fun _ _ => rfl).symm
  · exact (prEvent_eq_zero_of_forall_not _ _ fun _ h => Bool.noConfusion h).symm

/-- The instance with key name `r`, the coin name. -/
@[expose] def keyIsCoinInstance : EncInstance decl :=
  { padInstance with E := encSymbols .r, m₀ := .tt, m₁ := .ff, u := Env.empty }

/-- The only syntactic side condition that `keyIsCoinInstance` fails is that the key and coin
names be distinct: its messages and its context use neither. -/
theorem keyIsCoin_syntactic :
    ¬ keyIsCoinInstance.E.keyName ≠ keyIsCoinInstance.E.coinName ∧
      keyIsCoinInstance.m₀.AvoidsNames keyIsCoinInstance.E.IsSecret ∧
      keyIsCoinInstance.m₁.AvoidsNames keyIsCoinInstance.E.IsSecret ∧
      keyIsCoinInstance.u.AvoidsNames keyIsCoinInstance.E.IsSecret := by decide

/-- `decide` rejects `keyIsCoinInstance`. -/
theorem not_keyIsCoin_syntactic : ¬ keyIsCoinInstance.Syntactic := by decide

/-- **The names must be distinct.** With the key name equal to the coin name, the one-time pad
meets the IND-CPA hypothesis (`pad_advantage_eq_zero`), and the messages have equal length
(`equalLength`) and use neither name (`keyIsCoin_syntactic`), but the conclusion fails against
every machine: the public key is the pad, and the exclusive or of the two entries is the
message. -/
theorem not_valid_enc_keyIsCoin :
    ¬ Valid (fun M => M = encModel pad) (fun M => AdvClass.all M) (Γ := []) []
      (.equiv ((encSymbols .r).challenge .tt Env.empty)
        ((encSymbols .r).challenge .ff Env.empty)) := fun h => by
  have hM := Form.holds_equiv.1 (h (encModel pad) (encModel_respectsLabels _) rfl Env.empty
    (by simp)) (xorMachine _) (xorMachine_mem _ (AdvClass.all_mem_input _ _))
  rw [xorMachine_test] at hM
  refine not_negligible_one (negligible_of_le (fun η => le_of_eq ?_) hM)
  simp only [advantage, EncSymbols.rv_challenge, Env.cons_succ, Env.cons_zero]
  refine (ENNReal.absDiff_zero_right 1).symm.trans (congrArg₂ ENNReal.absDiff ?_ ?_)
  · refine (OracleComp.prEvent_eq_one_of_forall_mem_support _ _ fun ρ _ => ?_).symm
    change xor (encBit ρ.2 ((encSymbols .r).keySlot (encModel pad) η))
      (xor true (encBit ρ.2 ((encSymbols .r).keySlot (encModel pad) η))) = true
    cases encBit ρ.2 ((encSymbols .r).keySlot (encModel pad) η) <;> rfl
  · refine (prEvent_eq_zero_of_forall_not _ _ fun ρ => ?_).symm
    change xor (encBit ρ.2 ((encSymbols .r).keySlot (encModel pad) η))
      (xor false (encBit ρ.2 ((encSymbols .r).keySlot (encModel pad) η))) ≠ true
    cases encBit ρ.2 ((encSymbols .r).keySlot (encModel pad) η) <;> exact Bool.false_ne_true

/-- The coins `r`, as a context entry in which the public key is free but unused. -/
@[expose] def coinCtx : Vec decl [.loc .bool] [.bool] :=
  Env.cons (FTerm.name Name.r (FTerm.fn (D := decl) ())) Env.empty

/-- The instance with the coins as its context. -/
@[expose] def coinReusedInstance : EncInstance decl where
  E := encSymbols .s
  τs := [.bool]
  m₀ := .tt
  m₁ := .ff
  u := coinCtx
  order := by decide

/-- The only syntactic side condition that `coinReusedInstance` fails is that the context not
use the coin name: the names are distinct, and the messages use neither. -/
theorem coinReused_syntactic :
    coinReusedInstance.E.keyName ≠ coinReusedInstance.E.coinName ∧
      coinReusedInstance.m₀.AvoidsNames coinReusedInstance.E.IsSecret ∧
      coinReusedInstance.m₁.AvoidsNames coinReusedInstance.E.IsSecret ∧
      ¬ coinReusedInstance.u.AvoidsNames coinReusedInstance.E.IsSecret := by decide

/-- `decide` rejects `coinReusedInstance`. -/
theorem not_coinReused_syntactic : ¬ coinReusedInstance.Syntactic := by decide

/-- **The coins must be fresh.** With the coins themselves in the context, the one-time pad has
distinct names and meets the IND-CPA hypothesis (`pad_advantage_eq_zero`), and the messages have
equal length (`equalLength`) and use neither name (`coinReused_syntactic`), but the context reads
the coin coordinate, and the conclusion fails against every machine: the exclusive or of the
ciphertext and the coins is the message. -/
theorem not_valid_enc_coinReused :
    ¬ Valid (fun M => M = encModel pad) (fun M => AdvClass.all M) (Γ := []) []
      (.equiv ((encSymbols .s).challenge .tt coinCtx)
        ((encSymbols .s).challenge .ff coinCtx)) := fun h => by
  have hM := Form.holds_equiv.1 (h (encModel pad) (encModel_respectsLabels _) rfl Env.empty
    (by simp))
    ((xorMachine _).rename (Env.cons (.succ .zero) (Env.cons (.succ (.succ .zero)) Env.empty)))
    ((AdvClass.all _).rename_mem _ (xorMachine_mem _ (AdvClass.all_mem_input _ _)))
  rw [Machine.test_rename, xorMachine_test] at hM
  refine not_negligible_one (negligible_of_le (fun η => le_of_eq ?_) hM)
  simp only [advantage, Distinguisher.rename, Env.rename_apply, EncSymbols.rv_challenge,
    Env.cons_succ, Env.cons_zero]
  refine (ENNReal.absDiff_zero_right 1).symm.trans (congrArg₂ ENNReal.absDiff ?_ ?_)
  · refine (OracleComp.prEvent_eq_one_of_forall_mem_support _ _ fun ρ _ => ?_).symm
    change xor (xor true (encBit ρ.2 ((encSymbols .s).coinSlot (encModel pad) η)))
      (encBit ρ.2 ((encSymbols .s).coinSlot (encModel pad) η)) = true
    cases encBit ρ.2 ((encSymbols .s).coinSlot (encModel pad) η) <;> rfl
  · refine (prEvent_eq_zero_of_forall_not _ _ fun ρ => ?_).symm
    change xor (xor false (encBit ρ.2 ((encSymbols .s).coinSlot (encModel pad) η)))
      (encBit ρ.2 ((encSymbols .s).coinSlot (encModel pad) η)) ≠ true
    cases encBit ρ.2 ((encSymbols .s).coinSlot (encModel pad) η) <;> exact Bool.false_ne_true

end Interop.Squirrel.EncExamples
