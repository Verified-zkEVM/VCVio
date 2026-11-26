/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Squirrel.Derivation
import VCVio.OracleComp.EvalDist.Measure
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# A worked derivation of the encryption rule, and a scheme that leaks lengths

The declaration has a key name `k`, a coin name `r` and a message name `n`, all indexed by
`bool`, and honest symbols for the index, the public key, encryption, the length of a message, and
two message constants `zero` and `one`. A message is a pair of bits, read as a function
`bool → bool`: its length bit at `false` and its payload at `true`. In `model enc` the name `n`
samples a message of length bit `false` with a uniform payload, `zero` and `one` have length bit
`false`, and encryption is `enc`.

* `lpad`, the one-time pad on the payload that copies the length bit into the ciphertext, leaks
  the length. Against every adversary that submits messages of equal length its one-time IND-CPA
  advantage is zero (`lpad_advantage_eq_zero`); the rule's reduction is such an adversary
  (`EncSymbols.encReduction_isAdmissible`). Against an adversary that submits messages of different
  lengths its advantage is one (`lpad_advantage_unequalAdv`), so without the length restriction
  the IND-CPA hypothesis would fail for it.
* `workedDerivation` derives `pk(k), enc(n; r), n ∼ pk(k), enc(zero; r), n` (BC14's example) in
  one step of the encryption rule. Its syntactic side conditions hold by `decide`
  (`workedInstance_syntactic`). `workedDerivation_sound` is its validity from `Derivation.sound`,
  under the two hypotheses that remain: that `n` and `zero` have equal lengths in every admitted
  model, and IND-CPA for the image of the class.
* `valid_worked_lpad`: in the model of `lpad` both hypotheses hold against every machine.
  The length fact holds in the model (`equalLength_n_zero`), and is not assumed.
* `not_valid_leak`: for the scheme that returns the message, the rule's conclusion fails for the
  messages `one` and `zero`, although they have equal lengths and the side conditions hold.

## References

* [BC14] Bana, Comon-Lundh, *A Computationally Complete Symbolic Attacker for Equivalence
  Properties*, CCS 2014: §7.
-/

public section

namespace Interop.Squirrel.WorkedEnc

open IPFunctor IPFunctor.ScopedSignature AsymmEncAlg

/-- Messages and ciphertexts: a length bit and a payload bit, as a function on `bool`. -/
abbrev msg : Ty Empty := .arrow .bool .bool

/-- The key `k`, the coins `r` and the message `n`, indexed by `bool`. -/
inductive Name : Ty Empty → Ty Empty → Type where
  /-- The key name. -/
  | k : Name .bool .bool
  /-- The coin name. -/
  | r : Name .bool .bool
  /-- The message name. -/
  | n : Name .bool msg

/-- The honest symbols. -/
inductive Fn : Ty Empty → Type where
  /-- The index at which names are read. -/
  | idx : Fn .bool
  /-- The public key of a key. -/
  | pk : Fn (.arrow .bool .bool)
  /-- Encryption. -/
  | enc : Fn (.arrow msg (.arrow .bool (.arrow .bool msg)))
  /-- The length bit of a message. -/
  | len : Fn (.arrow msg .bool)
  /-- The message with payload `false`. -/
  | zero : Fn msg
  /-- The message with payload `true`. -/
  | one : Fn msg

-- The decision procedure is exposed, so that `decide` evaluates it in other modules.
@[expose] public section

deriving instance DecidableEq for Name

end

/-- The declaration: three names, the honest symbols, no attacker symbols. -/
@[expose, reducible] def decl : Decl Empty where
  labels b := b.elim
  Name := Name
  nameDom_finite := fun n => match n with | .k | .r | .n => nofun
  finite_names := Finite.of_injective (β := Option Bool)
    (fun n => match n with
      | ⟨_, _, .k⟩ => none | ⟨_, _, .r⟩ => some false | ⟨_, _, .n⟩ => some true)
    fun | ⟨_, _, .k⟩, ⟨_, _, .k⟩, _ => rfl | ⟨_, _, .r⟩, ⟨_, _, .r⟩, _ => rfl
        | ⟨_, _, .n⟩, ⟨_, _, .n⟩, _ => rfl
  Fn := Fn
  Att := Empty
  attTy f := f.elim

/-- Each name reads one bit. A key, a pad and a public key are a bit; the name `n` samples the
message with length bit `false` and its bit as payload. `len` reads the length bit, `zero` and
`one` have length bit `false`, and encryption is `enc`. -/
@[expose] noncomputable def model (enc : (Bool → Bool) → Bool → Bool → Bool → Bool) :
    Model decl where
  lenA _ := 0
  carrier b := b.elim
  nonempty b := b.elim
  coinLen _ _ := 1
  sample η b := match b with
    | .bool => fun c => c 0
    | .arrow .bool .bool => fun c i => i && c 0
    | b => fun _ => Classical.choice (b.nonempty_value (fun b => b.elim) η)
  finite_index _ := fun n => match n with | .k | .r | .n => inferInstanceAs (Finite Bool)
  fn _ τ f := match τ, f with
    | _, .idx => false
    | _, .pk => id
    | _, .enc => enc
    | _, .len => fun m => m false
    | _, .zero => fun _ => false
    | _, .one => fun i => i
  att _ f := f.elim

theorem model_respectsLabels (enc : (Bool → Bool) → Bool → Bool → Bool → Bool) :
    (model enc).RespectsLabels := fun b => b.elim

/-- The pad on the payload, which copies the length bit: it leaks the length. -/
@[expose] def lpad (m : Bool → Bool) (r _ : Bool) : Bool → Bool :=
  fun i => bif i then xor (m true) r else m false

/-- The scheme that returns the message. -/
@[expose] def leak (m : Bool → Bool) (_ _ : Bool) : Bool → Bool := m

/-- The scheme: key `k`, coins `r`, both at `idx`. -/
@[expose, reducible] def encSymbols : EncSymbols decl where
  keyIdx := .bool
  keyTy := .bool
  coinIdx := .bool
  coinTy := .bool
  pkTy := .bool
  msgTy := msg
  cTy := msg
  lenTy := .bool
  nk := Name.k
  ik := Fn.idx
  nr := Name.r
  ir := Fn.idx
  pkOf := Fn.pk
  encOf := Fn.enc
  lenOf := Fn.len

/-! ## Terms and side conditions -/

/-- The message `n`, read at `idx`; the public key is free but unused. -/
@[expose] def nTerm : FTerm decl [.loc .bool] msg := FTerm.name Name.n (FTerm.fn Fn.idx)

/-- The message `zero`. -/
@[expose] def zeroTerm : FTerm decl [.loc .bool] msg := FTerm.fn Fn.zero

/-- The message `one`. -/
@[expose] def oneTerm : FTerm decl [.loc .bool] msg := FTerm.fn Fn.one

/-- The context `n`. -/
@[expose] def ctx : Vec decl [.loc .bool] [msg] := Env.cons nTerm Env.empty

/-- In these models `n` has length bit `false`, as `zero` has. -/
theorem equalLength_n_zero (enc : (Bool → Bool) → Bool → Bool → Bool → Bool) :
    encSymbols.EqualLength (model enc) nTerm zeroTerm := fun _ _ => rfl

/-- `one` and `zero` have the same length. -/
theorem equalLength_one_zero (enc : (Bool → Bool) → Bool → Bool → Bool → Bool) :
    encSymbols.EqualLength (model enc) oneTerm zeroTerm := fun _ _ => rfl

/-! ## A scheme that leaks lengths -/

/-- Encryption with `lpad` is a uniform payload with the message's length bit. -/
theorem lpad_encrypt_evalDistEq (η : ℕ) (pk : Bool) (m : Bool → Bool) :
    (encSymbols.scheme (model lpad) η).encrypt pk m =ᵈ
      ((fun c i => bif i then c else m false) <$> ($ᵗ Bool : ProbComp Bool)) := by
  change (do let rc ← ($ᵗ (Fin 1 → Bool) : ProbComp (Fin 1 → Bool)); pure (lpad m (rc 0) pk)) =ᵈ _
  rw [bind_pure_comp, show (fun rc : Fin 1 → Bool => lpad m (rc 0) pk) =
    (fun c i => bif i then c else m false) ∘ (fun rc : Fin 1 → Bool => xor (m true) (rc 0))
    from rfl, comp_map]
  refine (SampleableType.map_uniformSample_evalDistEq_of_bijective
    ⟨fun a c h => funext fun i => ?_, fun c => ⟨fun _ => xor (m true) c, ?_⟩⟩).map _
  · rw [Subsingleton.elim (α := Fin 1) i 0]
    cases hm : m true <;> cases ha : a 0 <;> cases hc : c 0 <;> simp_all
  · cases m true <;> cases c <;> rfl

/-- For `lpad`, against an adversary that submits messages of equal length, the two branches of
the game are equal in distribution. -/
theorem lpad_experiment_evalDistEq (η : ℕ)
    (adv : IND_CPA_OneTime_Adversary (encSymbols.scheme (model lpad) η))
    (hadv : adv.IsAdmissible ((model lpad).fn η encSymbols.lenOf)) (b : Bool) :
    IND_CPA_OneTime_Experiment adv b =ᵈ IND_CPA_OneTime_Experiment adv true := by
  unfold IND_CPA_OneTime_Experiment
  refine EvalDistEq.bind_right _ fun ⟨pk, _⟩ =>
    OracleComp.EvalDistEq.bind_congr_of_support _ fun ⟨m₁, m₂, st⟩ hz => ?_
  have hl : m₁ false = m₂ false := hadv pk _ hz
  refine EvalDistEq.bind_left ?_ _
  cases b
  · refine (lpad_encrypt_evalDistEq η pk m₂).trans ?_
    rw [← hl]
    exact (lpad_encrypt_evalDistEq η pk m₁).symm
  · exact EvalDistEq.rfl

/-- `lpad` is perfectly one-time IND-CPA secure against adversaries that submit messages of equal
length, though it leaks the length. -/
theorem lpad_advantage_eq_zero (η : ℕ)
    (adv : IND_CPA_OneTime_Adversary (encSymbols.scheme (model lpad) η))
    (hadv : adv.IsAdmissible ((model lpad).fn η encSymbols.lenOf)) :
    IND_CPA_OneTime_Advantage _ ProbCompRuntime.probComp adv = 0 := by
  rw [IND_CPA_OneTime_Advantage_eq_boolDist,
    evalDistEq_iff_evalDist_eq.1 (lpad_experiment_evalDistEq η adv hadv false),
    MeasureTheory.Measure.boolDist_self]

/-- An adversary that submits messages of different lengths and reads the length bit of the
ciphertext. -/
@[expose] def unequalAdv (η : ℕ) :
    IND_CPA_OneTime_Adversary (encSymbols.scheme (model lpad) η) where
  State := Unit
  chooseMessages _ := pure (fun _ => false, fun _ => true, ())
  distinguish _ c := pure (c false)

/-- **The length restriction is needed.** Against an adversary that submits messages of different
lengths, `lpad` has one-time IND-CPA advantage one: VCVio's game, unrestricted, is not met by a
scheme that leaks lengths. -/
theorem lpad_advantage_unequalAdv (η : ℕ) :
    IND_CPA_OneTime_Advantage _ ProbCompRuntime.probComp (unequalAdv η) = 1 := by
  rw [IND_CPA_OneTime_Advantage_eq_boolDist, MeasureTheory.Measure.boolDist]
  simp [IND_CPA_OneTime_Experiment, unequalAdv, EncSymbols.scheme, lpad, model]

/-! ## The worked derivation -/

/-- The instance `pk(k), enc(n; r), n ∼ pk(k), enc(zero; r), n`. -/
@[expose] def workedInstance : EncInstance decl where
  E := encSymbols
  τs := [msg]
  m₀ := nTerm
  m₁ := zeroTerm
  u := ctx
  order := by decide

/-- The syntactic side conditions of the worked instance: the key `k` and the coins `r` are
distinct, and `n`, `zero` and the context use neither. -/
theorem workedInstance_syntactic : workedInstance.Syntactic := by decide

/-- **The worked derivation**: `pk(k), enc(n; r), n ∼ pk(k), enc(zero; r), n`, one step of the
encryption rule. -/
@[expose] def workedDerivation :
    Derivation decl (· = workedInstance) (fun _ => False) (fun _ => True) (Γ := []) []
      (.equiv (encSymbols.challenge nTerm ctx) (encSymbols.challenge zeroTerm ctx)) :=
  .equivEnc workedInstance rfl workedInstance_syntactic

/-- **Soundness of the worked derivation**, from `Derivation.sound`. The syntactic side conditions
are `workedInstance_syntactic`; what remains is that `n` and `zero` have equal lengths in every
admitted model, and IND-CPA for the image of the class under the named reduction. -/
theorem workedDerivation_sound {R : Model decl → Prop} {C : ∀ M : Model decl, AdvClass M}
    (hlen : ∀ M, R M → encSymbols.EqualLength M nTerm zeroTerm)
    (hcpa : ∀ M : Model decl, M.RespectsLabels → R M →
      ∀ A : Machine M [.bool, msg, msg] .bool, (C M).mem A →
        negligible fun η => IND_CPA_OneTime_Advantage (encSymbols.scheme M η)
          ProbCompRuntime.probComp (encSymbols.encReduction nTerm zeroTerm ctx A η)) :
    Valid R C (Γ := []) []
      (.equiv (encSymbols.challenge nTerm ctx) (encSymbols.challenge zeroTerm ctx)) :=
  workedDerivation.sound R C (fun e (he : e = workedInstance) => he ▸ ⟨hlen, hcpa⟩)
    (fun _ h => h.elim) fun _ _ => trivial

/-- **Satisfiability, for a scheme that leaks lengths.** In the model of `lpad`, the length fact
holds and the IND-CPA hypothesis holds against every machine, so the worked derivation's
conclusion is valid there. -/
theorem valid_worked_lpad :
    Valid (· = model lpad) (fun M => AdvClass.all M) (Γ := []) []
      (.equiv (encSymbols.challenge nTerm ctx) (encSymbols.challenge zeroTerm ctx)) :=
  workedDerivation_sound (fun M hM => hM ▸ equalLength_n_zero lpad) fun M _ hM A _ => by
    subst hM
    exact negligible_of_zero fun η => lpad_advantage_eq_zero η _
      (EncSymbols.encReduction_isAdmissible _ _ _ _ _)

/-- The instance with messages `one` and `zero` and the empty context. -/
@[expose] def leakInstance : EncInstance decl where
  E := encSymbols
  τs := []
  m₀ := oneTerm
  m₁ := zeroTerm
  u := Env.empty
  order := by decide

/-- The syntactic side conditions of `leakInstance` hold. -/
theorem leakInstance_syntactic : leakInstance.Syntactic := by decide

/-- **A scheme that leaks the message still fails.** For `leak`, the conclusion of the rule for
the messages `one` and `zero` fails against the machine that queries the ciphertext at `true`,
although they have equal lengths
(`equalLength_one_zero`) and meet the syntactic side conditions (`leakInstance_syntactic`). -/
theorem not_valid_leak :
    ¬ Valid (· = model leak) (fun M => AdvClass.all M) (Γ := []) []
      (.equiv (encSymbols.challenge oneTerm Env.empty)
        (encSymbols.challenge zeroTerm Env.empty)) := fun h => by
  have hM := Form.holds_equiv.1 (h (model leak) (model_respectsLabels _) rfl Env.empty
    (by simp)) (fun _ => Machine.ask ⟨encSymbols.cTy, .succ .zero, Env.cons true Env.empty⟩)
    (AdvClass.all_mem_of_readsBelow_zero (fun _ => Machine.allQueriesSatisfy_ask _ _)
      fun _ => Machine.isQueryBoundP_ask _)
  replace hM : negligible (advantage (fun _ e _ => e _ (.succ .zero) true :
      Distinguisher (model leak) [encSymbols.pkTy, encSymbols.cTy]) _ _) := hM
  refine not_negligible_one (negligible_of_le (fun η => le_of_eq ?_) hM)
  simp only [advantage, EncSymbols.rv_challenge, Env.cons_succ, Env.cons_zero]
  refine (ENNReal.absDiff_zero_right 1).symm.trans (congrArg₂ ENNReal.absDiff ?_ ?_)
  · exact (OracleComp.prEvent_eq_one_of_forall_mem_support _ _ fun _ _ => rfl).symm
  · exact (prEvent_eq_zero_of_forall_not _ _ fun _ h => Bool.noConfusion h).symm

end Interop.Squirrel.WorkedEnc
