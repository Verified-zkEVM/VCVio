/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Squirrel.Chain
public import Interop.Squirrel.Test.PRFExamples
import VCVio.OracleComp.QueryTracking.RandomOracle.IterateCollision
import VCVio.OracleComp.EvalDist.Measure
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# The ratchet's hypotheses are satisfiable, and safety is needed

`cmodel` is a model of the ratchet's declaration (`Interop.Squirrel.Chain.decl`) in which the hash
is a perfect PRF, as in `PRFExamples.pmodel`: messages at `η` are the bitstrings of length `η`, a
key is a whole uniform function table on messages, read from `η · 2^η` bits, and `h(x, k) = k(x)`.
Frames are all bitstrings, `empty_f` is the empty one and `⟨f, x⟩_f` appends `x` to `f`. The pair
is `⟨x, y⟩ = x` with `fst` the identity: in every finite model of `fst(⟨x, y⟩) = x` the pair
depends on its first argument only (`Chain`'s module docstring). `empty` and `att` are the message
of `η` zeros, and the attacker tape has `2^η` bits.

## Satisfiability

* `cmodel_chainR`, `instR_holds`, `instL_holds`, `hyps_valid`: against every machine with
  polynomial read and query bounds (`AdvClass.all`), every hypothesis of `chainPFS_sound` holds in
  `cmodel`: the model conditions, the PRF assumption of every instance, `adv(att)`, and the
  NoCollision lemmas.
* The keys at the positions of a history are the iterates `k^[i] s` of a uniform function table
  from a uniform `s` (`denote_ck`), and two of the first `n` iterates coincide with probability at
  most `n · n / 2^η` (`prEvent_key_iterate_collision_le`, from VCVio's
  `OracleComp.prEvent_iterate_collision_le`). So each NoCollision lemma of a trace with `n` updates
  fails with probability at most `n² · 2^{-η}`: for `n = 2^20` at `η = 128`, at most `2^{-88}`.
* `valid_chainPFS`, `valid_pfsFrame`: `chainPFS_sound` and `pfsFrame_sound` with all their
  hypotheses instantiated: every safe key is secret from the last frame of every trace, and from
  every frame before `Corrupt`, in `cmodel`.

The derivation's conclusion is asymptotic, so no concrete bound on the attacker's success follows
from it here: `Derivation.sound` gives negligibility, and the rules' bounds at each `η` are not
composed along the derivation.

## Safety is needed

`corrupt_not_secret`, `safety_needed`: in the same model, with every hypothesis holding, the
corrupted key is deducible from the frame that outputs it, so `frameC h ⊬ ckC h` fails.

## References

* [CCS26] Hérouard, Jacomme, Koutsos, Lallemand, *Secrecy in Squirrel and the Post-Compromise
  Security of a Ratchet*, CCS 2026: §2 (Fig. 1–2) and App. B.
-/

public section

namespace Interop.Squirrel.ChainModel

open IPFunctor IPFunctor.ScopedSignature Chain
open scoped ENNReal

/-! ## The model -/

/-- Messages at `η` are the bitstrings of length `η`; frames are all bitstrings. -/
@[expose] def carrier : Base → ℕ → Set (List Bool)
  | .msg, η => PRFExamples.carrier () η
  | .frm, _ => Set.univ

theorem carrier_nonempty : ∀ b η, (carrier b η).Nonempty
  | .msg, η => PRFExamples.carrier_nonempty () η
  | .frm, _ => Set.univ_nonempty

/-- The message of `η` zeros. -/
@[expose] def zeros (η : ℕ) : PRFExamples.carrier () η :=
  ⟨List.replicate η false, List.length_replicate⟩

/-- Messages read `η` bits of the honest tape, the key `η · 2^η` bits as a function table, and
Boolean names one bit. The attacker tape has `2^η` bits. `idx` is `false`, `h(x, k) = k(x)`,
`⟨x, y⟩ = x`, `fst` is the identity, `empty` and `att` give `η` zeros, and `⟨f, x⟩_f` appends `x`
to the frame `f`. -/
@[expose] noncomputable def cmodel : Model decl where
  lenA η := 2 ^ η
  carrier := carrier
  nonempty := carrier_nonempty
  coinLen η τ := match τ with
    | .base .msg => η
    | .bool => 1
    | .arrow (.base .msg) (.base .msg) => η * 2 ^ η
    | _ => 0
  sample η τ := match τ with
    | .base .msg => PRFExamples.msgEquiv η
    | .bool => fun c => c 0
    | .arrow (.base .msg) (.base .msg) => PRFExamples.keyEquiv η
    | τ => fun _ => Classical.choice (τ.nonempty_value carrier_nonempty η)
  finite_index _ {a b} n := match a, b, n with
    | _, _, .k => inferInstanceAs (Finite Bool)
    | _, _, .s => inferInstanceAs (Finite Bool)
  fn η {τ} f := match τ, f with
    | _, .idx => false
    | _, .h => fun x k => k x
    | _, .pair => fun x _ => x
    | _, .fst => fun x => x
    | _, .empty => zeros η
    | _, .emptyF => ⟨[], trivial⟩
    | _, .pairF => fun f x => ⟨f.1 ++ x.1, trivial⟩
  att η _ _ := fun _ => zeros η

/-! ## The model conditions -/

/-- `msg` is large in `cmodel`, with `c = 1`: each message is drawn with probability `2^{-η}`. -/
theorem cmodel_isLarge : cmodel.IsLarge msg := by
  refine ⟨1, one_pos, fun η y => le_of_eq ?_⟩
  have hc : ∀ c : cmodel.Coin η msg,
      (cmodel.sample η msg c = y) ↔ c = (PRFExamples.msgEquiv η).symm y :=
    fun c => ((PRFExamples.msgEquiv η).eq_symm_apply).symm
  rw [prEvent_congr _ _ _ hc]
  refine (SampleableType.prEvent_uniformSample_eq_singleton_natCard (α := cmodel.Coin η msg)
    _).trans ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, one_mul,
    ENNReal.rpow_neg, ENNReal.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
  rfl

theorem cmodel_respectsLabels : cmodel.RespectsLabels := fun b l h => by
  cases b
  · subst h
    exact cmodel_isLarge
  · exact h.elim

theorem cmodel_longTapes : cmodel.LongTapes := Model.longTapes_of_two_pow_le fun _ => le_rfl

theorem cmodel_polyCoins : cmodel.PolyCoins msg :=
  ⟨Polynomial.X, fun η => (Polynomial.eval_X (x := η)).ge⟩

theorem cmodel_uniformSampler : cmodel.UniformSampler msg := by
  intro η ms msc
  exact @SampleableType.evalDist_selectElem_eq_uniform _
    (SampleableType.ofEquiv (PRFExamples.msgEquiv η)) ms msc

theorem cmodel_fstPair : FstPair cmodel := fun _ _ _ => rfl

/-- The model conditions of the derivation hold in `cmodel`. -/
theorem cmodel_chainR : ChainR cmodel :=
  ⟨cmodel_uniformSampler, cmodel_longTapes, cmodel_polyCoins, cmodel_fstPair⟩

/-! ## The PRF assumption -/

/-- **A perfect PRF.** In `cmodel`, every distinguisher has PRF advantage zero against `h`: under
a uniform key, `h(·, k) = k` is a uniform function table. -/
theorem cmodel_prfAdv (η : ℕ) (hU : cmodel.UniformSampler P.hTy)
    (adv : PRFScheme.PRFAdversary (P.Dom cmodel η) (P.Rng cmodel η)) :
    P.prfAdv cmodel η hU adv = 0 :=
  have : Finite (P.Dom cmodel η) := (PRFExamples.carrier_finite () η).to_subtype
  P.prfAdv_eq_zero_of_bijective hU (PRFExamples.keyEquiv η).bijective adv

/-- The PRF assumption of every PRF.R instance holds in `cmodel` against all machines. -/
theorem instR_holds (h : List Step) : (instR h).Holds (· = cmodel) (fun M => AdvClass.all M) := by
  intro M _ hM hU g _ t _
  subst hM
  exact negligible_of_zero fun η => cmodel_prfAdv η hU _

/-- The PRF assumption of every PRF.L-sec instance holds in `cmodel` against all machines. -/
theorem instL_holds (h hτ : List Step) :
    (instL h hτ).Holds (· = cmodel) (fun M => AdvClass.all M) := by
  intro M _ hM hU g _
  subst hM
  exact ⟨negligible_of_zero fun η => cmodel_prfAdv η hU _,
    negligible_of_zero fun η => cmodel_prfAdv η hU _⟩

/-! ## `adv(att)` -/

/-- `adv(att)` holds in `cmodel` against all machines: `att` is the constant `empty`, which the
machine `AdvMachine.ofFn` computes. -/
theorem valid_advAtt {Θ : List (Form decl [])} :
    Valid (· = cmodel) (fun M => AdvClass.all M) Θ advAtt := fun M _ hM env _ => by
  subst hM
  refine Form.holds_adv.2 ⟨AdvMachine.ofFn (τs := [frm]) (Fn.empty : decl.Fn _) (Nat.zero_le 1),
    (AdvClass.all _).fn_mem _ ((AdvClass.all _).rename_mem _ ((AdvClass.all _).project_mem _ _)),
    fun η ρ => funext fun f => ?_⟩
  exact (AdvMachine.appVals_eval_ofFn (M := cmodel) (τs := [frm]) (ρa := ρ.1)
    (Fn.empty : decl.Fn _) (Nat.zero_le 1) (Env.cons f Env.empty)).symm

/-! ## NoCollision -/

/-- In `cmodel` the chain key at a history is the key table iterated from `s`, once per update:
`⟨x, y⟩ = x` and `h(x, k) = k(x)`. -/
theorem denote_ck (C : AdvClass cmodel) (env : Env (Kind.Value cmodel) []) (η : ℕ)
    (ρ : cmodel.Tape η) : ∀ h : List Step,
    (P.close (ck h)).denote (fullInterp cmodel C) env η ρ =
      (P.keyVal cmodel η ρ.2)^[(aSteps h).length] (cmodel.nameAt (D := decl) Name.s Fn.idx η ρ)
  | [] => (congrArg (fun t : FTerm decl [] msg => t.denote (fullInterp cmodel C) env η ρ)
      close_sO).trans rfl
  | .A :: h => by
    have e : (P.close (ck (.A :: h))).denote (fullInterp cmodel C) env η ρ =
        P.keyVal cmodel η ρ.2 ((P.close (ck h)).denote (fullInterp cmodel C) env η ρ) := by
      change (P.hashTerm (P.close (msgA h))).denote (fullInterp cmodel C) env η ρ = _
      rw [P.denote_hashTerm, msgA, close_pairO]
      rfl
    rw [e, denote_ck C env η ρ h]
    exact (Function.iterate_succ_apply' _ _ _).symm
  | .ROM :: h => denote_ck C env η ρ h

/-- A position before an update of `h` has fewer updates than `h`. -/
private theorem length_aSteps_lt {h' : List Step} :
    ∀ {h : List Step}, h' ∈ aSteps h → (aSteps h').length < (aSteps h).length
  | [], hh' => absurd hh' List.not_mem_nil
  | .A :: h, hh' => by
    rcases List.mem_cons.1 hh' with rfl | hh'
    · exact Nat.lt_succ_self _
    · exact (length_aSteps_lt hh').trans (Nat.lt_succ_self _)
  | .ROM :: h, hh' => length_aSteps_lt (h := h) hh'

/-- At `η`, the iterates of the key table from `s` up to `n` repeat with probability at most
`n · n / 2^η`: the key coordinate is resampled (`SampleableType.prEvent_uniformSample_prod_update`),
its table is a uniform function (`PRFExamples.keyEquiv` is a bijection), and VCVio's
`OracleComp.prEvent_iterate_collision_le` bounds the repeat for each value of `s`. -/
theorem prEvent_key_iterate_collision_le (η n : ℕ) :
    Pr{let ρ ← $ᵗ (cmodel.Tape η)}[∃ a b, a < b ∧ b ≤ n ∧
      (P.keyVal cmodel η ρ.2)^[a] (cmodel.nameAt (D := decl) Name.s Fn.idx η ρ) =
        (P.keyVal cmodel η ρ.2)^[b] (cmodel.nameAt (D := decl) Name.s Fn.idx η ρ)] ≤
      n * (n * ((2 ^ η : ℕ) : ℝ≥0∞)⁻¹) := by
  classical
  have := decl.finite_names
  have : ∀ n : (a : Ty Base) × (b : Ty Base) × decl.Name a b,
      Finite (n.1.Value cmodel.carrier η) := fun n => cmodel.finite_index η n.2.2
  rw [← SampleableType.prEvent_uniformSample_prod_update (β := cmodel.TapeA η)
    (R := fun k : cmodel.Slot η => cmodel.Coin η k.1.2.1) (P.keySlot cmodel η)]
  have hs : ∀ (c : cmodel.Coin η keyT) (ρ : cmodel.Tape η),
      cmodel.nameAt (D := decl) Name.s Fn.idx η
        (ρ.1, Function.update ρ.2 (P.keySlot cmodel η) c) =
        cmodel.nameAt (D := decl) Name.s Fn.idx η ρ := fun c ρ => by
    have hne : cmodel.nameSlot (D := decl) Name.s Fn.idx η ≠ P.keySlot cmodel η :=
      fun h => by cases h
    exact congrArg (cmodel.sample η msg) (Function.update_of_ne hne c ρ.2)
  have hk : ∀ (c : cmodel.Coin η keyT) (ρ : cmodel.Tape η),
      P.keyVal cmodel η (Function.update ρ.2 (P.keySlot cmodel η) c) =
        PRFExamples.keyEquiv η c := fun c ρ => by
    change cmodel.sample η keyT
      (Function.update ρ.2 (P.keySlot cmodel η) c (P.keySlot cmodel η)) = _
    rw [Function.update_self]
    rfl
  simp only [hs, hk]
  refine (SampleableType.prEvent_uniformSample_prod (α := cmodel.Coin η keyT)
    (β := cmodel.Tape η) fun z => ∃ a b, a < b ∧ b ≤ n ∧
      (PRFExamples.keyEquiv η z.1)^[a] (cmodel.nameAt (D := decl) Name.s Fn.idx η z.2) =
        (PRFExamples.keyEquiv η z.1)^[b] (cmodel.nameAt (D := decl) Name.s Fn.idx η z.2)).symm
    |>.trans_le ?_
  refine SampleableType.prEvent_uniformSample_prod_le_of_forall_snd _ fun ρ => ?_
  have : Finite (PRFExamples.carrier () η) := (PRFExamples.carrier_finite () η).to_subtype
  let : SampleableType (PRFExamples.carrier () η) :=
    SampleableType.ofEquiv (PRFExamples.msgEquiv η)
  let : SampleableType (PRFExamples.carrier () η → PRFExamples.carrier () η) :=
    SampleableType.ofEquiv (PRFExamples.keyEquiv η)
  refine ((SampleableType.prEvent_uniformSample_comp_of_bijective
    (PRFExamples.keyEquiv η).bijective (fun g => ∃ a b, a < b ∧ b ≤ n ∧
      g^[a] (cmodel.nameAt (D := decl) Name.s Fn.idx η ρ) =
        g^[b] (cmodel.nameAt (D := decl) Name.s Fn.idx η ρ))).trans_le
    (OracleComp.prEvent_iterate_collision_le _ n)).trans (le_of_eq ?_)
  rw [div_eq_mul_inv, PRFExamples.natCard_carrier]

/-- **The NoCollision lemmas hold in `cmodel`**: `ck(h') ≠ ck(h)` for a position `h'` before an
update of `h`, except with probability at most `n · n / 2^η`, `n` the number of updates of `h`. -/
theorem valid_noCollision {h h' : List Step} (hh' : h' ∈ aSteps h) {Θ : List (Form decl [])} :
    Valid (· = cmodel) (fun M => AdvClass.all M) Θ (.box (noCollision h' h)) :=
  fun M _ hM env _ => by
  subst hM
  refine Form.holds_box.2 (negligible_of_le (fun η => ?_)
    (negligible_const_mul (negligible_two_rpow_neg_mul one_pos)
      (c := ((aSteps h).length : ℝ≥0∞) * (aSteps h).length)
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _))))
  refine (prEvent_mono _ _ _ fun ρ hρ => ?_).trans
    ((prEvent_key_iterate_collision_le η (aSteps h).length).trans (le_of_eq ?_))
  · refine ⟨_, _, length_aSteps_lt hh', le_rfl, ?_⟩
    rw [← denote_ck (AdvClass.all cmodel) env η ρ h', ← denote_ck (AdvClass.all cmodel) env η ρ h]
    by_contra hne
    exact Bool.eq_false_iff.1 hρ (FTerm.denote_not_eq_eq_true.2 hne)
  · rw [one_mul, ENNReal.rpow_neg, ENNReal.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat, mul_assoc]

/-- A formula valid under hypotheses that are each valid is valid. -/
private theorem valid_of_forall_valid {R : Model decl → Prop} {C : ∀ M : Model decl, AdvClass M}
    {Θ : List (Form decl [])} {F : Form decl []} (hΘ : ∀ θ ∈ Θ, Valid R C [] θ)
    (h : Valid R C Θ F) : Valid R C [] F := fun M hl hR env _ =>
  h M hl hR env fun θ hθ => hΘ θ hθ M hl hR env fun _ h => nomatch h

/-! ## Satisfiability -/

/-- **Every hypothesis of the derivation holds in `cmodel`**, against all machines: `adv(att)` and
the NoCollision lemmas. -/
theorem hyps_valid (tr : Trace) :
    ∀ θ ∈ hyps tr, Valid (· = cmodel) (fun M => AdvClass.all M) [] θ := by
  rcases tr with ⟨h, _ | _⟩
  · intro θ hθ
    rw [hyps, List.mem_singleton] at hθ
    exact hθ ▸ valid_advAtt
  · intro θ hθ
    rcases List.mem_cons.1 hθ with rfl | hθ
    · exact valid_advAtt
    · obtain ⟨h', hh', rfl⟩ := List.mem_map.1 hθ
      exact valid_noCollision hh'

/-- **Forward secrecy in `cmodel`**: `chainPFS_sound` with every hypothesis instantiated
(`cmodel_chainR`, `instR_holds`, `instL_holds`, `hyps_valid`). For every trace and every safe
position, the last frame does not deduce the key, against every machine with polynomial read and
query bounds. -/
theorem valid_chainPFS (tr : Trace) {hτ : List Step} (hs : hτ <:+ tr.hist) :
    Valid (· = cmodel) (fun M => AdvClass.all M) []
      (.nonDed (Env.cons (P.close tr.frame) Env.empty) (P.close (ck hτ)) order_frame) :=
  valid_of_forall_valid (hyps_valid tr) (chainPFS_sound tr hs _ _
    (fun _ hM => hM ▸ cmodel_chainR) instR_holds instL_holds)

/-- **Forward secrecy before `Corrupt` in `cmodel`**: `pfsFrame_sound` with every hypothesis
instantiated, for any two positions before `Corrupt`. -/
theorem valid_pfsFrame (tr : Trace) (hτ h' : List Step) :
    Valid (· = cmodel) (fun M => AdvClass.all M) []
      (.nonDed (Env.cons (P.close (frame h')) Env.empty) (P.close (ck hτ)) order_frame) :=
  valid_of_forall_valid (hyps_valid tr) (pfsFrame_sound tr hτ h' _ _
    (fun _ hM => hM ▸ cmodel_chainR) instR_holds instL_holds)

/-! ## The corrupted key is not secret -/

/-- The last `η` bits of a bitstring, as a message. -/
@[expose] def lastMsg (η : ℕ) (l : List Bool) : PRFExamples.carrier () η :=
  ⟨List.ofFn fun i : Fin η => l.getD (l.length - η + i) false, List.length_ofFn⟩

theorem lastMsg_append (η : ℕ) (l : List Bool) (x : PRFExamples.carrier () η) :
    lastMsg η (l ++ x.1) = x := by
  obtain ⟨x, hx⟩ := x
  change x.length = η at hx
  subst hx
  refine Subtype.ext (List.ext_get (by simp [lastMsg]) fun i h₁ h₂ => ?_)
  simp only [lastMsg, List.get_eq_getElem, List.getElem_ofFn, List.length_append,
    Nat.add_sub_cancel]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left, List.getElem?_eq_getElem h₂, Option.getD_some]

/-- The attacker machine that returns the last output of the frame it is given. -/
@[expose] noncomputable def lastOutput : AdvMachine cmodel [frm] msg :=
  fun η => (fun f => lastMsg η f.1) <$> Machine.fetch (M := cmodel) (η := η) .zero trivial

theorem lastOutput_mem : (AdvClass.all cmodel).mem lastOutput :=
  AdvClass.all_mem_of_readsBelow_zero
    (fun _ => (OracleComp.allQueriesSatisfy_map_iff _ _ _).2
      (Machine.allQueriesSatisfy_fetch _ _ _)) (n := 1)
    fun _ => (OracleComp.isQueryBoundP_map_iff _ _ _).2 (Machine.isQueryBoundP_fetch _ _)

theorem appVals_eval_lastOutput {η : ℕ} (ρa : cmodel.TapeA η) (f : frm.Value cmodel.carrier η) :
    Ty.appVals (lastOutput.eval η ρa) (Env.cons f Env.empty) = lastMsg η f.1 := by
  rw [AdvMachine.appVals_eval]
  change evalWithAnswerFn _ ((fun f : frm.Value cmodel.carrier η => lastMsg η f.1) <$>
    Machine.fetch (M := cmodel) (η := η) (τs := [frm] ++ []) .zero trivial) = _
  exact (evalWithAnswerFn_map _ _ _).trans
    (congrArg (fun f : frm.Value cmodel.carrier η => lastMsg η f.1)
      (Machine.evalWithAnswerFn_fetch _ _ _))

/-- **Safety is needed.** In `cmodel`, where every hypothesis of `chainPFS_sound` holds, the key
output at `Corrupt` is deducible from the frame that outputs it: `lastOutput` returns it on every
tape, so `frameC h ⊬ ckC h` fails. -/
theorem corrupt_not_secret (h : List Step) :
    ¬ Valid (· = cmodel) (fun M => AdvClass.all M) []
      (.nonDed (Env.cons (P.close (frameC h)) Env.empty) (P.close (ckC h)) order_frame) := by
  intro hv
  have hN := Form.holds_nonDed.1 (hv cmodel cmodel_respectsLabels rfl Env.empty (by simp))
  refine not_negligible_one (negligible_of_le (fun η => le_of_eq ?_) (hN _ lastOutput_mem))
  refine ((prEvent_congr _ _ (fun _ => True) fun ρ => iff_true_intro ?_).trans
    (OracleComp.prEvent_true_eq_one _)).symm
  rw [Vec.rv_single, VecRV.single, appVals_eval_lastOutput, frameC, close_pairFO]
  exact lastMsg_append η _ _

/-- **The safety condition is needed.** For a trace that corrupts after `h`, every hypothesis of
`chainPFS_sound` holds in `cmodel` against all machines (the model conditions, the PRF assumption
of every instance, `adv(att)` and the NoCollision lemmas), and the key output at `Corrupt`, the one
position that is not safe, is not secret from the last frame. -/
theorem safety_needed (h : List Step) :
    ChainR cmodel ∧ (∀ h', (instR h').Holds (· = cmodel) (fun M => AdvClass.all M)) ∧
      (∀ h' hτ, (instL h' hτ).Holds (· = cmodel) (fun M => AdvClass.all M)) ∧
      (∀ θ ∈ hyps ⟨h, true⟩, Valid (· = cmodel) (fun M => AdvClass.all M) [] θ) ∧
      ¬ Valid (· = cmodel) (fun M => AdvClass.all M) []
        (.nonDed (Env.cons (P.close (Trace.frame ⟨h, true⟩)) Env.empty) (P.close (ckC h))
          order_frame) :=
  ⟨cmodel_chainR, instR_holds, instL_holds, hyps_valid _, corrupt_not_secret h⟩

end Interop.Squirrel.ChainModel
