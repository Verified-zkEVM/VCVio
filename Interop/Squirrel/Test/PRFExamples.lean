/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Squirrel.Derivation
import VCVio.OracleComp.EvalDist.Measure
import VCVio.OracleComp.Constructions.SampleableType.Measure
import Mathlib.Data.Set.Finite.List

/-!
# Checks of the compiled reading and of the PRF rules

The declaration has one base type `msg`, labelled `large`, and the type of keys `msg → msg`; a key
name `k : bool → (msg → msg)`, message names `n`, `s`, `r : bool → msg`; the honest index `idx`, a
constant message `c`, a predicate `p : msg → bool` and the hash `h : msg → (msg → msg) → msg`. In
`pmodel`, `msg` at `η` is the bitstrings of length `η`, the attacker tape has `2^η` bits, a message
name draws a uniform message, a key is a whole uniform function table on messages, read from
`η · 2^η` bits, `p` is constantly `false` and `h(x, k) = k(x)`. So `h` is a **perfect PRF**: under a
uniform key it is a uniform function, and every distinguisher has PRF advantage zero
(`pmodel_prfAdv`).

## The compiled reading

* `runLog_call_c`, `lower_call_c`: the compiled program of `o_h^k(c)` makes exactly one query, to
  the hash oracle at `c`, and returns the hash of `c` under the key.
* `lower_call_r`: adequacy (`PRFSymbols.lower_evalWithAnswerFn_denoteCBV`) at `o_h^k(r)`, whose
  `⊢pptm` premise `decide` checks.
* `adequacy_needs_pptm`: the local quantifier `∀ x. p(x)` is outside `⊢pptm` (`decide` rejects
  it), and there the compiled reading returns `true` while the term is `false`. So adequacy needs
  its `⊢pptm` premise.

## The PRF rules

* `prfWorked`, `prfWorked_sound`: from `[ψ_msg]`, derive `h(r, k) ⊬ s` by PRF-Simple, from
  `⊬ s` (FreshR); G.PRF inside it uses the fresh name `n`, and `decide` checks its syntactic side
  conditions (`inst_syntactic`). `valid_prfWorked`: in `pmodel`, against all machines
  (`AdvClass.all`), every hypothesis of G.PRF and FreshL holds jointly, and the conclusion holds;
  `valid_gprf` is G.PRF at the same instance.
* `gprf_needs_psiMsg`: with `u⃗ = h(c, k)` and `m = c`, every syntactic side condition and the PRF
  hypothesis hold, `ψ_msg` is `c ≠ c` and fails, and the conclusion `h(c, k), h(c, k) ∼ h(c, k), n`
  fails.
* `gprf_needs_psiKey`: with `u⃗ = k(c)` and `m = c`, the key occurs outside a hash, `ψ_msg` holds
  (there is no call), every other side condition and the PRF hypothesis hold, and
  `k(c), h(c, k) ∼ k(c), n` fails, since `k(c) = h(c, k)` in `pmodel`.

Both countermodels use the distinguisher comparing the two entries (`Machine.eqTest`): on the left
they are equal, on the right the second is a fresh name, equal to the first with probability at
most `2^{-η}` (`deduceAdv_nameAt_le`).

## References

* [LICS23] Baelde, Koutsos, Lallemand, *A Higher-Order Indistinguishability Logic for
  Cryptographic Reasoning*, LICS 2023: Fig. 10 and the rule G.PRF.
* [CCS26] Hérouard, Jacomme, Koutsos, Lallemand, *Secrecy in Squirrel and the Post-Compromise
  Security of a Ratchet*, CCS 2026: Fig. 11 and App. C.3.
-/

public section

namespace Interop.Squirrel.PRFExamples

open IPFunctor IPFunctor.ScopedSignature OracleComp

/-- The base type of messages. -/
abbrev msg : Ty Unit := .base ()

/-- The type of keys: functions on messages. -/
abbrev keyT : Ty Unit := .arrow msg msg

/-- The key name and three message names, each indexed by a Boolean. -/
inductive Name : Ty Unit → Ty Unit → Type where
  /-- The key name. -/
  | k : Name .bool keyT
  /-- The fresh name of G.PRF. -/
  | n : Name .bool msg
  /-- A secret. -/
  | s : Name .bool msg
  /-- A message. -/
  | r : Name .bool msg

/-- The honest symbols: an index, a constant message, a predicate and the hash. -/
inductive Fn : Ty Unit → Type where
  /-- The index at which names are read. -/
  | idx : Fn .bool
  /-- A constant message. -/
  | c : Fn msg
  /-- A predicate on messages. -/
  | p : Fn (.arrow msg .bool)
  /-- The keyed hash. -/
  | h : Fn (.arrow msg (.arrow keyT msg))

-- The decision procedure is exposed, so that `decide` evaluates it in other modules.
@[expose] public section

deriving instance DecidableEq for Name

end

/-- `msg` is labelled `large`; there are no attacker symbols. -/
@[expose, reducible] def decl : Decl Unit where
  labels _ l := l = .large
  Name := Name
  nameDom_finite := fun n => match n with | .k | .n | .s | .r => nofun
  finite_names := Finite.of_injective (β := Bool × Bool)
    (fun n => match n with
      | ⟨_, _, .k⟩ => (false, false) | ⟨_, _, .n⟩ => (false, true)
      | ⟨_, _, .s⟩ => (true, false) | ⟨_, _, .r⟩ => (true, true))
    fun | ⟨_, _, .k⟩, ⟨_, _, .k⟩, _ => rfl | ⟨_, _, .n⟩, ⟨_, _, .n⟩, _ => rfl
        | ⟨_, _, .s⟩, ⟨_, _, .s⟩, _ => rfl | ⟨_, _, .r⟩, ⟨_, _, .r⟩, _ => rfl
  Fn := Fn
  Att := Empty
  attTy := Empty.elim

/-- Messages at `η` are the bitstrings of length `η`. -/
@[expose] def carrier : Unit → ℕ → Set (List Bool) := fun _ η => {l | l.length = η}

theorem carrier_finite (b : Unit) (η : ℕ) : (carrier b η).Finite := List.finite_length_eq Bool η

theorem carrier_nonempty (b : Unit) (η : ℕ) : (carrier b η).Nonempty :=
  ⟨List.replicate η false, List.length_replicate⟩

/-- A bit block of length `η` as a message. -/
@[expose] def msgEquiv (η : ℕ) : (Fin η → Bool) ≃ carrier () η where
  toFun c := ⟨List.ofFn c, List.length_ofFn⟩
  invFun l := fun i => l.1.get (i.cast l.2.symm)
  left_inv c := funext fun i => by simp
  right_inv l := Subtype.ext (by
    obtain ⟨l, hl⟩ := l
    change l.length = η at hl
    subst hl
    exact List.ofFn_get l)

theorem natCard_carrier (η : ℕ) : Nat.card (carrier () η) = 2 ^ η := by
  rw [← Nat.card_congr (msgEquiv η), Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_bool,
    Nat.card_eq_fintype_card, Fintype.card_fin]

/-- A bit block of length `η · 2^η` as a function table on messages. -/
@[expose] noncomputable def keyEquiv (η : ℕ) :
    (Fin (η * 2 ^ η) → Bool) ≃ (carrier () η → carrier () η) :=
  have := (carrier_finite () η).to_subtype
  Classical.choice (Finite.card_eq.1 (by
    rw [Nat.card_fun, Nat.card_fun, natCard_carrier, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, Fintype.card_bool, Fintype.card_fin, ← pow_mul, mul_comm]))

/-- Message names read `η` bits, the key name `η · 2^η` bits as a function table, and Boolean
names one bit. The attacker tape has `2^η` bits. `idx` is `false`, `c` is the message of `η` zeros,
`p` is constantly `false` and `h(x, k) = k(x)`. -/
@[expose] noncomputable def pmodel : Model decl where
  lenA η := 2 ^ η
  carrier := carrier
  nonempty := carrier_nonempty
  coinLen η τ := match τ with
    | .base _ => η
    | .bool => 1
    | .arrow (.base _) (.base _) => η * 2 ^ η
    | .arrow _ _ => 0
  sample η τ := match τ with
    | .base _ => msgEquiv η
    | .bool => fun c => c 0
    | .arrow (.base _) (.base _) => keyEquiv η
    | .arrow a b => fun _ => Classical.choice ((Ty.arrow a b).nonempty_value carrier_nonempty η)
  finite_index η {a _} _ := a.finite_value_of_finite carrier_finite η
  fn η {τ} f := match τ, f with
    | _, .idx => false
    | _, .c => ⟨List.replicate η false, List.length_replicate⟩
    | _, .p => fun _ => false
    | _, .h => fun x k => k x
  att _ f := f.elim

/-- `msg` is large in `pmodel`, with `c = 1`: each message is drawn with probability `2^{-η}`. -/
theorem pmodel_isLarge : pmodel.IsLarge msg := by
  refine ⟨1, one_pos, fun η y => le_of_eq ?_⟩
  have hc : ∀ c : pmodel.Coin η msg, (pmodel.sample η msg c = y) ↔ c = (msgEquiv η).symm y :=
    fun c => ((msgEquiv η).eq_symm_apply).symm
  rw [prEvent_congr _ _ _ hc]
  refine (SampleableType.prEvent_uniformSample_eq_singleton_natCard (α := pmodel.Coin η msg)
    _).trans ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, one_mul,
    ENNReal.rpow_neg, ENNReal.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
  rfl

theorem pmodel_respectsLabels : pmodel.RespectsLabels := fun _ _ h => by
  subst h
  exact pmodel_isLarge

theorem pmodel_longTapes : pmodel.LongTapes := Model.longTapes_of_two_pow_le fun _ => le_rfl

/-- Messages read `η` bits of the honest tape. -/
theorem pmodel_polyCoins : pmodel.PolyCoins msg :=
  ⟨Polynomial.X, fun η => (Polynomial.eval_X (x := η)).ge⟩

/-- Message names are uniform: their sampler is a bijection of bit blocks with messages. -/
theorem pmodel_uniformSampler : pmodel.UniformSampler msg := by
  intro η ms msc
  exact @SampleableType.evalDist_selectElem_eq_uniform _ (SampleableType.ofEquiv (msgEquiv η))
    ms msc

/-! ## The keyed hash -/

/-- The keyed hash `h(·, k)` of the declaration. -/
abbrev P : PRFSymbols decl where
  keyIdx := .bool
  keyTy := keyT
  msgTy := msg
  hTy := msg
  nk := Name.k
  ik := Fn.idx
  hOf := Fn.h

/-- **A perfect PRF.** In `pmodel`, every distinguisher has PRF advantage zero against `h`: under a
uniform key, `h(·, k) = k` is a uniform function table. -/
theorem pmodel_prfAdv (η : ℕ) (hU : pmodel.UniformSampler P.hTy)
    (adv : PRFScheme.PRFAdversary (P.Dom pmodel η) (P.Rng pmodel η)) :
    P.prfAdv pmodel η hU adv = 0 :=
  have : Finite (P.Dom pmodel η) := (carrier_finite () η).to_subtype
  P.prfAdv_eq_zero_of_bijective hU (keyEquiv η).bijective adv

/-! ## Terms -/

/-- A message name at the index `idx`, as a term with calls. -/
@[expose] def nmO (x : Name .bool msg) : OTerm P [] msg :=
  OTerm.name (D := decl) x (OTerm.fn (D := decl) Fn.idx)

/-- The constant message `c`. -/
@[expose] def cO : OTerm P [] msg := OTerm.fn (D := decl) Fn.c

/-- The fresh name `n` at `idx`. -/
@[expose] def nT : FTerm decl [] msg := FTerm.name (D := decl) Name.n (FTerm.fn (D := decl) Fn.idx)

/-- `n(idx)` closed up from its term with calls. -/
theorem close_nmO (x : Name .bool msg) :
    P.close (nmO x) = FTerm.name (D := decl) x (FTerm.fn (D := decl) Fn.idx) :=
  (PRFSymbols.close_name _ _).trans (congrArg _ (PRFSymbols.close_fn _))

/-! ## The compiled reading on small terms -/

/-- The compiled program of `o_h^k(c)` makes one query: to the hash oracle, at `c`. -/
theorem runLog_call_c (η : ℕ) (ρ : pmodel.Tape η) (kv : P.keyTy.Value pmodel.carrier η) :
    runLog (P.answer pmodel η ρ kv) ((OTerm.call cO).denoteCBV (P.cbvInterp pmodel η) Env.empty) =
      [⟨Sum.inr (pmodel.fn η Fn.c), kv (pmodel.fn η Fn.c)⟩] := by
  simp only [OTerm.call, cO, OTerm.fn, Term.denoteCBV_node, PRFSymbols.cbvInterp,
    CBVInterpretation.sum, PRFSymbols.cbvCall, PRFSymbols.cbvLocal, pure_bind,
    PRFSymbols.askHash, runLog_map, runLog_query]
  rfl

/-- The run of the compiled program of `o_h^k(c)` is the hash of `c` under the key. -/
theorem lower_call_c (η : ℕ) (ρ : pmodel.Tape η) (kv : P.keyTy.Value pmodel.carrier η) :
    pmodel.lower (m := OracleComp (P.Iface pmodel η)) η msg (evalWithAnswerFn
      (P.answer pmodel η ρ kv) ((OTerm.call cO).denoteCBV (P.cbvInterp pmodel η) Env.empty)) =
        kv (pmodel.fn η Fn.c) := by
  simp only [OTerm.call, cO, OTerm.fn, Term.denoteCBV_node, PRFSymbols.cbvInterp,
    CBVInterpretation.sum, PRFSymbols.cbvCall, PRFSymbols.cbvLocal, pure_bind,
    PRFSymbols.askHash, evalWithAnswerFn_map]
  rfl

/-- **Adequacy at `o_h^k(r)`.** Its `⊢pptm` premise holds by `decide`, and the run of the compiled
program is the hash of `r`'s value under the key. -/
theorem lower_call_r (η : ℕ) (ρ : pmodel.Tape η) (kv : P.keyTy.Value pmodel.carrier η) :
    pmodel.lower (m := OracleComp (P.Iface pmodel η)) η msg (evalWithAnswerFn
      (P.answer pmodel η ρ kv)
      ((OTerm.call (nmO Name.r)).denoteCBV (P.cbvInterp pmodel η) Env.empty)) =
        kv (pmodel.name η Name.r false ρ.2) :=
  PRFSymbols.lower_evalWithAnswerFn_denoteCBV (Ty.isGround_base ()) _ (by decide)

/-- `∀ x. p(x)`, as a term with calls. -/
@[expose] def allP : OTerm P [] .bool := OTerm.all (OTerm.fn (D := decl) Fn.p)

/-- **Adequacy needs `⊢pptm`.** The local quantifier `∀ x. p(x)` is outside the fragment, and the
compiled reading returns `true` where the term is `false`. -/
theorem adequacy_needs_pptm : ¬ P.Pptm allP ∧ ∀ η (ρ : pmodel.Tape η) kv,
    pmodel.lower (m := OracleComp (P.Iface pmodel η)) η .bool (evalWithAnswerFn
      (P.answer pmodel η ρ kv) (allP.denoteCBV (P.cbvInterp pmodel η) Env.empty)) ≠
        allP.denote (P.ointerp pmodel η ρ kv) Env.empty := by
  refine ⟨by decide, fun η ρ kv => ?_⟩
  have h1 : pmodel.lower (m := OracleComp (P.Iface pmodel η)) η .bool (evalWithAnswerFn
      (P.answer pmodel η ρ kv) (allP.denoteCBV (P.cbvInterp pmodel η) Env.empty)) = true := by
    simp only [allP, OTerm.all, OTerm.app, OTerm.fn, Term.denoteCBV_node, PRFSymbols.cbvInterp,
      CBVInterpretation.sum, PRFSymbols.cbvLocal]
    rfl
  have h2 : allP.denote (P.ointerp pmodel η ρ kv) Env.empty = false := by
    change @decide (∀ x : carrier () η, false = true) (Classical.propDecidable _) = false
    obtain ⟨y, hy⟩ := carrier_nonempty () η
    exact @decide_eq_false _ (Classical.propDecidable _) fun h => Bool.false_ne_true (h ⟨y, hy⟩)
  rw [h1, h2]
  exact nofun

/-! ## The equality test against a fresh name -/

/-- In `pmodel`, against all machines, a vector whose two entries are surely equal is
distinguished from one whose second entry is `n(idx)` and whose first does not read `n(idx)`'s
coordinate: the equality test succeeds always on the first, and with probability at most
`2^{-cη}` on the second. -/
theorem not_indist_eq_name {u v : VecRV pmodel [msg, msg]}
    (hu : ∀ η ρ, u η ρ _ .zero = u η ρ _ (.succ .zero))
    (hv : ∀ η ρ, v η ρ _ (.succ .zero) = pmodel.nameAt (D := decl) Name.n Fn.idx η ρ)
    (hf : pmodel.FreshAt (pmodel.nameSlot (D := decl) Name.n Fn.idx) fun η ρ => v η ρ _ .zero) :
    ¬ (AdvClass.all pmodel).Indist u v := by
  intro h
  have hA := h (Machine.eqTest (Ty.isGround_base ())) ((AdvClass.all _).eqTest_mem _)
  obtain ⟨c, hc, hle⟩ := pmodel_isLarge
  refine not_negligible_one (negligible_of_le (fun η => ?_)
    (negligible_add hA (negligible_two_rpow_neg_mul hc)))
  have htest : ∀ (e : Vals pmodel η [msg, msg]) ρa,
      (Machine.eqTest (Ty.isGround_base ()) : Machine pmodel [msg, msg] .bool).test η e ρa =
        @decide (e _ .zero = e _ (.succ .zero)) (Ty.decEqValue (Ty.isGround_base ()) _ _) :=
    fun e ρa => Machine.run_eqTest _ e
  have h1 : Pr{let ρ ← $ᵗ (pmodel.Tape η)}[(Machine.eqTest (Ty.isGround_base ()) :
      Machine pmodel [msg, msg] .bool).test η (u η ρ) ρ.1 = true] = 1 :=
    (prEvent_congr _ _ (fun _ => True) fun ρ => iff_true_intro (by
      rw [htest, hu η ρ]; exact decide_eq_true rfl)).trans (OracleComp.prEvent_true_eq_one _)
  have h2 : Pr{let ρ ← $ᵗ (pmodel.Tape η)}[(Machine.eqTest (Ty.isGround_base ()) :
      Machine pmodel [msg, msg] .bool).test η (v η ρ) ρ.1 = true] ≤
      (2 : ENNReal) ^ (-(c * η)) := by
    refine le_of_eq_of_le (prEvent_congr _ _ _ fun ρ => ?_)
      (deduceAdv_nameAt_le (M := pmodel) (D := decl) Name.n Fn.idx (τs := [msg])
        (fun _ _ x => x) (u := fun η ρ => Env.cons (v η ρ _ .zero) Env.empty)
        (fun η ρa ρh ρh' hρ => congrArg (Env.cons · _) (hf η ρa ρh ρh' hρ)) η (hle η))
    rw [htest, decide_eq_true_iff, hv η ρ]
    rfl
  change 1 ≤ advantage _ u v η + (2 : ENNReal) ^ (-(c * η))
  rw [advantage, h1, add_comm]
  exact (ENNReal.absDiff_le_iff.1 le_rfl).1.trans (add_le_add h2 le_rfl)

/-! ## G.PRF needs `ψ_msg` -/

/-- The vector `h(c, k)`, with its call explicit. -/
abbrev u₁ : OVec P [] [msg] := Env.cons (OTerm.call cO) Env.empty

/-- The instance of G.PRF at `u⃗ = h(c, k)`, `m = c` and the fresh name `n`. -/
@[expose] def inst₁ : PRFInstance decl :=
  ⟨P, [msg], u₁, cO, .bool, Name.n, Fn.idx, of_decide_eq_true rfl⟩

/-- **G.PRF needs `ψ_msg`.** With `u⃗ = h(c, k)` and `m = c`, every syntactic side condition holds
and every distinguisher has PRF advantage zero, but `ψ_msg`, which is `c ≠ c`, fails, and so does
the conclusion `h(c, k), h(c, k) ∼ h(c, k), n`. -/
theorem gprf_needs_psiMsg :
    inst₁.Syntactic ∧ inst₁.Holds (· = pmodel) (fun M => AdvClass.all M) ∧
      ¬ Valid (· = pmodel) (fun M => AdvClass.all M) (Γ := []) [] (.box (P.psiMsg u₁ cO)) ∧
      ¬ Valid (· = pmodel) (fun M => AdvClass.all M) (Γ := []) []
        (.equiv inst₁.lhs inst₁.rhs inst₁.order) := by
  refine ⟨by decide, ⟨fun M hM => hM ▸ pmodel_uniformSampler, fun M _ hM hU A _ => ?_⟩,
    fun h => ?_, fun h => ?_⟩
  · subst hM
    exact ⟨negligible_of_zero fun η => pmodel_prfAdv η hU _,
      negligible_of_zero fun η => pmodel_prfAdv η hU _⟩
  · have hb := Form.holds_box.1 (h pmodel pmodel_respectsLabels rfl Env.empty (by simp))
    refine not_negligible_one (negligible_of_le (fun η => le_of_eq ?_) hb)
    refine ((prEvent_congr _ _ (fun _ => True) fun ρ => iff_true_intro ?_).trans
      (OracleComp.prEvent_true_eq_one _)).symm
    refine Bool.eq_false_iff.2 fun hψ => (P.psiMsg_eq_true_iff _ u₁ cO _ ρ).1 hψ cO ?_ rfl
    simp
  · have hI := Form.holds_equiv.1 (h pmodel pmodel_respectsLabels rfl Env.empty (by simp))
    rw [PRFInstance.lhs, PRFInstance.rhs, Vec.rv_snoc, Vec.rv_snoc] at hI
    refine not_indist_eq_name (fun _ _ => rfl) (fun _ _ => rfl) (fun η ρa ρh ρh' hρ => ?_) hI
    change pmodel.fn η Fn.h (pmodel.fn η Fn.c) (pmodel.sample η keyT (ρh (P.keySlot pmodel η))) =
      pmodel.fn η Fn.h (pmodel.fn η Fn.c) (pmodel.sample η keyT (ρh' (P.keySlot pmodel η)))
    rw [hρ _ fun h => by cases h]

/-! ## G.PRF needs `ψ_key` -/

/-- The vector `k(c)`, in which the key occurs outside a hash. -/
abbrev u₂ : OVec P [] [msg] :=
  Env.cons (OTerm.app (OTerm.name (D := decl) Name.k (OTerm.fn (D := decl) Fn.idx)) cO) Env.empty

/-- **G.PRF needs `ψ_key`.** With `u⃗ = k(c)` and `m = c`, the key occurs outside a hash, while
every other syntactic side condition holds, `ψ_msg` holds (there is no call) and every
distinguisher has PRF advantage zero; the conclusion `k(c), h(c, k) ∼ k(c), n` fails, since
`k(c) = h(c, k)` in `pmodel`. -/
theorem gprf_needs_psiKey :
    ¬ P.KeyFree (u₂ _ .zero) ∧ P.Pptm (u₂ _ .zero) ∧ P.FirstOrder (u₂ _ .zero) ∧
      (P.closeVec u₂).AvoidsNames (· = ⟨_, _, Name.n⟩) ∧
      (∀ η hU adv, P.prfAdv pmodel η hU adv = 0) ∧
      Valid (· = pmodel) (fun M => AdvClass.all M) (Γ := []) [] (.box (P.psiMsg u₂ cO)) ∧
      ¬ Valid (· = pmodel) (fun M => AdvClass.all M) (Γ := []) []
        (.equiv (Vec.snoc (P.closeVec u₂) (P.hashTerm (P.close cO)))
          (Vec.snoc (P.closeVec u₂) nT) (of_decide_eq_true rfl)) := by
  refine ⟨by decide, by decide, by decide, by decide, pmodel_prfAdv, fun M _ _ env _ => ?_,
    fun h => ?_⟩
  · refine Form.holds_box.2 (negligible_of_zero fun η =>
      prEvent_eq_zero_of_forall_not _ _ fun ρ hρ => ?_)
    rw [Bool.eq_false_iff] at hρ
    refine hρ ((P.psiMsg_eq_true_iff _ u₂ cO env ρ).2 fun t' ht' => ?_)
    rcases List.mem_append.1 ht' with h' | h' <;> exact absurd h' List.not_mem_nil
  · have hI := Form.holds_equiv.1 (h pmodel pmodel_respectsLabels rfl Env.empty (by simp))
    rw [Vec.rv_snoc, Vec.rv_snoc] at hI
    refine not_indist_eq_name (fun _ _ => rfl) (fun _ _ => rfl) (fun η ρa ρh ρh' hρ => ?_) hI
    change pmodel.sample η keyT (ρh (P.keySlot pmodel η)) (pmodel.fn η Fn.c) =
      pmodel.sample η keyT (ρh' (P.keySlot pmodel η)) (pmodel.fn η Fn.c)
    rw [hρ _ fun h => by cases h]

/-! ## The worked derivation, and satisfiability -/

/-- The vector `s`, to which PRF-Simple applies G.PRF. -/
abbrev uw : OVec P [] ([] ++ [msg]) :=
  Env.append (Env.empty : OVec P [] []) (Env.cons (nmO Name.s) Env.empty)

/-- The instance of G.PRF inside the worked PRF-Simple: the vector `s`, the message `r` and the
fresh name `n`. -/
@[expose] def inst : PRFInstance decl :=
  ⟨P, [] ++ [msg], uw, nmO Name.r, .bool, Name.n, Fn.idx, of_decide_eq_true rfl⟩

/-- The hypothesis `[ψ_msg]` of that instance; there is no call, so it is `[true]`. -/
@[expose] def psiH : Form decl [] := .box (P.psiMsg uw (nmO Name.r))

/-- The models over which the derivation uses FreshL. -/
abbrev LongR (M : Model decl) : Prop := M.LongTapes ∧ M.PolyCoins msg

/-- The syntactic side conditions of the instance, by `decide`. -/
theorem inst_syntactic : inst.Syntactic := by decide

theorem inst_holds : inst.Holds (· = pmodel) (fun M => AdvClass.all M) := by
  refine ⟨fun M hM => hM ▸ pmodel_uniformSampler, fun M _ hM hU A _ => ?_⟩
  subst hM
  exact ⟨negligible_of_zero fun η => pmodel_prfAdv η hU _,
    negligible_of_zero fun η => pmodel_prfAdv η hU _⟩

/-- `[ψ_msg]` holds in every model: there is no call. -/
theorem valid_psiH {R : Model decl → Prop} {C : ∀ M : Model decl, AdvClass M} :
    Valid R C (Γ := []) [] psiH := fun M _ _ env _ => by
  refine Form.holds_box.2 (negligible_of_zero fun η =>
    prEvent_eq_zero_of_forall_not _ _ fun ρ hρ => ?_)
  rw [Bool.eq_false_iff] at hρ
  refine hρ ((P.psiMsg_eq_true_iff _ uw (nmO Name.r) env ρ).2 fun t' ht' => ?_)
  rcases List.mem_append.1 ht' with h' | h' <;> exact absurd h' List.not_mem_nil

/-- **A worked PRF-Simple** (CCS26 Fig. 11): from `[ψ_msg]`, derive `h(r, k) ⊬ s`. FreshR gives
`⊬ s`, and PRF-Simple (`Derivation.nonDedPRF`) adds the hash of `r` under the key on the left,
through G.PRF at the vector `s` with the fresh name `n`, Perm, FreshL and Rw-Equiv. -/
@[expose] def prfWorked :
    Derivation decl (fun _ => False) (· = .gprf inst) LongR (Γ := []) [psiH]
      (.nonDed (Vec.snoc (P.closeVec (Env.empty : OVec P [] []))
        (P.hashTerm (P.close (nmO Name.r)))) (P.close (nmO Name.s))) :=
  Derivation.nonDedPRF P Env.empty (nmO Name.s) (nmO Name.r) Name.n Fn.idx
    (ho := of_decide_eq_true rfl) _ (Ty.isGround_base ()) _ rfl inst_syntactic (fun _ h => h)
    (fun _ _ _ _ _ _ => ⟨fun _ x => (nomatch x),
      (close_nmO Name.s).symm ▸ (FTerm.readsPoly_fn _).name _⟩)
    (fun _ x => nomatch x) (by decide) (.ax List.mem_cons_self)
    ((close_nmO Name.s).symm ▸ .nonDedFreshR (P.closeVec (Env.empty : OVec P [] [])) Name.s
      Fn.idx (of_decide_eq_true rfl) rfl fun _ x => nomatch x)

/-- The worked derivation is valid over the models with long tapes and polynomial bit blocks for
messages, against every class under which its G.PRF instance meets its hypotheses. -/
theorem prfWorked_sound (R : Model decl → Prop) (C : ∀ M : Model decl, AdvClass M)
    (hR : ∀ M, R M → LongR M) (hinst : inst.Holds R C) :
    Valid R C [psiH]
      (.nonDed (Vec.snoc (P.closeVec (Env.empty : OVec P [] []))
        (P.hashTerm (P.close (nmO Name.r)))) (P.close (nmO Name.s))) :=
  prfWorked.sound R C (fun _ h => h.elim) (fun e (he : e = .gprf inst) => he ▸ hinst) hR

/-- **Satisfiability of PRF-Simple.** In `pmodel`, against all machines, every hypothesis of the
worked derivation holds jointly: long tapes, polynomial bit blocks, uniform messages, freshness,
`[ψ_msg]` and the PRF hypothesis, since `h` is a perfect PRF. So `h(r, k) ⊬ s` holds there. -/
theorem valid_prfWorked :
    Valid (· = pmodel) (fun M => AdvClass.all M) (Γ := []) []
      (.nonDed (Vec.snoc (P.closeVec (Env.empty : OVec P [] []))
        (P.hashTerm (P.close (nmO Name.r)))) (P.close (nmO Name.s))) :=
  valid_psiH.cut (prfWorked_sound _ _ (fun _ hM => hM ▸ ⟨pmodel_longTapes, pmodel_polyCoins⟩)
    inst_holds)

/-- **Satisfiability of G.PRF.** In `pmodel`, against all machines, every hypothesis of G.PRF holds
at the instance `inst`, so `s, h(r, k) ∼ s, n` holds there. -/
theorem valid_gprf :
    Valid (· = pmodel) (fun M => AdvClass.all M) (Γ := []) []
      (.equiv inst.lhs inst.rhs inst.order) :=
  inst.valid inst_syntactic inst_holds valid_psiH

end Interop.Squirrel.PRFExamples
