/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Squirrel.Test.PRFExamples

/-!
# Checks of PRF.R and PRF.L-sec

Checks of PRF.R and PRF.L-sec (CCS26 Fig. 4 and §2.3, `Valid.nonDed_prfR`,
`Valid.nonDed_prfLSec`) in `PRFExamples.pmodel`, where messages at `η` are the bitstrings of
length `η`, a key is a whole uniform function table and `h(x, k) = k(x)`, so that every
distinguisher has PRF advantage zero (`PRFExamples.pmodel_prfAdv`).

## Satisfiability

* `chainWorked`, `chainWorked_sound`: two steps of a hash chain with the oracle as the leakage,
  `ck₀ = s`, `ck₁ = h(s, k)`, `ck₂ = h(ck₁, k)`. FreshR gives `o_h^k ⊬ s`; PRF.R gives
  `o_h^k ⊬ h(s, k)`; PRF.R again, at the message `h(s, k)`, which is itself a hash, gives
  `o_h^k ⊬ h(h(s, k), k)`. The second step has two candidates (`h(s, k)` and `s`), and needs no
  `ψ_msg` of the message: `m = h(s, k)` is not asked to differ from `s`.
* `valid_chainWorked`: in `pmodel`, against all machines, every hypothesis of both PRF.R steps
  holds jointly (uniform messages, long tapes, polynomial bit blocks, read bounds, the label
  `large`, `[ψ_msg]` and the PRF assumption on the named reductions), so `o_h^k ⊬ h(h(s, k), k)`
  holds there. FreshR does not give it: the right side is not a name.
* `leftWorked`, `valid_leftWorked`: PRF.R gives `o_h^k ⊬ h(s, k)`, FreshR gives `o_h^k ⊬ r`, and
  PRF.L-sec with the secret `h(s, k)` and the message `r` gives `o_h^k, h(r, k) ⊬ h(s, k)`; in
  `pmodel` every hypothesis of both steps holds jointly, `[s ≠ r]` (`valid_psiL`) because two
  independent messages collide with probability `2^{-η}`.

## Premises needed

* `prfLSec_needs_psiMsg`: with the secret `h(s, k)` and the message `s`, every hypothesis of
  PRF.L-sec but `[ψ_msg]` holds (the premise by PRF.R, `C_sec` by FreshR), `ψ_msg` is `s ≠ s`, and
  the conclusion `o_h^k, h(s, k) ⊬ h(s, k)` fails: the attacker returns the hash it is given.
* `prfR_needs_premise`: with the constant message `c`, every hypothesis of PRF.R but its premise
  `o_h^k ⊬ c` holds, and the conclusion `o_h^k ⊬ h(c, k)` fails: the attacker queries its oracle
  at `c`.
* `prfLSec_needs_premise`: with the constant secret `c` and the message `r`, every hypothesis of
  PRF.L-sec but its premise `o_h^k ⊬ c` holds, `C_sec` by FreshR and `[ψ_msg]` with no call, and
  the conclusion `o_h^k, h(r, k) ⊬ c` fails.

## References

* [CCS26] Hérouard, Jacomme, Koutsos, Lallemand, *Secrecy in Squirrel and the Post-Compromise
  Security of a Ratchet*, CCS 2026: §2.3 and Fig. 4.
-/

public section

namespace Interop.Squirrel.PRFOracleExamples

open IPFunctor IPFunctor.ScopedSignature PRFExamples

/-- The models over which the chain uses PRF.R: uniform messages, long tapes and polynomial bit
blocks for messages. -/
abbrev ChainR (M : Model decl) : Prop :=
  M.UniformSampler msg ∧ M.LongTapes ∧ M.PolyCoins msg

/-- The empty vector. -/
abbrev u₀ : OVec P [] [] := Env.empty

/-- The first link `h(s, k)`, with its call explicit. -/
@[expose] def ck₁ : OTerm P [] msg := OTerm.call (nmO Name.s)

/-- The first step of the chain: PRF.R at the message `s`. -/
@[expose] def inst₁ : PRFRInstance decl :=
  ⟨P, [], u₀, nmO Name.s, trivial, trivial, of_decide_eq_true rfl, of_decide_eq_true rfl⟩

/-- The second step of the chain: PRF.R at the message `h(s, k)`. -/
@[expose] def inst₂ : PRFRInstance decl :=
  ⟨P, [], u₀, ck₁, trivial, trivial, of_decide_eq_true rfl, of_decide_eq_true rfl⟩

/-- The hypothesis `[ψ_msg^{m,k}(∅)]`: the empty vector has no call, so it is `[true]`. -/
@[expose] def psiR (m : OTerm P [] msg) : Form decl [] := .box (P.psiMsgVec u₀ m)

/-- `[ψ_msg^{m,k}(∅)]` holds in every model. -/
theorem valid_psiR {R : Model decl → Prop} {C : ∀ M : Model decl, AdvClass M}
    {Θ : List (Form decl [])} (m : OTerm P [] msg) : Valid R C Θ (psiR m) := fun M _ _ env _ => by
  refine Form.holds_box.2 (negligible_of_zero fun η =>
    prEvent_eq_zero_of_forall_not _ _ fun ρ hρ => ?_)
  rw [Bool.eq_false_iff] at hρ
  exact hρ ((P.psiMsgVec_eq_true_iff _ u₀ m env ρ).2 fun t' ht' => absurd ht' List.not_mem_nil)

/-- The syntactic side conditions of the first step: the hash type `msg` is `large`, and `s`
meets `ψ_key`, `⊢pptm` and first order (`decide`). -/
theorem inst₁_syntactic : inst₁.Syntactic := by
  refine ⟨fun _ h => absurd h List.not_mem_nil, rfl, fun _ x => ?_, by decide, fun _ x => ?_,
    by decide, fun _ x => ?_, by decide⟩ <;> cases x

/-- The syntactic side conditions of the second step, at the message `h(s, k)`. -/
theorem inst₂_syntactic : inst₂.Syntactic := by
  refine ⟨fun _ h => absurd h List.not_mem_nil, rfl, fun _ x => ?_, by decide, fun _ x => ?_,
    by decide, fun _ x => ?_, by decide⟩ <;> cases x

/-- The PRF assumption of PRF.R holds in `pmodel` against all machines, at every instance: `h` is
a perfect PRF, so every named reduction has PRF advantage zero. -/
theorem holds_pmodel (e : PRFRInstance decl) (he : e.P = P) :
    e.Holds (· = pmodel) (fun M => AdvClass.all M) := by
  obtain ⟨_, τs, u, m, hmg, hh, o, o'⟩ := e
  subst he
  intro M _ hM hU g _ t _
  subst hM
  exact negligible_of_zero fun η => pmodel_prfAdv η hU _

/-- The empty vector beside the hash oracle does not use a message name. -/
theorem avoidsNames_lhs (x : Name .bool msg) :
    inst₁.lhs.AvoidsNames (· = ⟨_, _, x⟩) := by
  cases x <;> decide

/-- `o_h^k ⊬ x(idx)` by FreshR, for a message name `x`. -/
@[expose] def freshMsg (x : Name .bool msg) {prf : PRFRule decl → Prop}
    {R₀ : Model decl → Prop} {Θ : List (Form decl [])} :
    Derivation decl (fun _ => False) prf R₀ Θ (.nonDed inst₁.lhs (P.close (nmO x)) inst₁.orderM) :=
  (close_nmO x).symm ▸ Derivation.nonDedFreshR inst₁.lhs x Fn.idx inst₁.orderM rfl
    (avoidsNames_lhs x)

/-- The read bounds of PRF.R's terms at the empty vector: a message name or its hash reads no bit
of the attacker tape. -/
theorem readsPoly_chain (m : OTerm P [] msg) (hm : m = nmO Name.s ∨ m = ck₁) (M : Model decl)
    (C : AdvClass M) (env : Env (Kind.Value M) []) :
    Vec.ReadsPoly M C (P.closeVec u₀) env ∧ FTerm.ReadsPoly M C (P.close m) env := by
  refine ⟨fun _ x => (nomatch x), 0, fun _ _ _ _ _ => ?_⟩
  rcases hm with rfl | rfl <;> rfl

/-- **Two steps of a hash chain by PRF.R** (CCS26 §2.3): FreshR gives `o_h^k ⊬ s`, PRF.R gives
`o_h^k ⊬ h(s, k)`, and PRF.R at the message `h(s, k)` gives `o_h^k ⊬ h(h(s, k), k)`. -/
@[expose] def chainWorked :
    Derivation decl (fun _ => False) (fun e => e = .right inst₁ ∨ e = .right inst₂) ChainR
      (Γ := []) [psiR (nmO Name.s), psiR ck₁]
      (.nonDed inst₂.lhs (P.hashTerm (P.close ck₁)) inst₂.order) :=
  have d₁ := Derivation.nonDedPRFR inst₁ (.inl rfl) inst₁_syntactic (fun _ h => h)
    (fun M _ _ C env _ => readsPoly_chain _ (.inl rfl) M C env) (.ax List.mem_cons_self)
    (freshMsg Name.s)
  Derivation.nonDedPRFR inst₂ (.inr rfl) inst₂_syntactic (fun _ h => h)
    (fun M _ _ C env _ => readsPoly_chain _ (.inr rfl) M C env)
    (.ax (List.mem_cons_of_mem _ List.mem_cons_self)) d₁

/-- The chain is valid over the models of `ChainR`, against every class under which both PRF.R
instances meet their PRF assumption. -/
theorem chainWorked_sound (R : Model decl → Prop) (C : ∀ M : Model decl, AdvClass M)
    (hR : ∀ M, R M → ChainR M) (h₁ : inst₁.Holds R C) (h₂ : inst₂.Holds R C) :
    Valid R C [psiR (nmO Name.s), psiR ck₁]
      (.nonDed inst₂.lhs (P.hashTerm (P.close ck₁)) inst₂.order) :=
  chainWorked.sound R C (fun _ h => h.elim) (fun e he => by
    rcases he with rfl | rfl
    · exact h₁
    · exact h₂) hR

/-- `pmodel` meets the model conditions of the chain. -/
theorem pmodel_chainR : ChainR pmodel :=
  ⟨pmodel_uniformSampler, pmodel_longTapes, pmodel_polyCoins⟩

/-- **Satisfiability of PRF.R.** In `pmodel`, against all machines, every hypothesis of both PRF.R
steps holds jointly, so `o_h^k ⊬ h(h(s, k), k)` holds there. -/
theorem valid_chainWorked :
    Valid (· = pmodel) (fun M => AdvClass.all M) (Γ := []) []
      (.nonDed inst₂.lhs (P.hashTerm (P.close ck₁)) inst₂.order) :=
  have hc := chainWorked_sound (· = pmodel) (fun M => AdvClass.all M)
    (fun _ hM => hM ▸ pmodel_chainR) (holds_pmodel _ rfl) (holds_pmodel _ rfl)
  (valid_psiR (Θ := []) ck₁).cut ((valid_psiR (Θ := [psiR ck₁]) (nmO Name.s)).cut hc)

/-! ## PRF.L-sec -/

/-- The first PRF.R step: `o_h^k ⊬ h(s, k)`, from `[ψ_msg^{s,k}(∅)]`. -/
@[expose] def step₁ {prf : PRFRule decl → Prop} (hprf : prf (.right inst₁))
    {Θ : List (Form decl [])} (hψ : psiR (nmO Name.s) ∈ Θ) :
    Derivation decl (fun _ => False) prf ChainR Θ
      (.nonDed inst₁.lhs (P.hashTerm (P.close (nmO Name.s))) inst₁.order) :=
  Derivation.nonDedPRFR inst₁ hprf inst₁_syntactic (fun _ h => h)
    (fun M _ _ C env _ => readsPoly_chain _ (.inl rfl) M C env) (.ax hψ) (freshMsg _)

/-- PRF.L-sec at the empty vector, a secret `v` and a message `m`. -/
@[expose] def instL (v m : OTerm P [] msg) : PRFLInstance decl :=
  ⟨P, [], msg, u₀, v, m, trivial, trivial, of_decide_eq_true rfl, of_decide_eq_true rfl,
    of_decide_eq_true rfl⟩

/-- PRF.L-sec with the secret `h(s, k)` and the message `r`. -/
abbrev inst₃ : PRFLInstance decl := instL ck₁ (nmO Name.r)

theorem inst₃_syntactic : inst₃.Syntactic := by decide

/-- The PRF assumption of PRF.L-sec holds in `pmodel` against all machines, at every instance. -/
theorem holdsL_pmodel (e : PRFLInstance decl) (he : e.P = P) :
    e.Holds (· = pmodel) (fun M => AdvClass.all M) := by
  obtain ⟨_, τs, β, u, v, m, hβ, hmg, o, o', o''⟩ := e
  subst he
  intro M _ hM hU g _
  subst hM
  exact ⟨negligible_of_zero fun η => pmodel_prfAdv η hU _,
    negligible_of_zero fun η => pmodel_prfAdv η hU _⟩

/-- The hypothesis `[ψ_msg^{m,k}(∅, v, m)]` of PRF.L-sec. -/
@[expose] def psiL (v m : OTerm P [] msg) : Form decl [] :=
  .box (P.psiMsg (Env.append u₀ (Env.cons v Env.empty)) m)

/-- A message name at `idx` has no call. -/
theorem calls_nmO (x : Name .bool msg) : P.calls (nmO x) = [] :=
  rfl

/-- The arguments of the calls of `h(s, k)` and `r`: only `s`. -/
theorem calls_psiL (t' : OTerm P [] msg)
    (ht' : t' ∈ P.vecCalls (Env.append u₀ (Env.cons ck₁ Env.empty)) ++ P.calls (nmO Name.r)) :
    t' = nmO Name.s := by
  change t' ∈ P.vecCalls (Env.cons ck₁ Env.empty : OVec P [] [msg]) ++ P.calls (nmO Name.r) at ht'
  simp only [PRFSymbols.vecCalls_cons, PRFSymbols.vecCalls_nil, ck₁, PRFSymbols.calls_call,
    calls_nmO, List.append_nil, List.mem_singleton] at ht'
  exact ht'

/-- `[s ≠ r]` holds in `pmodel`: two independent uniform messages collide with probability at most
`2^{-η}` (`deduceAdv_nameAt_le`). -/
theorem valid_psiL {Θ : List (Form decl [])} :
    Valid (· = pmodel) (fun M => AdvClass.all M) Θ (psiL ck₁ (nmO Name.r)) :=
  fun M _ hM env _ => by
  subst hM
  obtain ⟨c, hc, hle⟩ := pmodel_isLarge
  refine Form.holds_box.2 (negligible_of_le (fun η => ?_) (negligible_two_rpow_neg_mul hc))
  refine (prEvent_mono _ _ (fun ρ => (P.close (nmO Name.r)).denote
    (fullInterp pmodel (AdvClass.all pmodel)) env η ρ =
      pmodel.nameAt (D := decl) Name.s Fn.idx η ρ) fun ρ hρ => ?_).trans ?_
  · by_contra hne
    refine Bool.eq_false_iff.1 hρ ((P.psiMsg_eq_true_iff _ _ _ env ρ).2 fun t' ht' heq => hne ?_)
    rw [calls_psiL t' ht'] at heq
    rw [P.denote_close_apply _ _ env ρ]
    exact heq.symm
  · exact deduceAdv_nameAt_le (M := pmodel) (D := decl) Name.s Fn.idx (τs := [msg])
      (fun _ _ x => x)
      (u := fun η ρ => Env.cons ((P.close (nmO Name.r)).denote
        (fullInterp pmodel (AdvClass.all pmodel)) env η ρ) Env.empty)
      (fun η ρa ρh ρh' hρ => congrArg (Env.cons · _) (by
        change pmodel.sample η msg (ρh ⟨⟨_, _, Name.r⟩, pmodel.fn η Fn.idx⟩) =
          pmodel.sample η msg (ρh' ⟨⟨_, _, Name.r⟩, pmodel.fn η Fn.idx⟩)
        rw [hρ _ fun h => by cases h])) η (hle η)

/-- The read bounds of PRF.L-sec's terms at the empty vector, for a secret and a message among
`h(s, k)`, `r`, `s` and `c`: none reads a bit of the attacker tape. -/
theorem readsPoly_left (t : OTerm P [] msg) (ht : t = ck₁ ∨ t = nmO Name.r ∨ t = nmO Name.s ∨
    t = cO) (M : Model decl) (C : AdvClass M) (env : Env (Kind.Value M) []) :
    FTerm.ReadsPoly M C (P.close t) env := by
  refine ⟨0, fun _ _ _ _ _ => ?_⟩
  rcases ht with rfl | rfl | rfl | rfl <;> rfl

/-- **PRF.R, then PRF.L-sec** (CCS26 §2.3): PRF.R gives `o_h^k ⊬ h(s, k)`; FreshR gives
`o_h^k ⊬ r`; PRF.L-sec, with the secret `h(s, k)` and the message `r`, gives
`o_h^k, h(r, k) ⊬ h(s, k)`. -/
@[expose] def leftWorked :
    Derivation decl (fun _ => False) (fun e => e = .right inst₁ ∨ e = .left inst₃) ChainR
      (Γ := []) [psiR (nmO Name.s), psiL ck₁ (nmO Name.r)]
      (.nonDed (Vec.snoc inst₃.lhs (P.hashTerm (P.close (nmO Name.r)))) (P.close ck₁)
        inst₃.orderC) :=
  Derivation.nonDedPRFLSec inst₃ (.inr rfl) inst₃_syntactic
    (fun _ h => ⟨h.1, h.2.1, h.2.2, h.2.2⟩)
    (fun M _ _ C env _ => ⟨fun _ x => (nomatch x), readsPoly_left _ (.inl rfl) M C env,
      readsPoly_left _ (.inr (.inl rfl)) M C env⟩)
    (.ax (List.mem_cons_of_mem _ List.mem_cons_self)) (step₁ (.inl rfl) List.mem_cons_self)
    (freshMsg _)

/-- **Satisfiability of PRF.L-sec.** In `pmodel`, against all machines, every hypothesis of the
PRF.R step and of the PRF.L-sec step holds jointly, so `o_h^k, h(r, k) ⊬ h(s, k)` holds there.
FreshR does not give it: the secret is not a name. -/
theorem valid_leftWorked :
    Valid (· = pmodel) (fun M => AdvClass.all M) (Γ := []) []
      (.nonDed (Vec.snoc inst₃.lhs (P.hashTerm (P.close (nmO Name.r)))) (P.close ck₁)
        inst₃.orderC) :=
  have hc := leftWorked.sound (· = pmodel) (fun M => AdvClass.all M) (fun _ h => h.elim)
    (fun e he => by
      rcases he with rfl | rfl
      · exact holds_pmodel _ rfl
      · exact holdsL_pmodel _ rfl)
    (fun _ hM => hM ▸ pmodel_chainR)
  (valid_psiL (Θ := [])).cut ((valid_psiR (Θ := [psiL ck₁ (nmO Name.r)]) (nmO Name.s)).cut hc)

/-! ## Premises needed -/

/-- A conclusion `u⃗ ⊬ v` fails in `pmodel` against all machines when an admitted machine computes
`v` on every tape. -/
theorem not_valid_nonDed {τs : List (Ty Unit)} {u : Vec decl [] τs} {v : FTerm decl [] msg}
    {ho : Ty.SecrecyOrder τs msg} (g : AdvMachine pmodel τs msg)
    (hg : (AdvClass.all pmodel).mem g)
    (hv : ∀ η (ρ : pmodel.Tape η), Ty.appVals (g.eval η ρ.1)
      (u.rv pmodel (AdvClass.all pmodel) Env.empty η ρ) =
        v.denote (fullInterp pmodel (AdvClass.all pmodel)) Env.empty η ρ) :
    ¬ Valid (· = pmodel) (fun M => AdvClass.all M) (Γ := []) [] (.nonDed u v ho) := by
  intro h
  have hN := Form.holds_nonDed.1 (h pmodel pmodel_respectsLabels rfl Env.empty (by simp))
  refine not_negligible_one (negligible_of_le (fun η => le_of_eq ?_) (hN g hg))
  exact ((prEvent_congr _ _ (fun _ => True) fun ρ => iff_true_intro (hv η ρ)).trans
    (OracleComp.prEvent_true_eq_one _)).symm

/-- No vector keeps the constant `c` secret: the attacker returns `c`. -/
theorem not_valid_nonDed_c {τs : List (Ty Unit)} (u : Vec decl [] τs)
    (ho : Ty.SecrecyOrder τs msg) :
    ¬ Valid (· = pmodel) (fun M => AdvClass.all M) (Γ := []) [] (.nonDed u (P.close cO) ho) :=
  not_valid_nonDed ((Machine.input (τs := msg :: (τs ++ msg.args)) .zero
      (Ty.isGround_base ())).fn Fn.c)
    ((AdvClass.all _).fn_mem _ ((AdvClass.all _).input_mem _ _)) fun η ρ => by
    rw [AdvMachine.appVals_eval]
    exact (Machine.run_fn _ _ _).trans (Machine.run_input _ _ _)

/-- PRF.L-sec with the secret `h(s, k)` and the message `s`: the secret's call is on the
message. -/
abbrev inst₄ : PRFLInstance decl := instL ck₁ (nmO Name.s)

/-- **PRF.L-sec needs `ψ_msg`.** With the secret `h(s, k)` and the message `s`: the syntactic
conditions and the PRF assumption hold, `o_h^k ⊬ h(s, k)` holds (PRF.R) and so does
`C_sec = o_h^k ⊬ s` (FreshR), but `ψ_msg`, which is `s ≠ s`, fails, and so does the conclusion
`o_h^k, h(s, k) ⊬ h(s, k)`: the attacker returns the hash it is given. -/
theorem prfLSec_needs_psiMsg :
    inst₄.Syntactic ∧ inst₄.Holds (· = pmodel) (fun M => AdvClass.all M) ∧
      Valid (· = pmodel) (fun M => AdvClass.all M) (Γ := []) []
        (.nonDed inst₄.lhs (P.close inst₄.v) inst₄.order) ∧
      Valid (· = pmodel) (fun M => AdvClass.all M) (Γ := []) []
        (.nonDed inst₄.lhs (P.close inst₄.m) inst₄.orderM) ∧
      ¬ Valid (· = pmodel) (fun M => AdvClass.all M) (Γ := []) []
        (.box (P.psiMsg (Env.append inst₄.u (Env.cons inst₄.v Env.empty)) inst₄.m)) ∧
      ¬ Valid (· = pmodel) (fun M => AdvClass.all M) (Γ := []) []
        (.nonDed (Vec.snoc inst₄.lhs (P.hashTerm (P.close inst₄.m))) (P.close inst₄.v)
          inst₄.orderC) := by
  refine ⟨by decide, holdsL_pmodel _ rfl, ?_, ?_, fun h => ?_, ?_⟩
  · exact (valid_psiR (Θ := []) (nmO Name.s)).cut
      ((step₁ (prf := (· = .right inst₁)) rfl List.mem_cons_self).sound _ _ (fun _ h => h.elim)
        (fun e he => he ▸ holds_pmodel _ rfl) (fun _ hM => hM ▸ pmodel_chainR))
  · exact (freshMsg (prf := fun _ => False) (R₀ := fun _ => True) (Θ := []) Name.s).sound _ _
      (fun _ h => h.elim) (fun _ h => h.elim) fun _ _ => trivial
  · have hb := Form.holds_box.1 (h pmodel pmodel_respectsLabels rfl Env.empty (by simp))
    refine not_negligible_one (negligible_of_le (fun η => le_of_eq ?_) hb)
    refine ((prEvent_congr _ _ (fun _ => True) fun ρ => iff_true_intro ?_).trans
      (OracleComp.prEvent_true_eq_one _)).symm
    refine Bool.eq_false_iff.2 fun hψ => (P.psiMsg_eq_true_iff _ _ _ _ ρ).1 hψ (nmO Name.s) ?_ rfl
    change nmO Name.s ∈ P.vecCalls (Env.cons ck₁ Env.empty : OVec P [] [msg]) ++
      P.calls (nmO Name.s)
    simp [ck₁, PRFSymbols.calls_call, calls_nmO]
  · exact not_valid_nonDed (Machine.input
      (τs := (([] ++ [Ty.arrow msg msg]) ++ [msg]) ++ msg.args) (.succ .zero) trivial)
      ((AdvClass.all _).input_mem _ (Ty.isGround_base ())) fun η ρ => rfl

/-- PRF.R at the constant message `c`. -/
@[expose] def instC : PRFRInstance decl :=
  ⟨P, [], u₀, cO, trivial, trivial, of_decide_eq_true rfl, of_decide_eq_true rfl⟩

/-- The attacker against `o_h^k ⊢ h(c, k)`: it queries its oracle at `c`. -/
@[expose] noncomputable def queryC : AdvMachine pmodel ([] ++ [Ty.arrow msg msg]) msg :=
  (((Machine.input (τs := [msg]) .zero (Ty.isGround_base ())).app
    (Ty.isGround_base ())).rename (Env.cons (.succ .zero) (Env.cons .zero Env.empty) :
      Renaming [Ty.arrow msg msg, msg] [msg, Ty.arrow msg msg])).fn Fn.c

/-- **PRF.R needs its premise.** At the constant message `c`, the syntactic conditions, the PRF
assumption and `[ψ_msg]` hold, but the premise `o_h^k ⊬ c` fails, and so does the conclusion
`o_h^k ⊬ h(c, k)`: the attacker queries its oracle at `c`. -/
theorem prfR_needs_premise :
    instC.Syntactic ∧ instC.Holds (· = pmodel) (fun M => AdvClass.all M) ∧
      Valid (· = pmodel) (fun M => AdvClass.all M) (Γ := []) [] (psiR cO) ∧
      ¬ Valid (· = pmodel) (fun M => AdvClass.all M) (Γ := []) []
        (.nonDed instC.lhs (P.close cO) instC.orderM) ∧
      ¬ Valid (· = pmodel) (fun M => AdvClass.all M) (Γ := []) []
        (.nonDed instC.lhs (P.hashTerm (P.close cO)) instC.order) := by
  refine ⟨?_, holds_pmodel _ rfl,
    valid_psiR cO, not_valid_nonDed_c _ _, not_valid_nonDed queryC
      ((AdvClass.all _).fn_mem _ ((AdvClass.all _).rename_mem _
        ((AdvClass.all _).app_mem _ ((AdvClass.all _).input_mem _ _)))) fun η ρ => ?_⟩
  · refine ⟨fun _ h => absurd h List.not_mem_nil, rfl, fun _ x => ?_, by decide, fun _ x => ?_,
      by decide, fun _ x => ?_, by decide⟩ <;> cases x
  refine (AdvMachine.appVals_eval queryC _).trans ((Machine.run_fn _ _ _).trans
    ((Machine.run_rename _ _ _).trans ((Machine.run_app _ _ _).trans
      ((Machine.run_input _ _ _).trans ?_))))
  change (P.hashOracle (Γ := [])).denote (fullInterp pmodel (AdvClass.all pmodel)) Env.empty η ρ
    (pmodel.fn η Fn.c) = _
  rw [P.denote_hashOracle]
  rfl

/-- PRF.L-sec with the constant secret `c` and the message `r`. -/
abbrev inst₅ : PRFLInstance decl := instL cO (nmO Name.r)

/-- **PRF.L-sec needs its premise.** With the constant secret `c` and the message `r`: the
syntactic conditions and the PRF assumption hold, `[ψ_msg]` holds (there is no call) and so does
`C_sec = o_h^k ⊬ r` (FreshR), but the premise `o_h^k ⊬ c` fails, and so does the conclusion
`o_h^k, h(r, k) ⊬ c`. -/
theorem prfLSec_needs_premise :
    inst₅.Syntactic ∧ inst₅.Holds (· = pmodel) (fun M => AdvClass.all M) ∧
      Valid (· = pmodel) (fun M => AdvClass.all M) (Γ := []) [] (psiL cO (nmO Name.r)) ∧
      Valid (· = pmodel) (fun M => AdvClass.all M) (Γ := []) []
        (.nonDed inst₅.lhs (P.close inst₅.m) inst₅.orderM) ∧
      ¬ Valid (· = pmodel) (fun M => AdvClass.all M) (Γ := []) []
        (.nonDed inst₅.lhs (P.close inst₅.v) inst₅.order) ∧
      ¬ Valid (· = pmodel) (fun M => AdvClass.all M) (Γ := []) []
        (.nonDed (Vec.snoc inst₅.lhs (P.hashTerm (P.close inst₅.m))) (P.close inst₅.v)
          inst₅.orderC) := by
  refine ⟨by decide, holdsL_pmodel _ rfl, fun M _ _ env _ => ?_,
    (freshMsg (prf := fun _ => False) (R₀ := fun _ => True) (Θ := []) Name.r).sound _ _
      (fun _ h => h.elim) (fun _ h => h.elim) fun _ _ => trivial,
    not_valid_nonDed_c _ _, not_valid_nonDed_c _ _⟩
  refine Form.holds_box.2 (negligible_of_zero fun η =>
    prEvent_eq_zero_of_forall_not _ _ fun ρ hρ => ?_)
  rw [Bool.eq_false_iff] at hρ
  refine hρ ((P.psiMsg_eq_true_iff _ _ _ env ρ).2 fun t' ht' => ?_)
  change t' ∈ P.vecCalls (Env.cons cO Env.empty : OVec P [] [msg]) ++ P.calls (nmO Name.r) at ht'
  simp [cO, calls_nmO] at ht'

end Interop.Squirrel.PRFOracleExamples
