/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Squirrel.Test.FreshLExamples

/-!
# Checks of Rw-Oracle and Pc-Oracle

The declaration and model are those of `Interop.Squirrel.FreshLExamples`: messages are bitstrings
of length `η`, the names `k, m, n` draw uniform messages, `h` is the identity, and `longModel` has
an attacker tape of `2^η` bits whose first `η` bits are the attacker symbol `a`. The oracles are
`h` and two punctured copies of it:

* `hideO = λx. if x ≠ m then h(x) else n` hides the secret `n` behind the secret point `m`;
* `leakO = λx. if x ≠ a then h(x) else n` hides it behind the attacker's own message `a`.

The checks:

* `valid_rwOracleWorked`: Rw-Oracle at `β = 2`. From `h ⊬ n` (FreshR) and the agreement of
  `hideO` and `h` at every message deducible from `h` (FreshR gives `h ⊬ m`, then Ineq), conclude
  `hideO ⊬ n`. Every hypothesis holds jointly in `longModel` against `AdvClass.all`. FreshR does
  not give this conclusion: `hideO` uses `n`, and `decide` rejects FreshR's freshness premise
  (`not_avoidsNames_hideO`).
* `valid_rwOracleFig3`: Rw-Oracle as in Fig. 3 (`β = 1`). From `hideO ⊬ k` (FreshR) and the
  agreement of `h` and `hideO` at every message deducible from `h`, conclude `h ⊬ k`.
* `rwOracle_needs_agree`: with `leakO` in place of `hideO`, `h ⊬ n` and every side condition still
  hold, but `leakO ⊬ n` fails: the machine querying the oracle at `a` computes `n`. So the
  agreement premise fails, at both `β`: the oracles differ at the deducible point `a`.
* `valid_pcOracleWorked`: Pc-Oracle. With `o′ = λx. if x ≠ m then hideO(x) else m`, which is the
  identity although it uses `n`, FreshR with its semantic freshness premise
  (`Valid.nonDed_freshR_of_freshAt`) gives `o′ ⊬ n` and `o′ ⊬ m`, and Pc-Oracle gives
  `hideO ⊬ n`.

## References

* [CCS26] Hérouard, Jacomme, Koutsos, Lallemand, *Secrecy in Squirrel and the Post-Compromise
  Security of a Ratchet*, CCS 2026: Fig. 3 and App. C.1.
-/

public section

namespace Interop.Squirrel.OracleExamples

open IPFunctor IPFunctor.ScopedSignature SecrecyExamples FreshLExamples

/-! ## The oracles -/

/-- The honest symbol `h`, the identity in `longModel`, as an oracle. -/
@[expose] def hO : FTerm decl [] (.arrow msg msg) := FTerm.fn (D := decl) Fn.h

/-- `λx. if x ≠ m then h(x) else n`: the secret `n` behind the secret point `m`. -/
@[expose] def hideO : FTerm decl [] (.arrow msg msg) := FTerm.puncture hO (nm Name.m) (nm Name.n)

/-- `λx. if x ≠ a then h(x) else n`: the secret `n` behind the attacker's message `a`. -/
@[expose] def leakO : FTerm decl [] (.arrow msg msg) := FTerm.puncture hO aT (nm Name.n)

/-- The vector of one oracle. -/
abbrev oneO (o : FTerm decl [] (.arrow msg msg)) : Vec decl [] ([] ++ [.arrow msg msg]) :=
  Vec.snoc Env.empty o

variable {M : Model decl} {C : AdvClass M} {env : Env (Kind.Value M) []}

/-- The random variable of `hideO`. -/
theorem denote_hideO :
    hideO.denote (fullInterp M C) env = RV.puncture (fun η _ => M.fn η Fn.h)
      (M.nameAt (D := decl) Name.m Fn.idx) (M.nameAt (D := decl) Name.n Fn.idx) := by
  rw [hideO, FTerm.denote_puncture]
  rfl

/-- `hideO` reads only names and honest symbols, so nothing of the attacker tape. -/
theorem readsPoly_hideO : hideO.ReadsPoly M C env :=
  ⟨0, fun η ρa ρa' ρh _ => by rw [denote_hideO]; rfl⟩

/-- A term punctured at points that read below polynomials reads below a polynomial. -/
private theorem readsPoly_puncture {a b : Ty Unit} {o : FTerm decl [] (.arrow a b)}
    {m : FTerm decl [] a} {w : FTerm decl [] b} (ho : o.ReadsPoly M C env)
    (hm : m.ReadsPoly M C env) (hw : w.ReadsPoly M C env) :
    (FTerm.puncture o m w).ReadsPoly M C env := by
  obtain ⟨po, hpo⟩ := ho
  obtain ⟨pm, hpm⟩ := hm
  obtain ⟨pw, hpw⟩ := hw
  refine ⟨po + pm + pw, fun η ρa ρa' ρh hρ => ?_⟩
  have h₁ := hpo η ρa ρa' ρh fun i hi => hρ i (by
    dsimp only at hi ⊢; simp only [Polynomial.eval_add]; omega)
  have h₂ := hpm η ρa ρa' ρh fun i hi => hρ i (by
    dsimp only at hi ⊢; simp only [Polynomial.eval_add]; omega)
  have h₃ := hpw η ρa ρa' ρh fun i hi => hρ i (by
    dsimp only at hi ⊢; simp only [Polynomial.eval_add]; omega)
  rw [FTerm.denote_puncture]
  unfold RV.puncture
  rw [h₁, h₂, h₃]

/-! ## The agreement premise, from FreshR and Ineq -/

/-- The agreement of two oracles that differ only at `m`, at every message deducible from `h`: in
`longModel`, such a message is not `m`, overwhelmingly (FreshR gives `h ⊬ m`, then Ineq). -/
theorem valid_agree (o₁ o₂ : FTerm decl [] (.arrow msg msg))
    (h₁₂ : ∀ (C : AdvClass longModel) env η ρ x,
      o₁.denote (fullInterp longModel C) env η ρ x ≠ o₂.denote (fullInterp longModel C) env η ρ x →
        x = longModel.nameAt (D := decl) Name.m Fn.idx η ρ) :
    Valid (· = longModel) (fun M => AdvClass.all M) (Γ := []) []
      (Form.oracleAgree Env.empty hO o₁ o₂) := by
  rintro M - rfl env -
  refine Form.holds_oracleAgree.2 fun X hX => ?_
  have hm := (AdvClass.all longModel).nonDed_nameAt (D := decl) Name.m Fn.idx longModel_isLarge
    (u := VecRV.snoc (Vec.rv longModel (AdvClass.all longModel) (Env.empty : Vec decl [] []) env)
      (hO.denote (fullInterp longModel (AdvClass.all longModel)) env))
    fun _ _ _ _ _ => by
      funext τ x
      cases x with
      | zero => rfl
      | succ x => exact nomatch x
  exact negligible_of_le (fun η => prEvent_mono _ _ _ fun ρ hne => (h₁₂ _ env η ρ _ hne).symm)
    (hm.negligible_eq hX)

/-- `hideO` differs from `h` only at `m`. -/
theorem hideO_ne (C : AdvClass longModel) (env : Env (Kind.Value longModel) []) (η : ℕ) ρ x
    (h : hideO.denote (fullInterp longModel C) env η ρ x ≠
      hO.denote (fullInterp longModel C) env η ρ x) :
    x = longModel.nameAt (D := decl) Name.m Fn.idx η ρ := by
  rw [denote_hideO] at h
  unfold RV.puncture at h
  split_ifs at h with hx
  · exact absurd rfl h
  · exact not_not.1 hx

/-! ## Rw-Oracle -/

/-- FreshR for the oracle `h` on the left: `h ⊬ n`, since `h` uses no name. -/
theorem valid_h_nonDed :
    Valid (· = longModel) (fun M => AdvClass.all M) (Γ := []) [] (.nonDed (oneO hO) (nm Name.n)) :=
  Valid.nonDed_freshR (D := decl) Name.n Fn.idx rfl (by decide)

/-- **Rw-Oracle at `β = 2`, satisfiable.** In `longModel` against all machines, every hypothesis
holds jointly: long tapes, polynomial bit blocks for messages, the read bounds, `h ⊬ n`, and the
agreement of `hideO` and `h` at every message deducible from `h`; so `hideO ⊬ n` holds. -/
theorem valid_rwOracleWorked :
    Valid (· = longModel) (fun M => AdvClass.all M) (Γ := []) []
      (.nonDed (oneO hideO) (nm Name.n)) :=
  Valid.nonDed_rwOracle_of (oβ := hO) (o₂ := hO) (Ty.isGround_base ()) (Ty.isGround_base ())
    (.inr rfl) (fun _ hM => hM ▸ ⟨longModel_longTapes, longModel_polyCoins⟩)
    (fun _ _ _ _ _ => ⟨(fun _ x => nomatch x), readsPoly_hideO, FTerm.readsPoly_fn _⟩)
    valid_h_nonDed (valid_agree hideO hO hideO_ne)

/-- FreshR does not give the conclusion of `valid_rwOracleWorked`: `hideO` uses `n`. -/
theorem not_avoidsNames_hideO : ¬ (oneO hideO).AvoidsNames (· = ⟨_, _, Name.n⟩) := by
  decide +kernel

/-- **Rw-Oracle as in Fig. 3** (`β = 1`): from `hideO ⊬ k`, by FreshR since `hideO` does not use
`k`, and the agreement of `h` and `hideO` at every message deducible from `h`, conclude
`h ⊬ k`. -/
theorem valid_rwOracleFig3 :
    Valid (· = longModel) (fun M => AdvClass.all M) (Γ := []) [] (.nonDed (oneO hO) (nm Name.k)) :=
  Valid.nonDed_rwOracle (o₂ := hideO) (ho₂ := of_decide_eq_true rfl) (Ty.isGround_base ())
    (Ty.isGround_base ()) (fun _ hM => hM ▸ ⟨longModel_longTapes, longModel_polyCoins⟩)
    (fun _ _ _ _ _ => ⟨(fun _ x => nomatch x), FTerm.readsPoly_fn _, readsPoly_hideO⟩)
    (Valid.nonDed_freshR (D := decl) Name.k Fn.idx rfl (by decide +kernel))
    (valid_agree hO hideO fun C env η ρ x h => hideO_ne C env η ρ x (Ne.symm h))

/-! ## The agreement premise is needed -/

/-- The machine that queries its oracle at the attacker symbol's message, read from the tape by the
sampler of messages. -/
@[expose] noncomputable def queryAtA (M : Model decl) : AdvMachine M [.arrow msg msg] msg :=
  Machine.subst (as := []) (ρ := msg)
    (((Machine.input .zero (Ty.isGround_base ()) : Machine M [msg] msg).app
      (Ty.isGround_base ())).rename (Env.cons (.succ .zero) (Env.cons .zero Env.empty)))
    ((Machine.sampler msg (by decide)).rename (Renaming.ofGround (Ty.isGround_base ())))

/-- The sampler of messages, on the first `η` bits of the tape, computes the attacker symbol. -/
private theorem sample_coinAt_eq_att (η : ℕ) (ρa : longModel.TapeA η) :
    longModel.sample η msg (longModel.coinAt msg ρa 0) = longModel.att η () ρa := by
  refine Subtype.ext (congrArg List.ofFn (funext fun j => ?_))
  simp [Model.coinAt, Model.readBit, longModel]

/-- The machine queries its oracle at the sampler's message. -/
private theorem run_queryAtA (η : ℕ) (ρa : longModel.TapeA η)
    (e : Vals longModel η [.arrow msg msg]) :
    (queryAtA longModel).run η ρa (Env.append e Env.empty) =
      e _ .zero (longModel.sample η msg (longModel.coinAt msg ρa 0)) := by
  refine (Machine.run_subst _ _ _).trans ((Machine.run_rename _ _ _).trans
    ((Machine.run_app _ _ _).trans ((Machine.run_input _ _ _).trans ?_)))
  change e _ .zero ((Machine.rename _ (Machine.sampler msg _)).run η ρa _) = _
  rw [Machine.run_rename, Machine.run_sampler]
  rfl

private theorem queryAtA_mem : (AdvClass.all longModel).mem (queryAtA longModel) :=
  (AdvClass.all _).subst_mem ((AdvClass.all _).rename_mem _ ((AdvClass.all _).app_mem _
    ((AdvClass.all _).input_mem _ _))) ((AdvClass.all _).rename_mem _
      ((AdvClass.all _).sampler_mem _ longModel_polyCoins))

/-- **Rw-Oracle needs its agreement premise.** With the oracle `leakO`, which hides `n` behind the
attacker's message `a`, the premise `h ⊬ n` holds and so do the side conditions, but `leakO ⊬ n`
fails: the machine querying the oracle at `a` computes `n` on every tape. So the agreement of
`leakO` and `h` fails, whether the deduction is from `h` (`β = 2`) or from `leakO` (`β = 1`):
the two oracles differ at `a`, which the attacker deduces. -/
theorem rwOracle_needs_agree :
    Valid (· = longModel) (fun M => AdvClass.all M) (Γ := []) [] (.nonDed (oneO hO) (nm Name.n)) ∧
      ¬ Valid (· = longModel) (fun M => AdvClass.all M) (Γ := []) []
        (.nonDed (oneO leakO) (nm Name.n)) ∧
      ¬ Valid (· = longModel) (fun M => AdvClass.all M) (Γ := []) []
        (Form.oracleAgree Env.empty hO leakO hO) ∧
      ¬ Valid (· = longModel) (fun M => AdvClass.all M) (Γ := []) []
        (Form.oracleAgree Env.empty leakO leakO hO) := by
  have hfail : ¬ Valid (· = longModel) (fun M => AdvClass.all M) (Γ := []) []
      (.nonDed (oneO leakO) (nm Name.n)) := fun h => by
    have hn := Form.holds_nonDed.1 (h longModel longModel_respectsLabels rfl Env.empty (by simp))
    refine not_nonDed_of_forall_eq (queryAtA longModel) queryAtA_mem (fun η ρ => ?_) hn
    rw [AdvMachine.appVals_eval]
    refine (run_queryAtA η ρ.1 _).trans ?_
    change leakO.denote (fullInterp longModel (AdvClass.all longModel)) Env.empty η ρ _ = _
    rw [leakO, FTerm.denote_puncture]
    unfold RV.puncture
    split_ifs with hc
    · exact absurd (sample_coinAt_eq_att η ρ.1) hc
    · rfl
  have hread : ∀ M : Model decl, M.RespectsLabels → M = longModel → ∀ env,
      (∀ θ ∈ ([] : List (Form decl [])), θ.Holds M (AdvClass.all M) env) →
        Vec.ReadsPoly M (AdvClass.all M) (Env.empty : Vec decl [] []) env ∧
          leakO.ReadsPoly M (AdvClass.all M) env ∧ hO.ReadsPoly M (AdvClass.all M) env :=
    fun M hl hM env _ => by
      subst hM
      have ha : aT.ReadsPoly longModel (AdvClass.all _) env := FTerm.readsPoly_of_adv (τs := [])
        (Form.holds_adv.1 (valid_advA longModel hl rfl env (by simp)))
      exact ⟨(fun _ x => nomatch x), readsPoly_puncture (FTerm.readsPoly_fn _) ha
        ((FTerm.readsPoly_fn _).name _), FTerm.readsPoly_fn _⟩
  refine ⟨valid_h_nonDed, hfail, fun hag => hfail ?_, fun hag => hfail ?_⟩
  · exact Valid.nonDed_rwOracle_of (Ty.isGround_base ()) (Ty.isGround_base ()) (.inr rfl)
      (fun _ hM => hM ▸ ⟨longModel_longTapes, longModel_polyCoins⟩) hread valid_h_nonDed hag
  · exact Valid.nonDed_rwOracle (Ty.isGround_base ()) (Ty.isGround_base ())
      (fun _ hM => hM ▸ ⟨longModel_longTapes, longModel_polyCoins⟩) hread valid_h_nonDed hag

/-! ## Pc-Oracle -/

/-- `hideO` punctured at `m` back to `m`: the identity, though it is written with `m` and `n`. -/
theorem denote_puncture_hideO (C : AdvClass longModel) (env : Env (Kind.Value longModel) []) :
    (FTerm.puncture hideO (nm Name.m) (nm Name.m)).denote (fullInterp longModel C) env =
      fun η _ => longModel.fn η Fn.h := by
  funext η ρ x
  rw [FTerm.denote_puncture, denote_hideO]
  unfold RV.puncture
  split_ifs with h₁ h₂
  · rfl
  · exact absurd h₁ h₂
  · exact (not_not.1 h₁).symm

/-- FreshR for the punctured `hideO`, the identity: it uses the name `n` but reads no honest
coordinate, so the semantic freshness premise holds. -/
theorem valid_puncture_nonDed (x : Name .bool msg) :
    Valid (· = longModel) (fun M => AdvClass.all M) (Γ := []) []
      (.nonDed (oneO (FTerm.puncture hideO (nm Name.m) (nm Name.m))) (nm x)) :=
  Valid.nonDed_freshR_of_freshAt (D := decl) x Fn.idx rfl
    fun M _ hM env _ η ρa ρh ρh' _ => by
    subst hM
    funext τ y
    cases y with
    | zero =>
      change (FTerm.puncture hideO _ _).denote _ env η _ =
        (FTerm.puncture hideO _ _).denote _ env η _
      rw [denote_puncture_hideO]
    | succ y => exact nomatch y

/-- **Pc-Oracle, worked.** With `o′ = λx. if x ≠ m then hideO(x) else m`, which is the identity,
FreshR gives `o′ ⊬ n` and `o′ ⊬ m`, and Pc-Oracle gives `hideO ⊬ n`, the conclusion of
`valid_rwOracleWorked`, in `longModel` against all machines. -/
theorem valid_pcOracleWorked :
    Valid (· = longModel) (fun M => AdvClass.all M) (Γ := []) []
      (.nonDed (oneO hideO) (nm Name.n)) :=
  Valid.nonDed_pcOracle (m := nm Name.m) (w := nm Name.m) (Ty.isGround_base ())
    (Ty.isGround_base ()) (fun _ hM => hM ▸ ⟨longModel_longTapes, longModel_polyCoins⟩)
    (fun _ _ _ _ _ => ⟨(fun _ x => nomatch x), readsPoly_hideO, (FTerm.readsPoly_fn _).name _,
      (FTerm.readsPoly_fn _).name _⟩)
    (valid_puncture_nonDed Name.n) (valid_puncture_nonDed Name.m)

end Interop.Squirrel.OracleExamples
