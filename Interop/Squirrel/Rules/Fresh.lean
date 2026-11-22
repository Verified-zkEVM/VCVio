/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Squirrel.Rules.Secrecy
public import Interop.Squirrel.Avoids
import VCVio.OracleComp.EvalDist.Measure
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# A fresh name of a large type is secret (FreshR)

CCS26's FreshR (Fig. 11, p. 17): `u⃗ ⊬ n` when `large ∈ label(τ)` for the type `τ` of `n` and `n`
is fresh in `u⃗`. CCS26 presents un-indexed names. Here a name `n : τ₀ → τ` is read at an honest
symbol `i : τ₀`, a closed index whose value at `η` is `⟦i⟧_η`, and the name reads one coordinate
of the honest tape at each `η` (`Model.nameSlot`).

* `Model.FreshAt M k X`: a family over the tapes, such as a random variable or a vector of them,
  agrees at two honest tapes that agree outside the coordinate `k η`. A closed term that does not
  use the name of that coordinate (`FTerm.AvoidsNames`, syntactic and decidable) gives one
  (`FTerm.AvoidsNames.freshAt`, `Vec.AvoidsNames.freshAt`).
* `deduceAdv_nameAt_le` is the concrete statement: if `u` does not read the coordinate of `n(i)`,
  every attacker function, admitted or not, computes `n(i)` from `u` with probability at most the
  largest probability of one value of the sampler. Overwriting the coordinate with a fresh coin
  leaves the tape uniform (`SampleableType.prEvent_uniformSample_prod_update`), and for each tape
  the coin hits the attacker's guess with that probability.
* `AdvClass.nonDed_nameAt` is its asymptotic form. With the label `large` (`Model.IsLarge`,
  LICS23 App. A) the bound is `2^{-cη}`, which is negligible (`negligible_two_rpow_neg_mul`). It
  needs no closure field: the bound holds against every function of the attacker tape.
* `Valid.nonDed_freshR` is the rule, for a closed vector that does not use the name `n`. The
  freshness condition is CCS26's: `n` does not occur in `u⃗`. A closed vector is needed, because a
  free variable ranges over all random variables, which may read the name's coordinate.

FreshL (`u⃗ ⊬ v ⟹ u⃗, n ⊬ v` for `n` fresh in `u⃗, v`) is in `Interop.Squirrel.Rules.FreshL`.

## References

* [CCS26] Hérouard, Jacomme, Koutsos, Lallemand, *Secrecy in Squirrel and the Post-Compromise
  Security of a Ratchet*, CCS 2026: Fig. 11.
* [LICS23] Baelde, Koutsos, Lallemand, *A Higher-Order Indistinguishability Logic for
  Cryptographic Reasoning*, LICS 2023: §II-B.2 and App. A.
-/

public section

namespace Interop.Squirrel

open IPFunctor IPFunctor.ScopedSignature

variable {B : Type} {D : Decl B} {M : Model D} {τs : List (Ty B)} {a b τ : Ty B}

/-! ## Random variables that do not read a coordinate -/

/-- A family over the tapes, such as a random variable or a vector of them, does not read the
honest-tape coordinate `k η`: it agrees at two honest tapes that agree outside it. -/
@[expose] def Model.FreshAt (M : Model D) {α : ℕ → Type} (k : (η : ℕ) → M.Slot η)
    (X : (η : ℕ) → M.Tape η → α η) : Prop :=
  ∀ η ρa (ρh ρh' : M.TapeH η), (∀ k', k' ≠ k η → ρh k' = ρh' k') → X η (ρa, ρh) = X η (ρa, ρh')

/-- The random variable of a closed term that does not use the names `N` does not read a
coordinate of a name in `N`: two honest tapes that agree outside it differ by one update. -/
theorem FTerm.AvoidsNames.freshAt {N : ((a : Ty B) × (b : Ty B) × D.Name a b) → Prop}
    {t : FTerm D [] τ} (h : t.AvoidsNames N) {k : (η : ℕ) → M.Slot η} (hk : ∀ η, N (k η).1)
    (C : AdvClass M) (env : Env (Kind.Value M) []) :
    M.FreshAt k (t.denote (fullInterp M C) env) := fun η ρa ρh ρh' hρ => by
  classical
  have hu : ρh' = Function.update (β := fun k : M.Slot η => M.Coin η k.1.2.1) ρh (k η)
      (ρh' (k η)) := funext fun k' => by
    by_cases hk' : k' = k η
    · subst hk'
      rw [Function.update_self]
    · rw [Function.update_of_ne hk', hρ k' hk']
  have h₁ := eval_denote_fullInterp M C η (ρa, ρh) t env
  have h₂ := eval_denote_fullInterp M C η (ρa, ρh') t env
  rw [Env.eq_empty (evalEnv M η (ρa, ρh) env)] at h₁
  rw [Env.eq_empty (evalEnv M η (ρa, ρh') env)] at h₂
  refine h₁.trans (Eq.trans ?_ h₂.symm)
  rw [hu, FTerm.denote_update_eq_of_avoidsNames h M ρa ρh (hk η)]

/-- The vector of a closed vector of terms that do not use the names `N` does not read a
coordinate of a name in `N`. -/
theorem Vec.AvoidsNames.freshAt {N : ((a : Ty B) × (b : Ty B) × D.Name a b) → Prop}
    {u : Vec D [] τs} (h : u.AvoidsNames N) {k : (η : ℕ) → M.Slot η} (hk : ∀ η, N (k η).1)
    (C : AdvClass M) (env : Env (Kind.Value M) []) : M.FreshAt k (u.rv M C env) :=
  fun η ρa ρh ρh' hρ => funext fun τ => funext fun x =>
    (h τ x).freshAt hk C env η ρa ρh ρh' hρ

/-! ## The name and its sampler -/

/-- The random variable of the name `n` read at the honest index `i`. -/
@[expose] def Model.nameAt (M : Model D) (n : D.Name a b) (i : D.Fn a) : RV M b :=
  fun η ρ => M.name η n (M.fn η i) ρ.2

/-- The name `n(i)` over uniform tapes follows its sampler on a uniform bit block: the marginal of
the honest tape's coordinate. -/
theorem prEvent_nameAt (n : D.Name a b) (i : D.Fn a) (η : ℕ) (q : b.Value M.carrier η → Prop) :
    Pr{let ρ ← $ᵗ (M.Tape η)}[q (M.nameAt n i η ρ)] =
      Pr{let c ← $ᵗ (M.Coin η b)}[q (M.sample η b c)] := by
  classical
  have := D.finite_names
  have : ∀ n : (a : Ty B) × (b : Ty B) × D.Name a b, Finite (n.1.Value M.carrier η) :=
    fun n => M.finite_index η n.2.2
  have h := SampleableType.prEvent_uniformSample_prod_update (β := M.TapeA η)
    (R := fun k : M.Slot η => M.Coin η k.1.2.1) (M.nameSlot n i η)
    fun ρ => q (M.nameAt n i η ρ)
  simp only [Model.nameAt, Model.name, Function.update_self] at h
  exact h.symm.trans ((SampleableType.prEvent_uniformSample_prod (α := M.Coin η b)
    (β := M.Tape η) fun z => q (M.sample η b z.1)).symm.trans
    (SampleableType.prEvent_uniformSample_fst (β := M.Tape η) fun c => q (M.sample η b c)))

/-! ## FreshR -/

/-- **FreshR at `η`.** If the vector `u` does not read the coordinate of `n(i)`, every attacker
function computes `n(i)` from `u` with probability at most a bound `ε` on the probability of each
value of the sampler. -/
theorem deduceAdv_nameAt_le (n : D.Name a b) (i : D.Fn a) (g : AttackerFn M (Ty.arrows τs b))
    {u : VecRV M τs} (hu : M.FreshAt (M.nameSlot n i) u) (η : ℕ) {ε : ENNReal}
    (hε : ∀ y, Pr{let r ← $ᵗ (M.Coin η b)}[M.sample η b r = y] ≤ ε) :
    deduceAdv g u (M.nameAt n i) η ≤ ε := by
  classical
  have := D.finite_names
  have : ∀ n : (a : Ty B) × (b : Ty B) × D.Name a b, Finite (n.1.Value M.carrier η) :=
    fun n => M.finite_index η n.2.2
  rw [deduceAdv, ← SampleableType.prEvent_uniformSample_prod_update (β := M.TapeA η)
    (R := fun k : M.Slot η => M.Coin η k.1.2.1) (M.nameSlot n i η)]
  have hev : ∀ (c : M.Coin η b) (ρ : M.Tape η),
      Ty.appVals (g η ρ.1) (u η (ρ.1, Function.update ρ.2 (M.nameSlot n i η) c)) =
          M.nameAt n i η (ρ.1, Function.update ρ.2 (M.nameSlot n i η) c) ↔
        Ty.appVals (g η ρ.1) (u η ρ) = M.sample η b c := fun c ρ => by
    rw [hu η ρ.1 _ ρ.2 fun k hk => Function.update_of_ne hk _ _]
    simp only [Model.nameAt, Model.name, Function.update_self]
  refine (prEvent_bind_congr_of_forall _ _ _ _ _ fun c =>
    prEvent_congr _ _ _ (hev c)).trans_le ?_
  refine (SampleableType.prEvent_uniformSample_prod (α := M.Coin η b) (β := M.Tape η)
    fun z => Ty.appVals (g η z.2.1) (u η z.2) = M.sample η b z.1).symm.trans_le ?_
  refine SampleableType.prEvent_uniformSample_prod_le_of_forall_snd _ fun ρ => ?_
  exact le_of_eq_of_le (prEvent_congr _ _ _ fun _ => eq_comm) (hε (Ty.appVals (g η ρ.1) (u η ρ)))

/-- **FreshR**, semantically: a name of a large type is secret from every vector that does not
read its coordinate, against every attacker machine, admitted or not. -/
theorem AdvClass.nonDed_nameAt (C : AdvClass M) (n : D.Name a b) (i : D.Fn a)
    (hb : M.IsLarge b) {u : VecRV M τs} (hu : M.FreshAt (M.nameSlot n i) u) :
    C.NonDed u (M.nameAt n i) := fun g _ => by
  obtain ⟨c, hc, hle⟩ := hb
  exact negligible_of_le (fun η => deduceAdv_nameAt_le n i g.eval hu η (hle η))
    (negligible_two_rpow_neg_mul hc)

/-- **FreshR** (CCS26 Fig. 11, p. 17), for a closed vector: `u⃗ ⊬ n(i)` when the type of `n` is
labelled `large` and no term of `u⃗` uses the name `n`. -/
theorem Valid.nonDed_freshR {R : Model D → Prop} {C : ∀ M : Model D, AdvClass M}
    {Θ : List (Form D [])} {u : Vec D [] τs} {ho : Ty.SecrecyOrder τs b} (n : D.Name a b)
    (i : D.Fn a) (hlarge : b.HasLabel D.labels .large) (hfresh : u.AvoidsNames (· = ⟨a, b, n⟩)) :
    Valid R C Θ (.nonDed u (FTerm.name n (FTerm.fn i)) ho) := fun M hl _ env _ =>
  Form.holds_nonDed.2 ((C M).nonDed_nameAt n i (M.isLarge_of_hasLabel hl hlarge)
    (hfresh.freshAt (fun _ => rfl) (C M) env))

end Interop.Squirrel
