/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Squirrel.Rules.Fresh
public import Interop.Squirrel.TapeBounds
import VCVio.OracleComp.EvalDist.Measure
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# A fresh name added on the left keeps a secret (FreshL)

CCS26's FreshL (Fig. 11, p. 17): from `u⃗ ⊬ v` conclude `u⃗, n ⊬ v`, when the name `n` is fresh in
`u⃗, v`. As for FreshR, the name is read at an honest symbol `i`, a closed index, and reads one
coordinate of the honest tape at each `η`.

CCS26's proof (App. C.2, pp. 16–17) turns a function `f` computing `v` from `u⃗, n_fresh` into a
function `f′` that "simulates the sampling of `n_fresh` from the adversarial randomness and then
runs `f`". Its footnote 2 makes room for that randomness by extending the attacker tape in a new
model and applying the premise there, "since the secrecy property `u ⊬ v` is assumed to hold in
any model". Here no model is extended. The reduction `AdvMachine.freshL` runs the attacker machine
`g` with the fresh name sampled from bits of the attacker tape of the same model, above a
polynomial `p` that bounds what `g` and the terms read; long tapes (`Model.LongTapes`) give those
bits at every large `η`. So the premise is used in the model where the conclusion is evaluated,
and the question whether the hypotheses `Θ` hold in an extended model does not arise.

* `deduceAdv_freshL_eq` is the concrete statement: at every `η` with
  `p(η) + coinLen η b ≤ lenA η`, the success of `g.freshL p` against `u ⊢ v` equals the success of
  `g` against `u, n ⊢ v`. Swapping the bit block `[p(η), p(η) + coinLen η b)` of the attacker tape
  with the coordinate of `n(i)` on the honest tape is a bijection of the tapes, so it preserves the
  uniform distribution; the machine and the terms read neither the block nor the coordinate, and
  the reduction reads exactly the block.
* `AdvClass.NonDed.freshL` is its asymptotic form: the two success probabilities agree eventually,
  and eventually equal functions are negligible together. It uses the closure fields
  `AdvClass.readBound_mem`, `shift_mem` and `sampler_mem` (through `AdvClass.freshL_mem`), and the
  model conditions `Model.LongTapes` and `Model.PolyCoins`.
* `Valid.nonDed_freshL` is the rule, for closed terms: they read the attacker tape below a
  polynomial in every admitted model of `Θ` (`FTerm.ReadsPoly`, discharged structurally by the
  lemmas of `Interop.Squirrel.TapeBounds`), and they do not use the name `n` (`FTerm.AvoidsNames`).

## References

* [CCS26] Hérouard, Jacomme, Koutsos, Lallemand, *Secrecy in Squirrel and the Post-Compromise
  Security of a Ratchet*, CCS 2026: Fig. 11 and App. C.2.
-/

public section

namespace Interop.Squirrel

open IPFunctor IPFunctor.ScopedSignature

variable {B : Type} {D : Decl B} {M : Model D} {τs : List (Ty B)} {a b β : Ty B}

/-! ## Swapping a bit block of the attacker tape with a coordinate of the honest tape -/

private theorem coinAt_setBlock {η : ℕ} (τ : Ty B) (o : ℕ) (ρa : M.TapeA η) (c : M.Coin η τ)
    (h : o + M.coinLen η τ ≤ M.lenA η) : M.coinAt τ (M.setBlock o ρa c) o = c :=
  M.bitsAt_setBlock o ρa c h

private theorem setBlock_coinAt {η : ℕ} (τ : Ty B) (o : ℕ) (ρa : M.TapeA η) :
    M.setBlock o ρa (M.coinAt τ ρa o) = ρa :=
  M.setBlock_bitsAt o ρa _

/-! ## FreshL at one security parameter -/

/-- **FreshL at `η`.** Let `g` be an attacker machine against `u, n(i) ⊢ v`, and `p` a polynomial
bounding the bits of the attacker tape that `g`, `u` and `v` read, with `n(i)` fresh in `u` and
`v`. At every `η` where the bit block `[p(η), p(η) + coinLen η b)` fits on the attacker tape, the
reduction `g.freshL p`, which samples the name from that block, computes `v` from `u` exactly as
often as `g` computes it from `u, n(i)`. -/
theorem deduceAdv_freshL_eq (n : D.Name a b) (i : D.Fn a) (p : Polynomial ℕ) (hb : b.order ≤ 1)
    (g : AdvMachine M (τs ++ [b]) β) {u : VecRV M τs} {v : RV M β}
    (hg : Machine.ReadsBelow g fun η => p.eval η) (hu : u.ReadsBelow fun η => p.eval η)
    (hv : v.ReadsBelow fun η => p.eval η) (hfu : M.FreshAt (M.nameSlot n i) u)
    (hfv : M.FreshAt (M.nameSlot n i) v) {η : ℕ} (hη : p.eval η + M.coinLen η b ≤ M.lenA η) :
    deduceAdv (g.freshL (fun η => p.eval η) hb).eval u v η =
      deduceAdv g.eval (VecRV.snoc u (M.nameAt n i)) v η := by
  classical
  let k := M.nameSlot n i η
  let σf : M.Tape η → M.Tape η := fun ρ =>
    (M.setBlock (p.eval η) ρ.1 (ρ.2 k), Function.update ρ.2 k (M.coinAt b ρ.1 (p.eval η)))
  have hσ : Function.Involutive σf := fun ρ => by
    simp only [σf, Function.update_self, coinAt_setBlock b _ _ _ hη, Model.setBlock_setBlock,
      setBlock_coinAt, Function.update_idem, Function.update_eq_self]
  refine (SampleableType.prEvent_uniformSample_equiv (Function.Involutive.toPerm σf hσ)
    _).symm.trans (prEvent_congr _ _ _ fun ρ => ?_)
  have hagree : ∀ j < p.eval η, M.readBit (M.setBlock (p.eval η) ρ.1 (ρ.2 k)) j =
      M.readBit ρ.1 j := fun j hj => M.readBit_setBlock_of_lt _ _ hj
  have hupd : ∀ k', k' ≠ M.nameSlot n i η →
      Function.update ρ.2 k (M.coinAt b ρ.1 (p.eval η)) k' = ρ.2 k' :=
    fun k' hk' => Function.update_of_ne hk' _ _
  have hu' : u η (σf ρ) = u η ρ := funext fun τ => funext fun x =>
    (hu τ x η _ _ _ hagree).trans (congrFun (congrFun (hfu η ρ.1 _ _ hupd) τ) x)
  have hv' : v η (σf ρ) = v η ρ := (hv η _ _ _ hagree).trans (hfv η ρ.1 _ _ hupd)
  change Ty.appVals ((g.freshL (fun η => p.eval η) hb).eval η (σf ρ).1) (u η (σf ρ)) = v η (σf ρ) ↔
    Ty.appVals (g.eval η ρ.1) (Env.append (u η ρ) (Env.cons (M.sample η b (ρ.2 k)) Env.empty)) =
      v η ρ
  rw [AdvMachine.appVals_eval_freshL, hu', hv']
  change Ty.appVals (g.eval η (M.setBlock (p.eval η) ρ.1 (ρ.2 k))) (Env.append (u η ρ)
      (Env.cons (M.sample η b (M.coinAt b (M.setBlock (p.eval η) ρ.1 (ρ.2 k)) (p.eval η)))
        Env.empty)) = v η ρ ↔ _
  rw [coinAt_setBlock b _ _ _ hη, AdvMachine.eval_eq_of_readsBelow hg hagree]

/-! ## FreshL -/

/-- **FreshL**, semantically (CCS26 Fig. 11, App. C.2): in a model with long attacker tapes and
polynomial bit blocks for names of type `b`, if `u ⊬ v` against the admitted machines, `u` and
`v` read the attacker tape below a polynomial, and `n(i)` is fresh in `u` and `v`, then
`u, n(i) ⊬ v`. The reduction is `AdvMachine.freshL` at the sum of the read bounds of the machine
and the terms (`deduceAdv_freshL_eq`). -/
theorem AdvClass.NonDed.freshL {C : AdvClass M} (hlong : M.LongTapes) (hc : M.PolyCoins b)
    (hb : b.order ≤ 1) (n : D.Name a b) (i : D.Fn a) {u : VecRV M τs} {v : RV M β}
    (hu : ∃ p : Polynomial ℕ, u.ReadsBelow fun η => p.eval η)
    (hv : ∃ p : Polynomial ℕ, v.ReadsBelow fun η => p.eval η)
    (hfu : M.FreshAt (M.nameSlot n i) u) (hfv : M.FreshAt (M.nameSlot n i) v)
    (h : C.NonDed u v) : C.NonDed (VecRV.snoc u (M.nameAt n i)) v := by
  intro g hg
  obtain ⟨pg, hpg⟩ := C.readBound_mem hg
  obtain ⟨pu, hpu⟩ := hu
  obtain ⟨pv, hpv⟩ := hv
  obtain ⟨pc, hpc⟩ := hc
  refine negligible_of_eventuallyLE ?_ (h _ (C.freshL_mem (pg + pu + pv) hb ⟨pc, hpc⟩ hg))
  filter_upwards [hlong (pg + pu + pv + pc)] with η hη
  refine le_of_eq (deduceAdv_freshL_eq n i (pg + pu + pv) hb g
    (hpg.mono fun η => by simp only [Polynomial.eval_add]; omega)
    (fun τ x => (hpu τ x).mono fun η => by simp only [Polynomial.eval_add]; omega)
    (hpv.mono fun η => by simp only [Polynomial.eval_add]; omega) hfu hfv ?_).symm
  have := hpc η
  simp only [Polynomial.eval_add] at hη ⊢
  omega

/-- **FreshL** (CCS26 Fig. 11, p. 17), for closed terms: from `u⃗ ⊬ v` conclude `u⃗, n(i) ⊬ v`,
over models with long attacker tapes and polynomial bit blocks for names of type `b`, when the
terms read the attacker tape below a polynomial in every admitted model of `Θ` and do not use the
name `n`. -/
theorem Valid.nonDed_freshL {R : Model D → Prop} {C : ∀ M : Model D, AdvClass M}
    {Θ : List (Form D [])} {u : Vec D [] τs} {v : FTerm D [] β} {ho : Ty.SecrecyOrder τs β}
    {ho' : Ty.SecrecyOrder (τs ++ [b]) β} (n : D.Name a b) (i : D.Fn a)
    (hR : ∀ M, R M → M.LongTapes ∧ M.PolyCoins b)
    (hread : ∀ M : Model D, M.RespectsLabels → R M → ∀ env, (∀ θ ∈ Θ, θ.Holds M (C M) env) →
      u.ReadsPoly M (C M) env ∧ v.ReadsPoly M (C M) env)
    (hfu : u.AvoidsNames (· = ⟨a, b, n⟩)) (hfv : v.AvoidsNames (· = ⟨a, b, n⟩))
    (h : Valid R C Θ (.nonDed u v ho)) :
    Valid R C Θ (.nonDed (Vec.snoc u (FTerm.name n (FTerm.fn i))) v ho') :=
  fun M hl hRM env hΘ => by
  obtain ⟨hlong, hc⟩ := hR M hRM
  obtain ⟨hru, hrv⟩ := hread M hl hRM env hΘ
  rw [Form.holds_nonDed, Vec.rv_snoc]
  exact (Form.holds_nonDed.1 (h M hl hRM env hΘ)).freshL hlong hc
    (ho'.1 b (List.mem_append_right _ (List.mem_singleton_self b))) n i
    hru.exists_readsBelow hrv (hfu.freshAt (fun _ => rfl) (C M) env)
    (hfv.freshAt (fun _ => rfl) (C M) env)

end Interop.Squirrel
