/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Squirrel.Secrecy

/-!
# The core rules of non-deduction and deduction

The rules of CCS26 Fig. 3 (p. 7) about `⊬` and `▷` (`Form.nonDed`, `Form.ded`) other than
Rw-Oracle and Pc-Oracle, as statements about validity: `Valid.not_ded` (Neg1),
`Valid.not_nonDed` (Neg2), `Valid.box_not_eq` (Ineq), `Valid.ded_trans` (Trans),
`Valid.nonDed_weakL` (WeakL), `Valid.nonDed_weakR` (WeakR) and `Valid.nonDed_rwEquiv`
(Rw-Equiv). A term in the middle of Trans or WeakL is on the right of a `▷`, so it is a single
term, written as the vector `[v]`. `Valid.ded_apps` concludes `u⃗ ▷ f(u⃗)` from `adv(f)`: the
definition of `▷`, with `f` as its witness.

Each rule reads its premises and conclusion with `Form.holds_nonDed` and `Form.holds_ded`, and
applies one law of `Interop.Squirrel.Secrecy`, whose proof is an inequality at every `η` with the
reduction named. Rw-Equiv is stated for a right side of Boolean or base type, where its
distinguisher can test `f(u⃗) = v`.

## References

* [CCS26] Hérouard, Jacomme, Koutsos, Lallemand, *Secrecy in Squirrel and the Post-Compromise
  Security of a Ratchet*, CCS 2026: §3.1 and Fig. 3.
-/

public section

namespace Interop.Squirrel

open IPFunctor IPFunctor.ScopedSignature

namespace Valid

variable {B : Type} {D : Decl B} {Γ : List (Kind B)} {τs : List (Ty B)} {β γ : Ty B}
  {R : Model D → Prop} {C : ∀ M : Model D, AdvClass M} {Θ : List (Form D Γ)} {u : Vec D Γ τs}
  {v w : FTerm D Γ β}

/-- **Neg1** (CCS26 Fig. 3): from `u⃗ ⊬ v`, conclude `¬ (u⃗ ▷ v)`. -/
theorem not_ded {ho : Ty.SecrecyOrder τs β} (h : Valid R C Θ (.nonDed u v ho)) :
    Valid R C Θ (.not (.ded u v ho)) :=
  fun M hl hR env hΘ => Form.holds_not.2 fun hd =>
    (Form.holds_nonDed.1 (h M hl hR env hΘ)).not_ded (Form.holds_ded.1 hd)

/-- **Neg2** (CCS26 Fig. 3): from `u⃗ ▷ v`, conclude `¬ (u⃗ ⊬ v)`. -/
theorem not_nonDed {ho : Ty.SecrecyOrder τs β} (h : Valid R C Θ (.ded u v ho)) :
    Valid R C Θ (.not (.nonDed u v ho)) :=
  fun M hl hR env hΘ => Form.holds_not.2 fun hn =>
    (Form.holds_ded.1 (h M hl hR env hΘ)).not_nonDed (Form.holds_nonDed.1 hn)

/-- **Ineq** (CCS26 Fig. 3): from `u⃗ ⊬ v` and `u⃗ ▷ w`, conclude `[v ≠ w]`. -/
theorem box_not_eq {ho : Ty.SecrecyOrder τs β} (h : Valid R C Θ (.nonDed u v ho))
    (h' : Valid R C Θ (.ded u w ho)) :
    Valid R C Θ (.box (FTerm.not (FTerm.eq v w))) := fun M hl hR env hΘ =>
  Form.holds_box.2 (negligible_of_le (fun η => prEvent_mono _ _ _ fun ρ hρ =>
      (FTerm.denote_not_eq_eq_false_iff v w η ρ).1 hρ)
    ((Form.holds_nonDed.1 (h M hl hR env hΘ)).negligible_eq (Form.holds_ded.1 (h' M hl hR env hΘ))))

/-- **Trans** (CCS26 Fig. 3): from `u⃗ ▷ v` and `v ▷ w`, conclude `u⃗ ▷ w`. -/
theorem ded_trans {w : FTerm D Γ γ} {ho₁ : Ty.SecrecyOrder τs β} {ho₂ : Ty.SecrecyOrder [β] γ}
    (h₁ : Valid R C Θ (.ded u v ho₁)) (h₂ : Valid R C Θ (.ded (Env.cons v Env.empty) w ho₂)) :
    Valid R C Θ (.ded u w ⟨ho₁.1, ho₂.2⟩) := by
  intro M hl hR env hΘ
  have h₂' := Form.holds_ded.1 (h₂ M hl hR env hΘ)
  rw [Vec.rv_single] at h₂'
  exact Form.holds_ded.2 ((Form.holds_ded.1 (h₁ M hl hR env hΘ)).trans h₂')

/-- **WeakL** (CCS26 Fig. 3): from `u⃗ ⊬ w` and `u⃗ ▷ v`, conclude `v ⊬ w`. -/
theorem nonDed_weakL {w : FTerm D Γ γ} {ho₁ : Ty.SecrecyOrder τs γ}
    {ho₂ : Ty.SecrecyOrder τs β} (h : Valid R C Θ (.nonDed u w ho₁))
    (h' : Valid R C Θ (.ded u v ho₂)) :
    Valid R C Θ (.nonDed (Env.cons v Env.empty) w ⟨.single ho₂.2, ho₁.2⟩) := by
  intro M hl hR env hΘ
  rw [Form.holds_nonDed, Vec.rv_single]
  exact (Form.holds_nonDed.1 (h M hl hR env hΘ)).weakL (Form.holds_ded.1 (h' M hl hR env hΘ))

/-- **WeakR** (CCS26 Fig. 3): from `u⃗ ⊬ v` and `w ▷ v`, conclude `u⃗ ⊬ w`. -/
theorem nonDed_weakR {w : FTerm D Γ γ} {ho₁ : Ty.SecrecyOrder τs β}
    {ho₂ : Ty.SecrecyOrder [γ] β} (h : Valid R C Θ (.nonDed u v ho₁))
    (h' : Valid R C Θ (.ded (Env.cons w Env.empty) v ho₂)) :
    Valid R C Θ (.nonDed u w ⟨ho₁.1, ho₂.1.head⟩) := by
  intro M hl hR env hΘ
  have h'' := Form.holds_ded.1 (h' M hl hR env hΘ)
  rw [Vec.rv_single] at h''
  exact Form.holds_nonDed.2 ((Form.holds_nonDed.1 (h M hl hR env hΘ)).weakR h'')

/-- **Rw-Equiv** (CCS26 Fig. 3), for a right side of Boolean or base type: from `u⃗₂ ⊬ v₂` and
`u⃗₁, v₁ ∼ u⃗₂, v₂`, conclude `u⃗₁ ⊬ v₁`. -/
theorem nonDed_rwEquiv (hβ : β.IsGround) {u₁ u₂ : Vec D Γ τs} {v₁ v₂ : FTerm D Γ β}
    {ho : Ty.SecrecyOrder τs β} {hoE : Ty.IndistOrder (τs ++ [β])}
    (h : Valid R C Θ (.nonDed u₂ v₂ ho))
    (h' : Valid R C Θ (.equiv (Vec.snoc u₁ v₁) (Vec.snoc u₂ v₂) hoE)) :
    Valid R C Θ (.nonDed u₁ v₁ ho) := fun M hl hR env hΘ => by
  have hI := Form.holds_equiv.1 (h' M hl hR env hΘ)
  rw [Vec.rv_snoc, Vec.rv_snoc] at hI
  exact Form.holds_nonDed.2 ((Form.holds_nonDed.1 (h M hl hR env hΘ)).rwEquiv hβ hI)

/-- `u⃗ ▷ f(u⃗)` from `adv(f)`: the definition of `▷`, with `f` as the witness. -/
theorem ded_apps {f : FTerm D Γ (Ty.arrows τs β)} {ha : Ty.AdvOrder τs β}
    {ho : Ty.SecrecyOrder τs β} (hf : Valid R C Θ (.adv f ha)) :
    Valid R C Θ (.ded u (FTerm.apps f u) ho) := fun M hl hR env hΘ => by
  obtain ⟨g, hg, hfg⟩ := Form.holds_adv.1 (hf M hl hR env hΘ)
  refine Form.holds_ded.2 ⟨g, hg, negligible_of_zero fun η =>
    prEvent_eq_zero_of_forall_not _ _ fun ρ hρ => hρ ?_⟩
  rw [FTerm.denote_apps]
  exact congrArg (fun x => Ty.appVals x _) (hfg η ρ).symm

end Valid

end Interop.Squirrel
