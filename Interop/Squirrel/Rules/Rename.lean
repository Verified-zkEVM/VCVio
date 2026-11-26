/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Squirrel.Global
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Renaming names

Renaming the names of a closed vector of terms gives an indistinguishable vector (BC14's
α-renaming of names). `Term.renameNames π` replaces every name `n` by `π n`; names are indexed by
their types, so `π` preserves types and the renaming needs no casts.

The rule holds wherever renaming the names is a bijection `σ` of the honest tapes: `n` reads
from `σ ρh` what `π n` reads from `ρh` (`Model.RenamesNames`). The uniform distribution is
invariant under `σ`, so every machine has advantage zero. Every model has such a `σ` for a
bijective renaming (`Model.renamesNames`): the honest tape has one coordinate per name and
index, and `σ` permutes the coordinates (`Model.tapePerm`). So `Valid.equiv_renameNames_of_equiv`
holds in every model.

The vectors must be closed: a free variable stands for any random variable, which may read the
honest tape, and then renaming is unsound.

## References

* [BC14] Bana, Comon-Lundh, *A Computationally Complete Symbolic Attacker for Equivalence
  Properties*, CCS 2014: α-renaming of names.
* [LICS23] Baelde, Koutsos, Lallemand, *A Higher-Order Indistinguishability Logic for
  Cryptographic Reasoning*, LICS 2023: §II-B.2.
-/

public section

namespace Interop.Squirrel

open IPFunctor IPFunctor.ScopedSignature

variable {B : Type} {D : Decl B}

/-- Replace every name `n` by `π n`. -/
@[expose] def Term.renameNames (π : ∀ {a b : Ty B}, D.Name a b → D.Name a b)
    {Γ : List (Kind B)} {s : Kind B} (t : (fullSig D).Term Γ s) : (fullSig D).Term Γ s :=
  t.fold (D := fun j : Judgment (Kind B) => (fullSig D).Term j.1 j.2) (fun _ x => .pure x)
    fun ⟨_, s⟩ o next => match s, o, next with
      | _, .inl (.name n), _ => .liftBind (.inl (.name (π n))) fun p => nomatch p
      | _, o, next => .liftBind o next

/-- Rename the names of every entry of a vector. -/
@[expose] def Vec.renameNames (π : ∀ {a b : Ty B}, D.Name a b → D.Name a b)
    {Γ : List (Kind B)} {τs : List (Ty B)} (u : Vec D Γ τs) : Vec D Γ τs :=
  fun _ x => Term.renameNames π (u _ x)

/-- Renaming names along `π` is the bijection `σ` of the honest tapes at `η`. -/
@[expose] def Model.RenamesNames (π : ∀ {a b : Ty B}, D.Name a b → D.Name a b) (M : Model D) :
    Prop :=
  ∀ η, ∃ σ : M.TapeH η ≃ M.TapeH η,
    ∀ {a b : Ty B} (n : D.Name a b) i ρh, M.name η (π n) i ρh = M.name η n i (σ ρh)

/-- Permute the coordinates of the honest tape along a bijective renaming of names. -/
@[expose] def Model.tapePerm (M : Model D) (η : ℕ) (π : ∀ {a b : Ty B}, D.Name a b ≃ D.Name a b) :
    M.TapeH η ≃ M.TapeH η where
  toFun ρh k := ρh ⟨⟨k.1.1, k.1.2.1, π k.1.2.2⟩, k.2⟩
  invFun ρh k := ρh ⟨⟨k.1.1, k.1.2.1, π.symm k.1.2.2⟩, k.2⟩
  left_inv ρh := funext fun ⟨⟨a, b, n⟩, i⟩ => by
    change ρh ⟨⟨a, b, π (π.symm n)⟩, i⟩ = ρh ⟨⟨a, b, n⟩, i⟩
    rw [π.apply_symm_apply]
  right_inv ρh := funext fun ⟨⟨a, b, n⟩, i⟩ => by
    change ρh ⟨⟨a, b, π.symm (π n)⟩, i⟩ = ρh ⟨⟨a, b, n⟩, i⟩
    rw [π.symm_apply_apply]

/-- A bijective renaming of names is the permutation `Model.tapePerm` of the honest tape. -/
theorem Model.renamesNames (M : Model D) (π : ∀ {a b : Ty B}, D.Name a b ≃ D.Name a b) :
    M.RenamesNames fun n => π n :=
  fun η => ⟨M.tapePerm η π, fun _ _ _ => by rfl⟩

variable {M : Model D} {π : ∀ {a b : Ty B}, D.Name a b → D.Name a b}

/-- Pointwise, renaming names along `π` reads the honest tape through `σ`. -/
private theorem denote_renameNames {η : ℕ} {σ : M.TapeH η ≃ M.TapeH η}
    (hσ : ∀ {a b : Ty B} (n : D.Name a b) i ρh, M.name η (π n) i ρh = M.name η n i (σ ρh))
    (ρ : M.Tape η) {Γ : List (Kind B)} {s : Kind B} (t : (fullSig D).Term Γ s)
    (e : Env (Kind.PtValue M η) Γ) :
    (Term.renameNames π t).denote (Interpretation.sum (interp M η ρ) (ptGlobal M η)) e =
      t.denote (Interpretation.sum (interp M η (ρ.1, σ ρ.2)) (ptGlobal M η)) e := by
  have h := IFreeM.fold_fusion (P := (fullSig D).polynomial)
    (D := fun j : Judgment (Kind B) => (fullSig D).Term j.1 j.2)
    (E := fun j : Judgment (Kind B) => Env (Kind.PtValue M η) j.1 → Kind.PtValue M η j.2)
    (fun _ t e => t.denote (Interpretation.sum (interp M η ρ) (ptGlobal M η)) e)
    (fun _ x => .pure x) (fun _ x e => e _ x)
    (fun ⟨_, s⟩ o next => match s, o, next with
      | _, .inl (.name n), _ => .liftBind (.inl (.name (π n))) fun p => nomatch p
      | _, o, next => .liftBind o next)
    (fun _ o next e => Interpretation.sum (interp M η (ρ.1, σ ρ.2)) (ptGlobal M η) o
      fun p ξ => next p (Env.append ξ e))
    (fun _ _ => rfl) ?_ t
  · exact congrFun h e
  rintro ⟨Γ, s⟩ (o | o) ds
  · cases o <;> first | rfl | (funext e i; exact hσ _ i ρ.2)
  · rfl

/-- A closed term with its names renamed reads the honest tape through `σ`. -/
theorem denote_renameNames_closed (C : AdvClass M) {η : ℕ} {σ : M.TapeH η ≃ M.TapeH η}
    (hσ : ∀ {a b : Ty B} (n : D.Name a b) i ρh, M.name η (π n) i ρh = M.name η n i (σ ρh))
    (ρ : M.Tape η) {τ : Ty B} (t : FTerm D [] τ) (env : Env (Kind.Value M) []) :
    (Term.renameNames π t).denote (fullInterp M C) env η ρ =
      t.denote (fullInterp M C) env η (ρ.1, σ ρ.2) := by
  have h₁ := eval_denote_fullInterp M C η ρ (Term.renameNames π t) env
  have h₂ := eval_denote_fullInterp M C η (ρ.1, σ ρ.2) t env
  refine h₁.trans ((denote_renameNames hσ ρ t _).trans (Eq.trans ?_ h₂.symm))
  rw [Env.eq_empty (evalEnv M η ρ env), Env.eq_empty (evalEnv M η (ρ.1, σ ρ.2) env)]

/-- **Name renaming.** In models where renaming names is a bijection of the honest tapes, a
closed vector is indistinguishable from its renaming: every machine has advantage zero. -/
theorem Valid.equiv_renameNames {R : Model D → Prop} {C : ∀ M : Model D, AdvClass M}
    (hR : ∀ M, R M → M.RenamesNames π) {Θ : List (Form D [])} {τs : List (Ty B)}
    (u : Vec D [] τs) {ho : Ty.IndistOrder τs} : Valid R C Θ (.equiv u (u.renameNames π) ho) := by
  intro M _ hRM env _
  refine Form.holds_equiv.2 fun A _ => negligible_of_zero fun η => ENNReal.absDiff_eq_zero.2 ?_
  obtain ⟨σ, hσ⟩ := hR M hRM η
  have hrv : ∀ ρ, Vec.rv M (C M) (u.renameNames π) env η ρ =
      Vec.rv M (C M) u env η (ρ.1, σ ρ.2) :=
    fun ρ => funext fun _ => funext fun x => denote_renameNames_closed (C M) hσ ρ (u _ x) env
  simp only [hrv]
  exact (SampleableType.prEvent_uniformSample_equiv ((Equiv.refl _).prodCongr σ)
    fun ρ => A.test η (Vec.rv M (C M) u env η ρ) ρ.1 = true).symm

/-- **Name renaming**, in every model: a closed vector is indistinguishable from its renaming
along a bijection of names. -/
theorem Valid.equiv_renameNames_of_equiv {R : Model D → Prop} {C : ∀ M : Model D, AdvClass M}
    (π : ∀ {a b : Ty B}, D.Name a b ≃ D.Name a b) {Θ : List (Form D [])} {τs : List (Ty B)}
    (u : Vec D [] τs) {ho : Ty.IndistOrder τs} :
    Valid R C Θ (.equiv u (u.renameNames fun n => π n) ho) :=
  Valid.equiv_renameNames (fun M _ => M.renamesNames π) u

end Interop.Squirrel
