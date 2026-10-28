/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.Projection
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Standard group models and evaluation morphisms

Discrete, pairing, symbolic and free models, with their product tracking models.
-/

public section

open OracleComp OracleSpec

namespace GroupModel

/-- The symbolic model of any signature: every sort is the polynomial ring, every linear
structure map is the identity and every bilinear one is multiplication. -/
noncomputable def symbolic (F : Type) [CommSemiring F] {S : Type} (σ : Sig S) (ι : Type) :
    Model F σ (fun _ => MvPolynomial ι F) where
  lin _ := LinearMap.id
  bil _ := LinearMap.mul F (MvPolynomial ι F)

/-- A family of types indexed by the pairing sorts. -/
@[expose] def PFam (A₁ A₂ Aₜ : Type) : PSort → Type
  | .g₁ => A₁
  | .g₂ => A₂
  | .gₜ => Aₜ

/-- The pairing family inherits the additive structures of its three carriers. -/
instance {A₁ A₂ Aₜ : Type} [AddCommMonoid A₁] [AddCommMonoid A₂] [AddCommMonoid Aₜ] :
    ∀ s, AddCommMonoid (PFam A₁ A₂ Aₜ s)
  | .g₁ => inferInstanceAs (AddCommMonoid A₁)
  | .g₂ => inferInstanceAs (AddCommMonoid A₂)
  | .gₜ => inferInstanceAs (AddCommMonoid Aₜ)

/-- The pairing family inherits the module structures of its three carriers. -/
instance {F A₁ A₂ Aₜ : Type} [CommSemiring F] [AddCommMonoid A₁] [AddCommMonoid A₂]
    [AddCommMonoid Aₜ] [Module F A₁] [Module F A₂] [Module F Aₜ] :
    ∀ s, Module F (PFam A₁ A₂ Aₜ s)
  | .g₁ => inferInstanceAs (Module F A₁)
  | .g₂ => inferInstanceAs (Module F A₂)
  | .gₜ => inferInstanceAs (Module F Aₜ)

section Pairing

variable {F G₁ G₂ Gₜ : Type} [CommSemiring F] [AddCommMonoid G₁] [AddCommMonoid G₂]
  [AddCommMonoid Gₜ] [Module F G₁] [Module F G₂] [Module F Gₜ]

/-- The real model of a pairing group: the pairing is a Mathlib bilinear map. -/
def pairingReal (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) : Model F pairingSig (PFam G₁ G₂ Gₜ) where
  lin o := o.elim
  bil _ := e

/-- Representations in the source sorts: a coefficient per handle of that sort. -/
abbrev Repr (F : Type) := Handle → F

/-- Representations in the target sort: a coefficient per target handle and a coefficient per
pair of a first-source handle and a second-source handle. -/
abbrev ReprT (F : Type) := (Handle → F) × (Handle → Handle → F)

/-- The outer product of two source representations, as a bilinear map. -/
def outer (F : Type) [CommSemiring F] : Repr F →ₗ[F] Repr F →ₗ[F] ReprT F :=
  LinearMap.mk₂ F (fun r₁ r₂ => (0, fun i j => r₁ i * r₂ j))
    (by intro a b c; ext <;> simp [add_mul])
    (by intro c a b; ext <;> simp [mul_assoc])
    (by intro a b c; ext <;> simp [mul_add])
    (by intro c a b; ext <;> simp [mul_left_comm])

/-- The free model on given elements: representations only. -/
@[expose] def free.pairing (F : Type) [CommSemiring F] :
    Model F pairingSig (PFam (Repr F) (Repr F) (ReprT F)) where
  lin o := o.elim
  bil _ := outer F

/-- Evaluate a source representation on a list of given elements. -/
def evRepr {G : Type} [AddCommMonoid G] [Module F G] (xs : List G) : Repr F →ₗ[F] G :=
  ∑ i ∈ Finset.range xs.length, (LinearMap.proj (R := F) (φ := fun _ : Handle => F) i).smulRight
    (xs.getD i 0)

/-- Source evaluation is the finite weighted sum of the supplied values. -/
theorem evRepr_apply {G : Type} [AddCommMonoid G] [Module F G] (xs : List G) (r : Repr F) :
    evRepr xs r = ∑ i ∈ Finset.range xs.length, r i • xs.getD i 0 := by
  simp [evRepr, LinearMap.sum_apply]

/-- Evaluate a target representation: the linear part on the given target elements, the
bilinear part on the pairings of the given source elements. -/
def evReprT (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (xs : List G₁) (ys : List G₂) (zs : List Gₜ) :
    ReprT F →ₗ[F] Gₜ :=
  (evRepr zs).comp (LinearMap.fst F (Repr F) (Handle → Handle → F)) +
    ∑ i ∈ Finset.range xs.length, ∑ j ∈ Finset.range ys.length,
      ((LinearMap.proj (R := F) (φ := fun _ : Handle => F) j).comp
        ((LinearMap.proj (R := F) (φ := fun _ : Handle => Handle → F) i).comp
          (LinearMap.snd F (Repr F) (Handle → Handle → F)))).smulRight
        (e (xs.getD i 0) (ys.getD j 0))

/-- Target evaluation sums the linear part and the paired source contributions. -/
theorem evReprT_apply (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (xs : List G₁) (ys : List G₂) (zs : List Gₜ)
    (r : ReprT F) :
    evReprT e xs ys zs r = evRepr zs r.1 +
      ∑ i ∈ Finset.range xs.length, ∑ j ∈ Finset.range ys.length,
        r.2 i j • e (xs.getD i 0) (ys.getD j 0) := by
  simp [evReprT, LinearMap.sum_apply]

/-- Evaluating an outer product agrees with pairing the source evaluations. -/
theorem evReprT_outer (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (xs : List G₁) (ys : List G₂) (zs : List Gₜ)
    (r₁ r₂ : Repr F) :
    evReprT e xs ys zs (outer F r₁ r₂) = e (evRepr xs r₁) (evRepr ys r₂) := by
  simp only [evReprT_apply, evRepr_apply, outer, LinearMap.mk₂_apply, map_sum,
    LinearMap.sum_apply, mul_smul, Finset.smul_sum, map_smul, LinearMap.smul_apply,
    Pi.zero_apply, zero_smul, Finset.sum_const_zero, zero_add]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => smul_comm _ _ _

/-- Evaluation on the given elements is a morphism from the free model to the real model. -/
def evHom.pairing (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (xs : List G₁) (ys : List G₂) (zs : List Gₜ) :
    (free.pairing F).Hom (pairingReal e) where
  toFun
    | .g₁ => (evRepr xs : Repr F →ₗ[F] G₁)
    | .g₂ => (evRepr ys : Repr F →ₗ[F] G₂)
    | .gₜ => (evReprT e xs ys zs : ReprT F →ₗ[F] Gₜ)
  map_lin o := o.elim
  map_bil _ r₁ r₂ := by
    exact evReprT_outer e xs ys zs r₁ r₂

/-- A given element is the value of its own basis representation. -/
theorem evRepr_single {G : Type} [AddCommMonoid G] [Module F G]
    (xs : List G) (i : Handle) (hi : i < xs.length) :
    evRepr (F := F) xs (Pi.single i 1) = xs.getD i 0 := by
  simp [evRepr_apply, Pi.single_apply, hi]

end Pairing

section Evaluation

variable {F : Type} [Field F] {G₁ G₂ Gₜ : Type} [AddCommGroup G₁] [AddCommGroup G₂]
  [AddCommGroup Gₜ] [Module F G₁] [Module F G₂] [Module F Gₜ]

/-- Evaluate a polynomial at `x` and scale a fixed element by the value. -/
noncomputable def evalAt {ι G : Type} [AddCommGroup G] [Module F G] (g : G) (x : ι → F) :
    MvPolynomial ι F →ₗ[F] G :=
  (LinearMap.toSpanSingleton F G g).comp (MvPolynomial.aeval x).toLinearMap

/-- Polynomial evaluation scales the chosen module element by its value at the point. -/
theorem evalAt_apply {ι G : Type} [AddCommGroup G] [Module F G] (g : G) (x : ι → F)
    (P : MvPolynomial ι F) : evalAt g x P = MvPolynomial.eval x P • g := by
  simp [evalAt, LinearMap.toSpanSingleton_apply, MvPolynomial.aeval_eq_eval]

/-- Evaluating at `x` and scaling the generators is a morphism from the symbolic model to the
real model: the hidden-real run on polynomials is the real run on their values. -/
noncomputable def evalHom.pairing {ι : Type} (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (x : ι → F) : (symbolic F pairingSig ι).Hom (pairingReal e) where
  toFun
    | .g₁ => (evalAt g₁ x : MvPolynomial ι F →ₗ[F] G₁)
    | .g₂ => (evalAt g₂ x : MvPolynomial ι F →ₗ[F] G₂)
    | .gₜ => (evalAt (e g₁ g₂) x : MvPolynomial ι F →ₗ[F] Gₜ)
  map_lin o := o.elim
  map_bil _ P Q := by
    change evalAt (e g₁ g₂) x (P * Q) = e (evalAt g₁ x P) (evalAt g₂ x Q)
    simp only [evalAt_apply, map_mul, mul_smul, map_smul, LinearMap.smul_apply]
    rw [smul_comm]

end Evaluation

/-! ## Discrete models and tracking products -/

/-- The model of independent modules, with no structure maps. -/
@[expose] def Model.discrete {F : Type} [CommSemiring F] {S : Type} (G : S → Type)
    [∀ s, AddCommMonoid (G s)] [∀ s, Module F (G s)] : Model F (discreteSig S) G where
  lin o := o.elim
  bil o := o.elim

/-- The model of a single module. -/
@[expose] def Model.group {F : Type} [CommSemiring F] (G : Type)
    [AddCommMonoid G] [Module F G] :
    Model F groupSig (fun _ => G) := Model.discrete (fun _ => G)

/-- Free representations for independent sorts. -/
@[expose] def free.discrete (F S : Type) [CommSemiring F] :
    Model F (discreteSig S) (fun _ => Repr F) := Model.discrete _

/-- Free representations for a single group. -/
@[expose] def free.group (F : Type) [CommSemiring F] :
    Model F groupSig (fun _ => Repr F) := free.discrete F Unit

/-- Evaluation of free representations in independent modules. -/
def evHom.discrete {F S : Type} [CommSemiring F] {G : S → Type}
    [∀ s, AddCommMonoid (G s)] [∀ s, Module F (G s)] (xs : (s : S) → List (G s)) :
    (free.discrete F S).Hom (Model.discrete G) where
  toFun s := evRepr (xs s)
  map_lin o := o.elim
  map_bil o := o.elim

/-- Polynomial evaluation at a point in each independent module. -/
noncomputable def evalHom.discrete {F S ι : Type} [Field F] {G : S → Type}
    [∀ s, AddCommGroup (G s)] [∀ s, Module F (G s)] (g : (s : S) → G s) (x : ι → F) :
    (symbolic F (discreteSig S) ι).Hom (Model.discrete G) where
  toFun s := evalAt (g s) x
  map_lin o := o.elim
  map_bil o := o.elim

/-- Track a representation alongside every element of an independent module. -/
@[expose] def tracking {F S : Type} [CommSemiring F] {G : S → Type}
    [∀ s, AddCommMonoid (G s)] [∀ s, Module F (G s)] (M : Model F (discreteSig S) G) :
    Model F (discreteSig S) (fun s => Repr F × G s) := (free.discrete F S).prod M

/-- Tracking in one group. -/
@[expose] def tracking.group {F G : Type} [CommSemiring F] [AddCommMonoid G] [Module F G]
    (M : Model F groupSig (fun _ => G)) : Model F groupSig (fun _ => Repr F × G) :=
  tracking M

/-- Tracking source and target representations in a pairing model. -/
@[expose] def tracking.pairing {F G₁ G₂ Gₜ : Type} [CommSemiring F]
    [AddCommMonoid G₁] [AddCommMonoid G₂] [AddCommMonoid Gₜ]
    [Module F G₁] [Module F G₂] [Module F Gₜ] (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) :=
  (free.pairing F).prod (pairingReal e)

/-- Forgetting representations commutes with a generic run on independent sorts. -/
theorem runGen_tracking_map_snd {F S : Type} [CommSemiring F] [DecidableEq S]
    {G : S → Type} [∀ s, AddCommMonoid (G s)] [∀ s, Module F (G s)]
    [∀ s, DecidableEq (G s)] (M : Model F (discreteSig S) G) {α : Type}
    (oa : OracleComp (genSpec F (discreteSig S)) α) (tbl : Tbl (fun s => Repr F × G s)) :
    Prod.map id (mapTbl fun _ => Prod.snd) <$> runGen (tracking M) (fun _ => Prod.snd) oa tbl =
      runGen M (fun _ => id) oa (mapTbl (fun _ => Prod.snd) tbl) := by
  have hsnd : (fun s => ⇑((Model.Hom.snd (free.discrete F S) M).toFun s)) =
      (fun _ => Prod.snd) := by
    funext s x
    exact Model.Hom.snd_apply _ _ _ _
  simpa only [hsnd, Function.comp_def, id_eq, tracking] using
    runGen_map (Model.Hom.snd (free.discrete F S) M) (fun _ => id) oa tbl

/-- Forgetting representations commutes with a generic pairing run. -/
theorem runGen_tracking_map_snd.pairing {F G₁ G₂ Gₜ : Type} [CommSemiring F]
    [AddCommMonoid G₁] [AddCommMonoid G₂] [AddCommMonoid Gₜ]
    [Module F G₁] [Module F G₂] [Module F Gₜ]
    [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) {α : Type}
    (oa : OracleComp (genSpec F pairingSig) α)
    (tbl : Tbl (fun s => PFam (Repr F) (Repr F) (ReprT F) s × PFam G₁ G₂ Gₜ s)) :
    Prod.map id (mapTbl fun _ => Prod.snd) <$>
        runGen (tracking.pairing e) (fun _ => Prod.snd) oa tbl =
      runGen (pairingReal e) (fun _ => id) oa (mapTbl (fun _ => Prod.snd) tbl) := by
  have hsnd : (fun s => ⇑((Model.Hom.snd (free.pairing F) (pairingReal e)).toFun s)) =
      (fun _ => Prod.snd) := by
    funext s x
    exact Model.Hom.snd_apply _ _ _ _
  simpa only [hsnd, Function.comp_def, id_eq, tracking.pairing] using
    runGen_map (Model.Hom.snd (free.pairing F) (pairingReal e)) (fun _ => id) oa tbl

end GroupModel
