/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import VCVio.OracleComp.SimSemantics.Append
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.LinearAlgebra.BilinearMap

/-!
# Sorted prototype for the group-model design note

The sorted group model with linear and bilinear structure maps (pairings), for
`docs/design/group-models.md`, Section 6. Every proof in this file is complete. The file is not
part of any Lake library, so it uses plain imports.
-/

open OracleComp OracleSpec

namespace GroupModel.Sorted

/-- A handle is a position in the table of its sort. -/
abbrev Handle := ℕ

/-- A signature over sorts `S`: the names of the linear and bilinear structure maps and their
sorts. -/
structure Sig (S : Type) where
  Lin : Type
  lsrc : Lin → S
  ltgt : Lin → S
  Bil : Type
  src₁ : Bil → S
  src₂ : Bil → S
  tgt : Bil → S

/-- Queries: the module operations and equality in each sort, and each structure map. -/
inductive Query (F : Type) {S : Type} (σ : Sig S) : Type
  | add (s : S) (a b : Handle)
  | smul (s : S) (c : F) (a : Handle)
  | eq (s : S) (a b : Handle)
  | lin (o : σ.Lin) (a : Handle)
  | bil (o : σ.Bil) (a b : Handle)

def spec (F : Type) {S : Type} (σ : Sig S) : OracleSpec (Query F σ)
  | .add _ _ _ => Handle
  | .smul _ _ _ => Handle
  | .eq _ _ _ => Bool
  | .lin _ _ => Handle
  | .bil _ _ _ => Handle

/-- A model of a signature: a module per sort and a map per structure map. -/
structure Model (F : Type) [CommSemiring F] {S : Type} (σ : Sig S) (V : S → Type)
    [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)] where
  lin : (o : σ.Lin) → V (σ.lsrc o) →ₗ[F] V (σ.ltgt o)
  bil : (o : σ.Bil) → V (σ.src₁ o) →ₗ[F] V (σ.src₂ o) →ₗ[F] V (σ.tgt o)

/-- A morphism of models: a linear map per sort that commutes with the structure maps. -/
structure Model.Hom {F : Type} [CommSemiring F] {S : Type} {σ : Sig S} {V W : S → Type}
    [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)]
    [∀ s, AddCommMonoid (W s)] [∀ s, Module F (W s)]
    (M : Model F σ V) (N : Model F σ W) where
  toFun : (s : S) → V s →ₗ[F] W s
  map_lin : ∀ o x, toFun (σ.ltgt o) (M.lin o x) = N.lin o (toFun _ x)
  map_bil : ∀ o x y, toFun (σ.tgt o) (M.bil o x y) = N.bil o (toFun _ x) (toFun _ y)

section Handler

variable {F : Type} {S : Type} [DecidableEq S] {σ : Sig S} {V W U : S → Type}

/-- One table per sort. -/
abbrev Tbl (V : S → Type) := (s : S) → List (V s)

def lookup [∀ s, Zero (V s)] (tbl : Tbl V) (s : S) (h : Handle) : V s := (tbl s).getD h 0

def append (tbl : Tbl V) (s : S) (v : V s) : Tbl V := Function.update tbl s (tbl s ++ [v])

def mapTbl (φ : (s : S) → V s → W s) (tbl : Tbl V) : Tbl W := fun s => (tbl s).map (φ s)

/-- The one handler, sorted: entries of sort `s` live in `V s`, equality is decided on `obs s`. -/
def impl [CommSemiring F] [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)]
    [∀ s, DecidableEq (U s)] (M : Model F σ V) (obs : (s : S) → V s → U s)
    (m : Type → Type) [Monad m] : QueryImpl (spec F σ) (StateT (Tbl V) m)
  | .add s a b => modifyGet fun tbl =>
      ((tbl s).length, append tbl s (lookup tbl s a + lookup tbl s b))
  | .smul s c a => modifyGet fun tbl => ((tbl s).length, append tbl s (c • lookup tbl s a))
  | .eq s a b => do
      let tbl ← get
      pure (decide (obs s (lookup tbl s a) = obs s (lookup tbl s b)))
  | .lin o a => modifyGet fun tbl =>
      ((tbl (σ.ltgt o)).length, append tbl (σ.ltgt o) (M.lin o (lookup tbl (σ.lsrc o) a)))
  | .bil o a b => modifyGet fun tbl =>
      ((tbl (σ.tgt o)).length,
        append tbl (σ.tgt o) (M.bil o (lookup tbl (σ.src₁ o) a) (lookup tbl (σ.src₂ o) b)))

theorem mapTbl_append (φ : (s : S) → V s → W s) (tbl : Tbl V) (s : S) (v : V s) :
    mapTbl φ (append tbl s v) = append (mapTbl φ tbl) s (φ s v) := by
  funext t
  by_cases h : t = s
  · subst h
    simp [mapTbl, append]
  · simp [mapTbl, append, Function.update_of_ne h]

abbrev genSpec (F : Type) (σ : Sig S) := unifSpec + spec F σ

def run [CommSemiring F] [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)]
    [∀ s, DecidableEq (U s)] (M : Model F σ V) (obs : (s : S) → V s → U s) {α : Type}
    (oa : OracleComp (genSpec F σ) α) (tbl : Tbl V) : ProbComp (α × Tbl V) :=
  (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (Tbl V) ProbComp) +
    impl M obs ProbComp) oa).run tbl

end Handler

/-! ## Projection -/

section Projection

variable {F : Type} [CommSemiring F] {S : Type} [DecidableEq S] {σ : Sig S} {V W U : S → Type}
  [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)]
  [∀ s, AddCommMonoid (W s)] [∀ s, Module F (W s)]

omit [DecidableEq S] in
theorem lookup_mapTbl (φ : (s : S) → V s →ₗ[F] W s) (tbl : Tbl V) (s : S) (h : Handle) :
    lookup (mapTbl (fun s => φ s) tbl) s h = φ s (lookup tbl s h) := by
  simp only [lookup, mapTbl, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases (tbl s)[h]? <;> simp

/-- L1, sorted. Along a morphism of models the observed handler is the plain handler on the
image tables. -/
theorem run_map [∀ s, DecidableEq (U s)] {M : Model F σ V} {N : Model F σ W} (φ : M.Hom N)
    (obs : (s : S) → W s → U s) {α : Type} (oa : OracleComp (genSpec F σ) α) (tbl : Tbl V) :
    Prod.map id (mapTbl fun s => φ.toFun s) <$> run M (fun s => obs s ∘ φ.toFun s) oa tbl =
      run N obs oa (mapTbl (fun s => φ.toFun s) tbl) := by
  unfold run
  refine OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ (mapTbl fun s => φ.toFun s) ?_ oa tbl
  intro t s
  rcases t with n | (⟨s', a, b⟩ | ⟨s', c, a⟩ | ⟨s', a, b⟩ | ⟨o, a⟩ | ⟨o, a, b⟩)
  · simp
  · simp [impl, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, StateT.run, lookup_mapTbl,
      mapTbl_append, Prod.map]
    exact Prod.ext (by simp [mapTbl]; rfl) rfl
  · simp [impl, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, StateT.run, lookup_mapTbl,
      mapTbl_append, Prod.map]
    exact Prod.ext (by simp [mapTbl]; rfl) rfl
  · simp only [QueryImpl.add_apply_inr, impl, Function.comp_apply, StateT.run_bind,
      StateT.run_get, pure_bind, lookup_mapTbl]
    erw [StateT.run_pure, StateT.run_pure]
    simp
    rfl
  · simp [impl, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, StateT.run, lookup_mapTbl,
      mapTbl_append, Prod.map, φ.map_lin]
    exact Prod.ext (by simp [mapTbl]; rfl) rfl
  · simp [impl, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, StateT.run, lookup_mapTbl,
      mapTbl_append, Prod.map, φ.map_bil]
    exact Prod.ext (by simp [mapTbl]; rfl) rfl

/-- The handler depends on the observation only through the equalities it induces. Two
observations with the same equalities give the same handler, hence the same run. -/
theorem impl_congr {U' : S → Type} [∀ s, DecidableEq (U s)] [∀ s, DecidableEq (U' s)]
    (M : Model F σ V) (obs : (s : S) → V s → U s) (obs' : (s : S) → V s → U' s)
    (h : ∀ s x y, obs s x = obs s y ↔ obs' s x = obs' s y) (m : Type → Type) [Monad m] :
    impl M obs m = impl M obs' m := by
  funext t
  cases t with
  | eq s a b => simp [impl, h]
  | _ => rfl

/-- The kernel lemma. If two tables are the images of one table under morphisms that identify
the same pairs of elements, the two runs have the same output distribution. -/
theorem run_fst_eq_of_kernel_eq {K : S → Type} [∀ s, AddCommMonoid (K s)] [∀ s, Module F (K s)]
    [∀ s, DecidableEq (V s)] [∀ s, DecidableEq (W s)]
    {L : Model F σ K} {M : Model F σ V} {N : Model F σ W} (φ : L.Hom M) (ψ : L.Hom N)
    (h : ∀ s x y, φ.toFun s x = φ.toFun s y ↔ ψ.toFun s x = ψ.toFun s y)
    {α : Type} (oa : OracleComp (genSpec F σ) α) (tbl : Tbl K) :
    Prod.fst <$> run M (fun _ => id) oa (mapTbl (fun s => φ.toFun s) tbl) =
      Prod.fst <$> run N (fun _ => id) oa (mapTbl (fun s => ψ.toFun s) tbl) := by
  rw [← run_map φ (fun _ => id), ← run_map ψ (fun _ => id)]
  simp only [Functor.map_map]
  unfold run
  rw [impl_congr L (fun s => id ∘ φ.toFun s) (fun s => id ∘ ψ.toFun s) (by simpa using h)]
  rfl

end Projection

/-! ## Instances of the signature -/

/-- One group: one sort, no structure map. -/
def groupSig : Sig Unit :=
  ⟨Empty, Empty.elim, Empty.elim, Empty, Empty.elim, Empty.elim, Empty.elim⟩

/-- The sorts of a pairing group. -/
inductive PSort
  | g₁ | g₂ | gₜ
  deriving DecidableEq

/-- Asymmetric pairing without a map between the source groups (Type 3). -/
def pairingSig : Sig PSort :=
  ⟨Empty, Empty.elim, Empty.elim, Unit, fun _ => .g₁, fun _ => .g₂, fun _ => .gₜ⟩

/-- Asymmetric pairing with a map from the second source group to the first (Type 2). -/
def pairingIsoSig : Sig PSort :=
  ⟨Unit, fun _ => .g₂, fun _ => .g₁, Unit, fun _ => .g₁, fun _ => .g₂, fun _ => .gₜ⟩

/-- Symmetric pairing (Type 1): one source sort paired with itself. -/
def symmPairingSig : Sig Bool :=
  ⟨Empty, Empty.elim, Empty.elim, Unit, fun _ => false, fun _ => false, fun _ => true⟩

/-- The symbolic model of any signature: every sort is the polynomial ring, every linear
structure map is the identity and every bilinear one is multiplication. -/
noncomputable def symbolic (F : Type) [CommSemiring F] {S : Type} (σ : Sig S) (ι : Type) :
    Model F σ (fun _ => MvPolynomial ι F) where
  lin _ := LinearMap.id
  bil _ := LinearMap.mul F (MvPolynomial ι F)

/-- A family of types indexed by the pairing sorts. -/
def PFam (A₁ A₂ Aₜ : Type) : PSort → Type
  | .g₁ => A₁
  | .g₂ => A₂
  | .gₜ => Aₜ

instance {A₁ A₂ Aₜ : Type} [AddCommMonoid A₁] [AddCommMonoid A₂] [AddCommMonoid Aₜ] :
    ∀ s, AddCommMonoid (PFam A₁ A₂ Aₜ s)
  | .g₁ => inferInstanceAs (AddCommMonoid A₁)
  | .g₂ => inferInstanceAs (AddCommMonoid A₂)
  | .gₜ => inferInstanceAs (AddCommMonoid Aₜ)

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
def real (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) : Model F pairingSig (PFam G₁ G₂ Gₜ) where
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

/-- The pairing on tracked entries: the outer product of the representations, the pairing of
the elements. -/
def trackingPair (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) :
    (Repr F × G₁) →ₗ[F] (Repr F × G₂) →ₗ[F] (ReprT F × Gₜ) :=
  LinearMap.mk₂ F (fun x y => (outer F x.1 y.1, e x.2 y.2))
    (by intro a b c; simp)
    (by intro c a b; simp)
    (by intro a b c; simp)
    (by intro c a b; simp)

/-- The tracking model of a pairing group: each entry carries its representation; the pairing
of two entries carries the outer product of their representations. -/
def tracking (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) :
    Model F pairingSig (PFam (Repr F × G₁) (Repr F × G₂) (ReprT F × Gₜ)) where
  lin o := o.elim
  bil _ := trackingPair e

/-- Forgetting representations is a morphism from the tracking model to the real model. -/
def tracking.forget (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) : (tracking e).Hom (real e) where
  toFun
    | .g₁ => LinearMap.snd F (Repr F) G₁
    | .g₂ => LinearMap.snd F (Repr F) G₂
    | .gₜ => LinearMap.snd F (ReprT F) Gₜ
  map_lin o := o.elim
  map_bil _ _ _ := rfl

/-- The free model on given elements: representations only. -/
def free (F : Type) [CommSemiring F] : Model F pairingSig (PFam (Repr F) (Repr F) (ReprT F)) where
  lin o := o.elim
  bil _ := outer F

/-- Evaluate a source representation on a list of given elements. -/
def evRepr {G : Type} [AddCommMonoid G] [Module F G] (xs : List G) : Repr F →ₗ[F] G :=
  ∑ i ∈ Finset.range xs.length, (LinearMap.proj (R := F) (φ := fun _ : Handle => F) i).smulRight
    (xs.getD i 0)

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

theorem evReprT_apply (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (xs : List G₁) (ys : List G₂) (zs : List Gₜ)
    (r : ReprT F) :
    evReprT e xs ys zs r = evRepr zs r.1 +
      ∑ i ∈ Finset.range xs.length, ∑ j ∈ Finset.range ys.length,
        r.2 i j • e (xs.getD i 0) (ys.getD j 0) := by
  simp [evReprT, LinearMap.sum_apply]

theorem evReprT_outer (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (xs : List G₁) (ys : List G₂) (zs : List Gₜ)
    (r₁ r₂ : Repr F) :
    evReprT e xs ys zs (outer F r₁ r₂) = e (evRepr xs r₁) (evRepr ys r₂) := by
  simp only [evReprT_apply, evRepr_apply, outer, LinearMap.mk₂_apply, map_sum,
    LinearMap.sum_apply, mul_smul, Finset.smul_sum, map_smul, LinearMap.smul_apply,
    Pi.zero_apply, zero_smul, Finset.sum_const_zero, zero_add]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => smul_comm _ _ _

/-- Evaluation on the given elements is a morphism from the free model to the real model. -/
def evHom (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (xs : List G₁) (ys : List G₂) (zs : List Gₜ) :
    (free F).Hom (real e) where
  toFun
    | .g₁ => (evRepr xs : Repr F →ₗ[F] G₁)
    | .g₂ => (evRepr ys : Repr F →ₗ[F] G₂)
    | .gₜ => (evReprT e xs ys zs : ReprT F →ₗ[F] Gₜ)
  map_lin o := o.elim
  map_bil _ r₁ r₂ := by
    exact evReprT_outer e xs ys zs r₁ r₂

/-- A given element is the value of its own basis representation. -/
theorem evRepr_single {G : Type} [AddCommMonoid G] [Module F G] [DecidableEq Handle]
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

theorem evalAt_apply {ι G : Type} [AddCommGroup G] [Module F G] (g : G) (x : ι → F)
    (P : MvPolynomial ι F) : evalAt g x P = MvPolynomial.eval x P • g := by
  simp [evalAt, LinearMap.toSpanSingleton_apply, MvPolynomial.aeval_eq_eval]

/-- Evaluating at `x` and scaling the generators is a morphism from the symbolic model to the
real model: the hidden-real run on polynomials is the real run on their values. -/
noncomputable def evalHom {ι : Type} (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (x : ι → F) : (symbolic F pairingSig ι).Hom (real e) where
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

end GroupModel.Sorted

#print axioms GroupModel.Sorted.run_map
#print axioms GroupModel.Sorted.impl_congr
#print axioms GroupModel.Sorted.tracking.forget
#print axioms GroupModel.Sorted.evalHom
#print axioms GroupModel.Sorted.run_fst_eq_of_kernel_eq
#print axioms GroupModel.Sorted.evHom
#print axioms GroupModel.Sorted.evRepr_single
