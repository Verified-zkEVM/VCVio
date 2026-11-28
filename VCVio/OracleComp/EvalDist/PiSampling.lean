/-
Copyright (c) 2026 aryaethn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/
module

public import VCVio.OracleComp.Constructions.SampleableType
public import ToMathlib.Control.Monad.Fold

/-!
# Laws of a finite family of independent draws

`Fintype.mPi f` runs the computations `f i` of a finite family independently and collects their
results into a function. This file gives its laws in distribution for `ProbComp`.

* It is a congruence (`Fintype.mPi_evalDistEq`), and running a family of two-step computations has
  the law of running all first steps and then all second steps (`Fintype.mPi_bind_evalDistEq`).
* Drawing the family and then overwriting coordinate `a` with a fresh draw of `f a` has the law of
  the family (`Fintype.mPi_resample`).
* Reading the family at one index has the law of that index's computation
  (`Fintype.mPi_map_eval`). Reading it at an index, or along a list of distinct indices, together
  with a function of the family that ignores those indices, has the law of drawing them first and,
  independently, the function of the family (`Fintype.mPi_map_eval_prod`,
  `Fintype.mPi_map_list_prod`). Reading it
  along disjoint lists of distinct indices has the law of drawing every list independently
  (`Fintype.mPi_map_list`, `Fintype.mPi_map_lists`).
* Drawing a uniform index and running its computation has the law of drawing the whole family and
  then a uniform index (`Fintype.uniformSample_bind_evalDistEq_mPi`): a lazily sampled table and an
  eagerly sampled one agree.

The measures of `Fintype.mPi` are the product measures of `evalDist_mPi`; the laws here are stated
with `=ᵈ`, which compares laws in the discrete structure on the results and so is not a corollary of
`evalDist_mPi` when the payload is uncountable.
-/

public section

open OracleComp

/-- Running families of computations equal in distribution in sequence gives results equal in
distribution. It is proved by induction rather than through `evalDist_mOfFn`, whose product
structure on the results is not the discrete one that `=ᵈ` uses. -/
theorem Fin.mOfFn_evalDistEq {α : Type} :
    ∀ {n : ℕ} {f g : Fin n → ProbComp α}, (∀ i, f i =ᵈ g i) → Fin.mOfFn n f =ᵈ Fin.mOfFn n g
  | 0, _, _, _ => .rfl
  | n + 1, f, g, h => by
      simp only [Fin.mOfFn]
      exact (h 0).bind fun a => (Fin.mOfFn_evalDistEq fun i => h i.succ).bind fun _ => .rfl

/-- A finite family of computations equal in distribution, run independently, gives results equal
in distribution. -/
theorem Fintype.mPi_evalDistEq {α : Type} {ι : Type} [Fintype ι] {f g : ι → ProbComp α}
    (h : ∀ i, f i =ᵈ g i) : Fintype.mPi f =ᵈ Fintype.mPi g := by
  unfold Fintype.mPi
  exact EvalDistEq.map_congr _ (Fin.mOfFn_evalDistEq fun i => h _)

/-- Running a family of two-step computations in sequence has the law of running all the first
steps, then all the second steps. -/
theorem Fin.mOfFn_bind_evalDistEq {α β : Type} :
    ∀ {n : ℕ} (mx : Fin n → ProbComp α) (f : Fin n → α → ProbComp β),
      Fin.mOfFn n (fun i => mx i >>= f i) =ᵈ
        (Fin.mOfFn n mx >>= fun xs => Fin.mOfFn n fun i => f i (xs i))
  | 0, _, _ => by
      simp only [Fin.mOfFn, pure_bind]
      exact .rfl
  | n + 1, mx, f => by
      simp only [Fin.mOfFn, bind_assoc, pure_bind, Fin.cons_zero, Fin.cons_succ]
      refine EvalDistEq.bind_right _ fun x => ?_
      refine EvalDistEq.trans (EvalDistEq.bind_right _ fun a =>
        EvalDistEq.bind_left (Fin.mOfFn_bind_evalDistEq _ _) _) ?_
      simp only [bind_assoc]
      exact OracleComp.EvalDistEq.bind_bind_swap _ _ _

/-- Running a finite family of two-step computations independently has the law of running all the
first steps, then all the second steps. -/
theorem Fintype.mPi_bind_evalDistEq {α β : Type} {ι : Type} [Fintype ι] (mx : ι → ProbComp α)
    (f : ι → α → ProbComp β) :
    Fintype.mPi (fun i => mx i >>= f i) =ᵈ
      (Fintype.mPi mx >>= fun xs => Fintype.mPi fun i => f i (xs i)) := by
  unfold Fintype.mPi
  refine (EvalDistEq.map_congr _ (Fin.mOfFn_bind_evalDistEq _ _)).trans ?_
  simp only [map_bind, bind_map_left]
  refine EvalDistEq.bind_right (m := ProbComp) _ fun xs => ?_
  simp only [Equiv.arrowCongr_apply, Equiv.refl_apply, Function.comp_def, Equiv.symm_symm,
    Equiv.apply_symm_apply]
  exact EvalDistEq.refl _

/-- Drawing a sequence of independent computations and then overwriting coordinate `k` with a fresh
draw of `g k` has the law of the sequence. -/
theorem Fin.mOfFn_resample {α : Type} :
    ∀ {n : ℕ} (g : Fin n → ProbComp α) (k : Fin n),
      (do let v ← Fin.mOfFn n g; let x ← g k; pure (Function.update v k x)) =ᵈ Fin.mOfFn n g
  | 0, _, k => k.elim0
  | n + 1, g, k => by
      cases k using Fin.cases with
      | zero =>
          simp only [Fin.mOfFn, bind_assoc, pure_bind, Fin.update_cons_zero]
          refine (OracleComp.EvalDistEq.bind_const _ _).trans ?_
          exact OracleComp.EvalDistEq.bind_bind_swap _ _ _
      | succ k =>
          simp only [Fin.mOfFn, bind_assoc, pure_bind, ← Fin.cons_update]
          refine EvalDistEq.bind_right _ fun a => ?_
          have ih := EvalDistEq.map_congr (fun v : Fin n → α => (Fin.cons a v : Fin (n + 1) → α))
            (Fin.mOfFn_resample (fun i => g i.succ) k)
          simpa only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def] using ih

/-- Drawing a finite family of independent computations and then overwriting coordinate `a` with a
fresh draw of `f a` has the law of the family. -/
theorem Fintype.mPi_resample {α : Type} {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → ProbComp α) (a : ι) :
    (do let T ← Fintype.mPi f; let x ← f a; pure (Function.update T a x)) =ᵈ Fintype.mPi f := by
  unfold Fintype.mPi
  set e := Fintype.equivFin ι
  have hres := EvalDistEq.map_congr ⇑(e.symm.arrowCongr (Equiv.refl α))
    (Fin.mOfFn_resample (fun k => f (e.symm k)) (e a))
  refine EvalDistEq.trans ?_ hres
  simp only [map_bind, bind_map_left, map_pure, Equiv.symm_apply_apply]
  refine EvalDistEq.bind_right (m := ProbComp) _ fun v => ?_
  refine EvalDistEq.bind_right (m := ProbComp) _ fun x => ?_
  have hupd : Function.update ((e.symm.arrowCongr (Equiv.refl α)) v) a x =
      (e.symm.arrowCongr (Equiv.refl α)) (Function.update v (e a) x) := by
    funext i
    simp only [Equiv.arrowCongr_apply, Equiv.refl_apply, Function.comp_apply, Equiv.symm_symm]
    by_cases h : i = a
    · subst h
      simp
    · rw [Function.update_of_ne h, Function.update_of_ne (fun h' => h (e.injective h'))]
      simp [Equiv.arrowCongr_apply]
  rw [hupd]

/-- **Marginal at an index.** Reading a family of independent draws at an index `a`, together with a
function of the family that ignores `a`, has the law of drawing `f a` and, independently, the
function of the family. -/
theorem Fintype.mPi_map_eval_prod {α γ : Type} {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → ProbComp α) (a : ι) (G : (ι → α) → γ)
    (hG : ∀ T x, G (Function.update T a x) = G T) :
    ((fun T => (T a, G T)) <$> Fintype.mPi f) =ᵈ
      (do let x ← f a; let g ← G <$> Fintype.mPi f; pure (x, g)) := by
  have hres := EvalDistEq.map_congr (m := ProbComp) (fun T : ι → α => (T a, G T))
    (Fintype.mPi_resample f a)
  refine EvalDistEq.trans (m := ProbComp) (m' := ProbComp) (m'' := ProbComp) hres.symm ?_
  simp only [map_bind, map_pure, Function.update_self, hG]
  refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
  refine EvalDistEq.bind_right (m := ProbComp) _ fun x => ?_
  simp only [bind_map_left]
  exact EvalDistEq.refl _

/-- **Marginal along a list.** Reading a family of independent draws along a list of distinct
indices, together with a function of the family that ignores those indices, has the law of drawing
the listed indices in order and, independently, the function of the family. -/
theorem Fintype.mPi_map_list_prod {α γ : Type} {ι : Type} [Fintype ι]
    (f : ι → ProbComp α) (G : (ι → α) → γ) :
    ∀ (L : List ι), L.Nodup → (∀ T T' : ι → α, (∀ c, c ∉ L → T c = T' c) → G T = G T') →
      ((fun T => (L.map T, G T)) <$> Fintype.mPi f) =ᵈ
        (do let t ← L.mapM f; let g ← G <$> Fintype.mPi f; pure (t, g))
  | [], _, _ => by
      simp only [List.map_nil, List.mapM_nil, pure_bind, map_eq_bind_pure_comp, Function.comp_def,
        bind_assoc]
      exact EvalDistEq.refl _
  | a :: L, hL, hG => by
      classical
      have haL : a ∉ L := (List.nodup_cons.mp hL).1
      have hG' : ∀ T T' : ι → α, (∀ c, c ∉ L → T c = T' c) → G T = G T' := by
        intro T T' h
        refine hG T T' fun c hc => h c fun hc' => hc (List.mem_cons_of_mem a hc')
      have hGa : ∀ T x, G (Function.update T a x) = G T := by
        intro T x
        refine hG _ _ fun c hc => ?_
        rw [Function.update_of_ne (fun h => hc (by subst h; exact List.mem_cons_self))]
      have ih := Fintype.mPi_map_list_prod f G L (List.nodup_cons.mp hL).2 hG'
      -- resample coordinate `a` on the left
      refine (EvalDistEq.map_congr (fun T => ((a :: L).map T, G T))
        (Fintype.mPi_resample f a)).symm.trans ?_
      simp only [map_bind, map_pure, List.map_cons, Function.update_self, hGa]
      have hmap : ∀ (T : ι → α) x, L.map (Function.update T a x) = L.map T := fun T x =>
        List.map_congr_left fun c hc =>
          Function.update_of_ne (fun h => haL (by subst h; exact hc)) _ _
      simp only [hmap]
      refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
      simp only [List.mapM_cons, bind_assoc, pure_bind]
      refine EvalDistEq.bind_right (m := ProbComp) _ fun x => ?_
      have ih' := EvalDistEq.map_congr (fun p : List α × γ => (x :: p.1, p.2)) ih
      simp only [map_bind, map_pure, Functor.map_map] at ih'
      simpa only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def] using ih'

/-- Reading a family of independent draws along a list of distinct indices has the law of drawing
the listed indices in order. -/
theorem Fintype.mPi_map_list {α : Type} {ι : Type} [Fintype ι]
    (f : ι → ProbComp α) (L : List ι) (hL : L.Nodup) :
    ((fun T => L.map T) <$> Fintype.mPi f) =ᵈ L.mapM f := by
  have h := EvalDistEq.map_congr Prod.fst
    (Fintype.mPi_map_list_prod f (fun _ => ()) L hL fun _ _ _ => rfl)
  simp only [Functor.map_map, map_bind, map_pure] at h
  refine h.trans ?_
  simp only [bind_map_left]
  have hdrop := EvalDistEq.bind_right (m := ProbComp) (L.mapM f)
    (f := fun a => Fintype.mPi f >>= fun _ => pure a) (g := pure)
    fun a => OracleComp.EvalDistEq.bind_const _ _
  rwa [bind_pure] at hdrop

/-- **Marginal along disjoint lists.** Reading a family of independent draws along `n` lists of
distinct indices, no index in two lists, has the law of drawing every list in order,
independently. -/
private theorem Fin.mOfFn_map_lists {α : Type} {ι : Type} [Fintype ι]
    (f : ι → ProbComp α) :
    ∀ {n : ℕ} (L : Fin n → List ι), (∀ k, (L k).Nodup) →
      (∀ k k' c, c ∈ L k → c ∈ L k' → k = k') →
      ((fun T k => (L k).map T) <$> Fintype.mPi f) =ᵈ Fin.mOfFn n fun k => (L k).mapM f
  | 0, L, _, _ => by
      simp only [Fin.mOfFn]
      rw [map_eq_bind_pure_comp]
      have : (fun T : ι → α => fun k : Fin 0 => (L k).map T) = fun _ => finZeroElim :=
        funext fun _ => funext fun k => k.elim0
      rw [this]
      exact OracleComp.EvalDistEq.bind_const _ _
  | n + 1, L, hnd, hdisj => by
      have hsplit : (fun T : ι → α => fun k : Fin (n + 1) => (L k).map T) =
          fun T => Fin.cons ((L 0).map T) fun k : Fin n => (L k.succ).map T := by
        funext T k
        refine Fin.cases rfl (fun k => rfl) k
      rw [hsplit]
      have hG : ∀ T T' : ι → α, (∀ c, c ∉ L 0 → T c = T' c) →
          (fun k : Fin n => (L k.succ).map T) = fun k => (L k.succ).map T' := by
        intro T T' h
        funext k
        refine List.map_congr_left fun c hc => h c fun hc0 => ?_
        exact Fin.succ_ne_zero k (hdisj _ _ c hc hc0)
      have hprod := EvalDistEq.map_congr
        (fun p : List α × (Fin n → List α) => (Fin.cons p.1 p.2 : Fin (n + 1) → List α))
        (Fintype.mPi_map_list_prod f (fun T k => (L k.succ).map T) (L 0) (hnd 0) hG)
      simp only [Functor.map_map] at hprod
      refine hprod.trans ?_
      have ih := Fin.mOfFn_map_lists f (fun k : Fin n => L k.succ) (fun k => hnd k.succ)
        fun k k' c hc hc' => Fin.succ_injective _ (hdisj _ _ c hc hc')
      simp only [Fin.mOfFn, map_bind, map_pure]
      refine EvalDistEq.bind_right (m := ProbComp) _ fun t => ?_
      rw [bind_map_left]
      have ih' := EvalDistEq.bind_left (m := ProbComp) ih
        (fun rest => (pure (Fin.cons t rest : Fin (n + 1) → List α) : ProbComp _))
      simpa only [bind_map_left] using ih'

/-- **Marginal along disjoint lists**, over a finite index type. -/
theorem Fintype.mPi_map_lists {α : Type} {ι : Type} [Fintype ι] {κ : Type}
    [Fintype κ] (f : ι → ProbComp α) (L : κ → List ι) (hnd : ∀ j, (L j).Nodup)
    (hdisj : ∀ j j' c, c ∈ L j → c ∈ L j' → j = j') :
    ((fun T j => (L j).map T) <$> Fintype.mPi f) =ᵈ Fintype.mPi fun j => (L j).mapM f := by
  set e := Fintype.equivFin κ
  have h := EvalDistEq.map_congr ⇑(e.symm.arrowCongr (Equiv.refl (List α)))
    (Fin.mOfFn_map_lists f (fun k => L (e.symm k)) (fun k => hnd _)
      fun k k' c hc hc' => e.symm.injective (hdisj _ _ c hc hc'))
  simp only [Functor.map_map] at h
  unfold Fintype.mPi at h ⊢
  refine EvalDistEq.trans ?_ h
  have hfun : (fun T : ι → α => fun j : κ => (L j).map T) =
      fun T => (e.symm.arrowCongr (Equiv.refl (List α))) fun k => (L (e.symm k)).map T := by
    funext T j
    simp [Equiv.arrowCongr_apply]
  rw [hfun]

/-- **Marginal at a centre and along disjoint lists.** Reading a family of independent draws at an
index `c₀` and along lists of distinct indices, no index in two lists and `c₀` in none, has the law
of drawing `f c₀` and, independently, every list. -/
theorem Fintype.mPi_map_eval_lists {α : Type} {ι : Type} [Fintype ι] {κ : Type}
    [Fintype κ] (f : ι → ProbComp α) (c₀ : ι) (L : κ → List ι) (hnd : ∀ j, (L j).Nodup)
    (hdisj : ∀ j j' c, c ∈ L j → c ∈ L j' → j = j') (hc₀ : ∀ j, c₀ ∉ L j) :
    ((fun T => (T c₀, fun j => (L j).map T)) <$> Fintype.mPi f) =ᵈ
      (do
        let x ← f c₀
        let ts ← Fintype.mPi fun j => (L j).mapM f
        pure (x, ts)) := by
  classical
  have hG : ∀ (T : ι → α) x, (fun j => (L j).map (Function.update T c₀ x)) =
      fun j => (L j).map T := fun T x => funext fun j =>
    List.map_congr_left fun c hc =>
      Function.update_of_ne (fun h => hc₀ j (by subst h; exact hc)) _ _
  refine (Fintype.mPi_map_eval_prod f c₀ _ hG).trans
    (EvalDistEq.bind_right (m := ProbComp) _ fun x => ?_)
  have h := EvalDistEq.bind_left (m := ProbComp) (Fintype.mPi_map_lists f L hnd hdisj)
    (fun t => (pure (x, t) : ProbComp _))
  simpa only [bind_map_left] using h

/-- Reading one coordinate of a family of independent draws has the law of that coordinate's
computation. -/
theorem Fintype.mPi_map_eval {α : Type} {ι : Type} [Fintype ι]
    (f : ι → ProbComp α) (a : ι) : ((fun T => T a) <$> Fintype.mPi f) =ᵈ f a := by
  classical
  have h := EvalDistEq.map_congr (m := ProbComp) Prod.fst
    (Fintype.mPi_map_eval_prod f a (fun _ => ()) fun _ _ => rfl)
  simp only [Functor.map_map, map_bind, map_pure] at h
  have hdrop := EvalDistEq.bind_right (m := ProbComp) (f a)
    (f := fun x => (fun _ => ()) <$> Fintype.mPi f >>= fun _ => pure x) (g := pure)
    fun x => OracleComp.EvalDistEq.bind_const _ _
  rw [bind_pure] at hdrop
  exact h.trans hdrop

/-- **A lazy table is an eager one.** Drawing a uniform index and running its computation has the
law of drawing the whole family of independent computations and then reading it at a uniform
index. -/
theorem Fintype.uniformSample_bind_evalDistEq_mPi {α : Type} {ι : Type} [Fintype ι]
    [SampleableType ι] (f : ι → ProbComp α) :
    (do let c ← $ᵗ ι; f c) =ᵈ (do let T ← Fintype.mPi f; let c ← $ᵗ ι; pure (T c)) := by
  classical
  refine (EvalDistEq.bind_right (m := ProbComp) _ fun c => ?_).trans
    (OracleComp.EvalDistEq.bind_bind_swap _ _ _)
  simpa only [map_eq_bind_pure_comp, Function.comp_def] using (Fintype.mPi_map_eval f c).symm
