/-
Copyright (c) 2026 Quang Dao, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Alexander Hicks
-/

module
public import VCVio.Schemes.PointerChainPuzzle.QuantumCoupling
import VCVio.Schemes.PointerChainPuzzle.LeanSealDelay

/-!
# Fresh-challenge incidence for preprocessing

Before the challenge is drawn, a fixed raw oracle input hits its programmed path with probability
at most `|Salt|⁻¹ * (|L|⁻¹ + solvePoints / |S|)`. Start, step, mask, key and commitment inputs
retain the fresh salt directly or through the injective context. The first accumulator input
contains that context and one fresh state. Later accumulator inputs carry no salt; their two
independent fresh predecessor states instead give `|S|⁻² ≤ (|Salt| * |S|)⁻¹`.

The bounds average unconditionally over full raw path responses and all fresh challenge coins.
Applying them to preprocessing query weights requires a reference state independent of those
coins. No event is conditioned on distinct path inputs.
-/

public section
open OracleSpec OracleComp Quantum MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace PointerChainPuzzle.LeanSeal
variable {b n m B : ℕ}

/-- Incidence of the fresh programmed path against a preprocessing query. -/
@[expose]
noncomputable def preprocessingIncidence (b n m : ℕ) : ℝ≥0∞ :=
  (Fintype.card (Bytes 16) : ℝ≥0∞)⁻¹ *
    ((Fintype.card (Bytes b) : ℝ≥0∞)⁻¹ + solvePoints n m / Fintype.card (Bytes 32))

/-- The fresh-challenge preprocessing incidence is finite. -/
theorem preprocessingIncidence_ne_top (b n m : ℕ) :
    preprocessingIncidence b n m ≠ ⊤ := by
  unfold preprocessingIncidence
  finiteness

/-- Real form of the fresh-challenge preprocessing incidence. -/
@[expose]
noncomputable def preprocessingIncidenceReal (b n m : ℕ) : ℝ :=
  (preprocessingIncidence b n m).toReal

/-- The real incidence coefficient is nonnegative. -/
theorem preprocessingIncidenceReal_nonneg (b n m : ℕ) :
    0 ≤ preprocessingIncidenceReal b n m := ENNReal.toReal_nonneg

/-- The real incidence coefficient has the same explicit cardinality formula. -/
theorem preprocessingIncidenceReal_eq (b n m : ℕ) :
    preprocessingIncidenceReal b n m =
      (Fintype.card (Bytes 16) : ℝ)⁻¹ *
        ((Fintype.card (Bytes b) : ℝ)⁻¹ + solvePoints n m / Fintype.card (Bytes 32)) := by
  unfold preprocessingIncidenceReal preprocessingIncidence
  rw [ENNReal.toReal_mul, ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_div]

/-- Converting the real incidence coefficient to an extended nonnegative real is exact. -/
theorem ofReal_preprocessingIncidenceReal (b n m : ℕ) :
    ENNReal.ofReal (preprocessingIncidenceReal b n m) = preprocessingIncidence b n m :=
  ENNReal.ofReal_toReal (preprocessingIncidence_ne_top b n m)

private theorem labels_pair_le (a c : PathValue n m) (hac : a ≠ c)
    (u : a.Val (Bytes 32) (Bytes b)) (v : c.Val (Bytes 32) (Bytes b)) :
    Pr{let ℓ ← $ᵗ Labels n m (Bytes 32) (Bytes b)}[ℓ a = u ∧ ℓ c = v] ≤
      (Fintype.card (a.Val (Bytes 32) (Bytes b)) : ℝ≥0∞)⁻¹ *
        (Fintype.card (c.Val (Bytes 32) (Bytes b)) : ℝ≥0∞)⁻¹ := by
  let : ∀ w : PathValue n m, MeasurableSpace (w.Val (Bytes 32) (Bytes b)) := fun _ ↦ ⊤
  let f : Labels n m (Bytes 32) (Bytes b) → ProbComp Prop :=
    fun ℓ ↦ pure (ℓ a = u ∧ ℓ c = v)
  have h₁ := evalDist_bind_bind_update_dependent c ($ᵗ (c.Val (Bytes 32) (Bytes b)))
    ($ᵗ Labels n m (Bytes 32) (Bytes b)) SampleableType.evalDist_uniformSample
    SampleableType.evalDist_uniformSample f
  rw [map_eq_bind_pure_comp]
  change prEvent ($ᵗ Labels n m (Bytes 32) (Bytes b) >>= f) ≤ _
  rw [prEvent_def, ← h₁, ← prEvent_def, prEvent_bind_bind_swap]
  refine prEvent_uniform_bind_le_of_update a _ fun ℓ ↦ ?_
  simp only [f, Function.update_self, Function.update_of_ne hac]
  have hh := prEvent_bind_bind_and ($ᵗ (a.Val (Bytes 32) (Bytes b)))
    ($ᵗ (c.Val (Bytes 32) (Bytes b))) (fun x ↦ x = u) (fun y ↦ y = v)
  rw [SampleableType.prEvent_uniformSample_eq_singleton,
    SampleableType.prEvent_uniformSample_eq_singleton] at hh
  simpa only [bind_pure_comp] using hh.le

private theorem prEvent_pathLabels_eq (hb : b ≤ 32)
    (E : Labels n m (Bytes 32) (Bytes b) → Prop) :
    Pr{let W ← $ᵗ (PathValue n m → Bytes 32)}[E (pathLabels hb W)] =
      Pr{let ℓ ← $ᵗ Labels n m (Bytes 32) (Bytes b)}[E ℓ] := by
  let : MeasurableSpace (PathValue n m → Bytes 32) := ⊤
  let : MeasurableSpace (Labels n m (Bytes 32) (Bytes b)) := ⊤
  have he := congrArg (fun μ : Measure (Labels n m (Bytes 32) (Bytes b)) ↦ μ {ℓ | E ℓ})
    (uniformOn_univ_map_pathLabels (n := n) (m := m) hb)
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete] at he
  simpa only [prEvent_eq_evalDist_of_discrete, SampleableType.evalDist_uniformSample,
    Set.preimage_ofPred_eq] using he

variable [NeZero n]

private theorem seed_bound_of_guard (t : TypedPoint b n) (guard : Bytes 16 → Prop)
    (hg : Pr{let salt ← $ᵗ Bytes 16}[guard salt] ≤
      (Fintype.card (Bytes 16) : ℝ≥0∞)⁻¹)
    (ht : ∀ ctx i x, t ≠ .start ctx i x)
    (hguard : ∀ (salt : Bytes 16) (p : Bytes b × (Fin (n - 1) → Bytes b))
      (ℓ : Labels n m (Bytes 32) (Bytes b)) v,
      t = pathInput m (ctx b n m) id (labelPuzzle salt p.1 p.2 ℓ) ℓ v → guard salt) :
    Pr{let salt ← $ᵗ Bytes 16; let p ← $ᵗ (Bytes b × (Fin (n - 1) → Bytes b));
        let ℓ ← $ᵗ Labels n m (Bytes 32) (Bytes b)}[
      ∃ v, t = pathInput m (ctx b n m) id (labelPuzzle salt p.1 p.2 ℓ) ℓ v] ≤
      (Fintype.card (Bytes 16) : ℝ≥0∞)⁻¹ *
        (solvePoints n m / Fintype.card (Bytes 32)) := by
  refine (prEvent_bind_le_mul guard (ε := solvePoints n m / Fintype.card (Bytes 32)) ?_ ?_).trans ?_
  · intro salt _
    refine prEvent_bind_le fun p ↦ prEvent_labelPuzzle_le salt p.1 p.2
      (fun P ℓ ↦ ∃ v, t = pathInput m (ctx b n m) id P ℓ v) fun ℓ₀ ↦ ?_
    exact (prEvent_mono _ _ _ fun ℓ' ⟨v, hv⟩ ↦
      hitAt_empty_of_eq hv (fun ctx x ↦ ht ctx _ x)).trans
        (prEvent_hitAt_le_of_ne_start _ ∅ ℓ₀ ht)
  · intro salt hng
    exact le_antisymm (prEvent_bind_le fun p ↦ le_of_eq
      (prEvent_eq_zero_of_forall_not _ _ fun ℓ ⟨v, hv⟩ ↦
        hng (hguard salt p ℓ v hv))) zero_le
  · gcongr

private theorem seed_start_le (c : Bytes 32) (i : Fin n) (x : Bytes b) :
    Pr{let salt ← $ᵗ Bytes 16; let p ← $ᵗ (Bytes b × (Fin (n - 1) → Bytes b));
        let ℓ ← $ᵗ Labels n m (Bytes 32) (Bytes b)}[
      ∃ v, Point.start c i x =
        pathInput m (ctx b n m) id (labelPuzzle salt p.1 p.2 ℓ) ℓ v] ≤
      (Fintype.card (Bytes 16) * Fintype.card (Bytes b) : ℝ≥0∞)⁻¹ := by
  have h₁ : ∀ salt, ctx b n m salt = c →
      Pr{let p ← $ᵗ (Bytes b × (Fin (n - 1) → Bytes b));
          let ℓ ← $ᵗ Labels n m (Bytes 32) (Bytes b)}[
        ∃ v, Point.start c i x = pathInput m (ctx b n m) id (labelPuzzle salt p.1 p.2 ℓ) ℓ v] ≤
        (Fintype.card (Bytes b) : ℝ≥0∞)⁻¹ := by
    intro salt hsalt
    obtain ⟨_ | j, hi⟩ := i
    · have h₀ : ∀ p : (Bytes b) × (Fin (n - 1) → (Bytes b)), ¬p.1 = x →
          Pr{let ℓ ← $ᵗ Labels n m (Bytes 32) (Bytes b)}[∃ v, Point.start c ⟨0, hi⟩ x =
            pathInput m (ctx b n m) id (labelPuzzle salt p.1 p.2 ℓ) ℓ v] = 0 := by
        intro p hp
        refine prEvent_eq_zero_of_forall_not _ _ fun ℓ ⟨v, hv⟩ => hp ?_
        obtain rfl := eq_of_pathInput_eq_start hv.symm
        simp only [pathInput, labelPuzzle, Point.start.injEq] at hv
        exact hv.2.2.symm
      refine (prEvent_bind_le_mul (fun p => p.1 = x) (ε := 1) (fun _ _ => prEvent_le_one _)
        h₀).trans ?_
      have hfst := SampleableType.evalDist_uniformSample_prod_bind_fst
        (β := Fin (n - 1) → Bytes b)
        (fun a : (Bytes b) => (pure (a = x) : ProbComp Prop))
      calc Pr{let p ← $ᵗ (Bytes b × (Fin (n - 1) → Bytes b))}[p.1 = x] * 1 =
            Pr{let a ← $ᵗ Bytes b}[a = x] := by
            rw [mul_one, prEvent_def, prEvent_def, map_eq_bind_pure_comp, map_eq_bind_pure_comp]
            exact congrArg (· {True}) hfst
        _ ≤ _ := (SampleableType.prEvent_uniformSample_eq_singleton x).le
    · refine prEvent_bind_le fun p => prEvent_labelPuzzle_le salt p.1 p.2
        (fun P ℓ => ∃ v, Point.start c ⟨j + 1, hi⟩ x = pathInput m (ctx b n m) id P ℓ v)
        fun ℓ₀ => ?_
      have hne : ∀ c' x', (Point.start c ⟨j + 1, hi⟩ x : TypedPoint b n) ≠
          .start c' ⟨0, Nat.pos_of_neZero n⟩ x' := by
        intro c' x' h
        simp only [Point.start.injEq, Fin.mk.injEq] at h
        omega
      refine (prEvent_mono _ _ _ fun ℓ' ⟨v, hv⟩ => hitAt_empty_of_eq hv hne).trans
        ((prEvent_hitAt_start_le _ ∅ ℓ₀ c ⟨j + 1, hi⟩ x).trans ?_)
      split_ifs <;> simp
  have h₂ : ∀ salt, ¬ctx b n m salt = c →
      Pr{let p ← $ᵗ (Bytes b × (Fin (n - 1) → Bytes b));
          let ℓ ← $ᵗ Labels n m (Bytes 32) (Bytes b)}[
        ∃ v, Point.start c i x = pathInput m (ctx b n m) id (labelPuzzle salt p.1 p.2 ℓ) ℓ v] =
        0 := by
    intro salt hsalt
    refine le_antisymm (prEvent_bind_le fun p => le_of_eq
      (prEvent_eq_zero_of_forall_not _ _ fun ℓ ⟨v, hv⟩ => hsalt ?_)) zero_le
    obtain rfl := eq_of_pathInput_eq_start hv.symm
    obtain ⟨_ | j, hj⟩ := i <;>
      simp only [Fin.mk_zero', pathInput, labelPuzzle, Point.start.injEq, true_and] at hv <;>
      exact hv.1.symm
  refine (prEvent_bind_le_mul (fun salt => ctx b n m salt = c) h₁ h₂).trans ?_
  have hsalt : Pr{let salt ← $ᵗ Bytes 16}[ctx b n m salt = c] ≤
      (Fintype.card (Bytes 16) : ℝ≥0∞)⁻¹ := by
    rw [← Nat.card_eq_fintype_card]
    exact SampleableType.prEvent_uniformSample_apply_eq_le (ctx_injective b n m) c
  rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
  gcongr

private theorem seed_acc_node_le (a y : Bytes 32) (v : PathValue n m) :
    Pr{let salt ← $ᵗ Bytes 16; let p ← $ᵗ (Bytes b × (Fin (n - 1) → Bytes b));
        let ℓ ← $ᵗ Labels n m (Bytes 32) (Bytes b)}[
      Point.acc a y = pathInput m (ctx b n m) id (labelPuzzle salt p.1 p.2 ℓ) ℓ v] ≤
      (Fintype.card (Bytes 16) : ℝ≥0∞)⁻¹ * (Fintype.card (Bytes 32) : ℝ≥0∞)⁻¹ := by
  have hone (w : PathValue n m) (u : w.Val (Bytes 32) (Bytes b)) :
      Pr{let ℓ ← $ᵗ Labels n m (Bytes 32) (Bytes b)}[ℓ w = u] ≤
        (Fintype.card (w.Val (Bytes 32) (Bytes b)) : ℝ≥0∞)⁻¹ := by
    refine prEvent_uniform_le_of_update w _ fun ℓ ↦ ?_
    simpa only [Function.update_self] using
      (SampleableType.prEvent_uniformSample_eq_singleton u).le
  have hinv : (Fintype.card (Bytes 32) : ℝ≥0∞)⁻¹ ≤
      (Fintype.card (Bytes 16) : ℝ≥0∞)⁻¹ := by
    gcongr
    norm_num [card_bytes]
  rcases v with ⟨⟨_ | i, hi⟩, ⟨_ | k, hk⟩⟩ | i | ⟨_ | i, hi⟩ | _ | _
  all_goals try solve
    | refine prEvent_bind_le fun salt ↦ prEvent_bind_le fun p ↦ ?_
      refine le_of_eq_of_le (prEvent_eq_zero_of_forall_not _ _ fun ℓ h ↦ ?_) zero_le
      simp only [pathInput, labelPuzzle, reduceCtorEq] at h
  · refine (prEvent_bind_le_mul (fun salt ↦ ctx b n m salt = a)
      (ε := (Fintype.card (Bytes 32) : ℝ≥0∞)⁻¹) ?_ ?_).trans ?_
    · intro salt _
      refine prEvent_bind_le fun p ↦ ?_
      refine (prEvent_mono _ _ _ fun ℓ h ↦ ?_).trans
        (hone (.state ⟨0, hi⟩ (Fin.last m)) y)
      exact (Point.acc.inj h).2.symm
    · intro salt hs
      exact le_antisymm (prEvent_bind_le fun p ↦ le_of_eq
        (prEvent_eq_zero_of_forall_not _ _ fun ℓ h ↦ hs (Point.acc.inj h).1.symm)) zero_le
    · apply mul_le_mul_left
      rw [← Nat.card_eq_fintype_card]
      exact SampleableType.prEvent_uniformSample_apply_eq_le (ctx_injective b n m) a
  · refine prEvent_bind_le fun salt ↦ prEvent_bind_le fun p ↦ ?_
    refine (prEvent_mono _ _ _ fun ℓ h ↦ ?_).trans
      ((labels_pair_le (.acc ⟨i, by omega⟩) (.state ⟨i + 1, hi⟩ (Fin.last m))
        (by simp) a y).trans ?_)
    · exact ⟨(Point.acc.inj h).1.symm, (Point.acc.inj h).2.symm⟩
    · exact mul_le_mul_left hinv _

private theorem seed_acc_le (a y : Bytes 32) :
    Pr{let salt ← $ᵗ Bytes 16; let p ← $ᵗ (Bytes b × (Fin (n - 1) → Bytes b));
        let ℓ ← $ᵗ Labels n m (Bytes 32) (Bytes b)}[
      ∃ v, Point.acc a y = pathInput m (ctx b n m) id (labelPuzzle salt p.1 p.2 ℓ) ℓ v] ≤
      (Fintype.card (Bytes 16) : ℝ≥0∞)⁻¹ *
        (solvePoints n m / Fintype.card (Bytes 32)) := by
  let draw : ProbComp (Bytes 16 × (Bytes b × (Fin (n - 1) → Bytes b)) ×
      Labels n m (Bytes 32) (Bytes b)) := do
    let salt ← $ᵗ Bytes 16
    let p ← $ᵗ (Bytes b × (Fin (n - 1) → Bytes b))
    let ℓ ← $ᵗ Labels n m (Bytes 32) (Bytes b)
    pure (salt, p, ℓ)
  have hh := prEvent_exists_le_card_mul draw
    (fun v q ↦ Point.acc a y =
      pathInput m (ctx b n m) id (labelPuzzle q.1 q.2.1.1 q.2.1.2 q.2.2) q.2.2 v)
    (ε := (Fintype.card (Bytes 16) : ℝ≥0∞)⁻¹ *
      (Fintype.card (Bytes 32) : ℝ≥0∞)⁻¹)
    (fun v ↦ by simpa only [draw, prEvent_norm] using seed_acc_node_le (b := b) a y v)
  simp only [draw, prEvent_norm, PathValue.card_eq] at hh
  simpa only [div_eq_mul_inv, mul_left_comm] using hh

/-- A fixed typed oracle point hits a freshly sampled path with probability at most the fresh
salt factor times the sum of the link and state incidence bounds. Later accumulator inputs use
two independent state labels because their byte encoding carries no salt field. -/
theorem prEvent_eq_pathInput_seed_le_salted (t : TypedPoint b n) :
    Pr{let salt ← $ᵗ Bytes 16; let p ← $ᵗ (Bytes b × (Fin (n - 1) → Bytes b));
        let ℓ ← $ᵗ Labels n m (Bytes 32) (Bytes b)}[
      ∃ v, t = pathInput m (ctx b n m) id (labelPuzzle salt p.1 p.2 ℓ) ℓ v] ≤
      (Fintype.card (Bytes 16) : ℝ≥0∞)⁻¹ *
        ((Fintype.card (Bytes b) : ℝ≥0∞)⁻¹ +
          solvePoints n m / Fintype.card (Bytes 32)) := by
  have hgctx (c : Bytes 32) :
      Pr{let salt ← $ᵗ Bytes 16}[ctx b n m salt = c] ≤
        (Fintype.card (Bytes 16) : ℝ≥0∞)⁻¹ := by
    rw [← Nat.card_eq_fintype_card]
    exact SampleableType.prEvent_uniformSample_apply_eq_le (ctx_injective b n m) c
  have hd : (Fintype.card (Bytes 16) : ℝ≥0∞)⁻¹ *
        (solvePoints n m / Fintype.card (Bytes 32)) ≤
      (Fintype.card (Bytes 16) : ℝ≥0∞)⁻¹ *
        ((Fintype.card (Bytes b) : ℝ≥0∞)⁻¹ +
          solvePoints n m / Fintype.card (Bytes 32)) := by
    rw [mul_add]
    exact le_add_left le_rfl
  cases t with
  | start c i x =>
    have hs := seed_start_le (m := m) c i x
    rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
      (Or.inl (ENNReal.natCast_ne_top _))] at hs
    exact hs.trans (by rw [mul_add]; exact le_add_right le_rfl)
  | acc a y => exact (seed_acc_le (b := b) a y).trans hd
  | step s i a =>
    refine (seed_bound_of_guard (m := m) (.step s i a) (fun salt ↦ salt = s)
      (SampleableType.prEvent_uniformSample_eq_singleton s).le
      (by simp) ?_).trans hd
    intro salt p ℓ v he
    rcases v with ⟨⟨_ | j, hj⟩, ⟨_ | k, hk⟩⟩ | j | ⟨_ | j, hj⟩ | _ | _ <;>
      simp_all [pathInput, labelPuzzle]
  | mask c a =>
    refine (seed_bound_of_guard (m := m) (.mask c a) (fun salt ↦ ctx b n m salt = c)
      (hgctx c) (by simp) ?_).trans hd
    intro salt p ℓ v he
    rcases v with ⟨⟨_ | j, hj⟩, ⟨_ | k, hk⟩⟩ | j | ⟨_ | j, hj⟩ | _ | _ <;>
      simp_all [pathInput, labelPuzzle]
  | key c a =>
    refine (seed_bound_of_guard (m := m) (.key c a) (fun salt ↦ ctx b n m salt = c)
      (hgctx c) (by simp) ?_).trans hd
    intro salt p ℓ v he
    rcases v with ⟨⟨_ | j, hj⟩, ⟨_ | k, hk⟩⟩ | j | ⟨_ | j, hj⟩ | _ | _ <;>
      simp_all [pathInput, labelPuzzle]
  | commit c a =>
    refine (seed_bound_of_guard (m := m) (.commit c a) (fun salt ↦ ctx b n m salt = c)
      (hgctx c) (by simp) ?_).trans hd
    intro salt p ℓ v he
    rcases v with ⟨⟨_ | j, hj⟩, ⟨_ | k, hk⟩⟩ | j | ⟨_ | j, hj⟩ | _ | _ <;>
      simp_all [pathInput, labelPuzzle]

/-- A fixed raw byte string hits the path programmed after preprocessing with probability at
most the salt factor times link/state incidence. Full raw path responses are sampled uniformly
without conditioning on distinct inputs. -/
theorem prEvent_eq_rawPathInput_seed_le (hb : b ≤ 32) (hn : n < 2 ^ 32)
    (hB : hashInputBound b ≤ B) (t : ByteArray.Bounded B) :
    Pr{let salt ← $ᵗ Bytes 16; let p ← $ᵗ (Bytes b × (Fin (n - 1) → Bytes b));
        let W ← $ᵗ (PathValue n m → Bytes 32)}[
      ∃ v, t = rawPathInput hb hB salt p.1 p.2 v W] ≤
      (Fintype.card (Bytes 16) : ℝ≥0∞)⁻¹ *
        ((Fintype.card (Bytes b) : ℝ≥0∞)⁻¹ +
          solvePoints n m / Fintype.card (Bytes 32)) := by
  classical
  by_cases ht : ∃ u : TypedPoint b n, hashInputWindow hB u = t
  · obtain ⟨u, rfl⟩ := ht
    have he (salt : Bytes 16) (p : Bytes b × (Fin (n - 1) → Bytes b)) :
        Pr{let W ← $ᵗ (PathValue n m → Bytes 32)}[
          ∃ v, hashInputWindow hB u = rawPathInput hb hB salt p.1 p.2 v W] =
        Pr{let ℓ ← $ᵗ Labels n m (Bytes 32) (Bytes b)}[
          ∃ v, u = pathInput m (ctx b n m) id (labelPuzzle salt p.1 p.2 ℓ) ℓ v] := by
      simpa only [rawPathInput, pathWindowInput, (hashInputWindow_injective hB hn).eq_iff]
        using prEvent_pathLabels_eq hb (fun ℓ ↦
          ∃ v, u = pathInput m (ctx b n m) id (labelPuzzle salt p.1 p.2 ℓ) ℓ v)
    let : MeasurableSpace (Bytes 16) := ⊤
    let : MeasurableSpace (Bytes b × (Fin (n - 1) → Bytes b)) := ⊤
    let : MeasurableSpace (PathValue n m → Bytes 32) := ⊤
    let : MeasurableSpace (Labels n m (Bytes 32) (Bytes b)) := ⊤
    have hs :
        Pr{let salt ← $ᵗ Bytes 16; let p ← $ᵗ (Bytes b × (Fin (n - 1) → Bytes b));
            let W ← $ᵗ (PathValue n m → Bytes 32)}[
          ∃ v, hashInputWindow hB u = rawPathInput hb hB salt p.1 p.2 v W] =
        Pr{let salt ← $ᵗ Bytes 16; let p ← $ᵗ (Bytes b × (Fin (n - 1) → Bytes b));
            let ℓ ← $ᵗ Labels n m (Bytes 32) (Bytes b)}[
          ∃ v, u = pathInput m (ctx b n m) id (labelPuzzle salt p.1 p.2 ℓ) ℓ v] := by
      simp_rw [prEvent_bind_of_discrete] at he ⊢
      apply lintegral_congr
      intro salt
      apply lintegral_congr
      intro p
      exact he salt p
    exact hs.le.trans (prEvent_eq_pathInput_seed_le_salted u)
  · apply le_trans (b := 0)
    · refine prEvent_bind_le fun salt ↦ prEvent_bind_le fun p ↦ ?_
      exact le_of_eq (prEvent_eq_zero_of_forall_not _ _ fun W ⟨v, hv⟩ ↦ ht ⟨_, hv.symm⟩)
    · exact zero_le

/-- Uniform real query weights have the same fresh-challenge incidence bound. The oracle input
is fixed before the salt, first and masked links, and complete raw path responses are drawn. -/
theorem sum_indicator_rawPathInputs_seed_le (hb : b ≤ 32) (hn : n < 2 ^ 32)
    (hB : hashInputBound b ≤ B) (d : ByteArray.Bounded B) :
    ∑ ω : Bytes 16 × (Bytes b × (Fin (n - 1) → Bytes b)) × (PathValue n m → Bytes 32),
      {t | ∃ v, t = rawPathInput hb hB ω.1 ω.2.1.1 ω.2.1.2 v ω.2.2}.indicator
        (fun _ ↦ (Fintype.card
          (Bytes 16 × (Bytes b × (Fin (n - 1) → Bytes b)) × (PathValue n m → Bytes 32)) : ℝ)⁻¹)
        d ≤ preprocessingIncidenceReal b n m := by
  classical
  let Ω := Bytes 16 × (Bytes b × (Fin (n - 1) → Bytes b)) × (PathValue n m → Bytes 32)
  let : MeasurableSpace Ω := ⊤
  have hi : (uniformOn Set.univ : Measure Ω)
      {ω | ∃ v, d = rawPathInput hb hB ω.1 ω.2.1.1 ω.2.1.2 v ω.2.2} ≤
        preprocessingIncidence b n m := by
    have hp : Pr{let ω ← $ᵗ Ω}[
        ∃ v, d = rawPathInput hb hB ω.1 ω.2.1.1 ω.2.1.2 v ω.2.2] ≤
        preprocessingIncidence b n m := by
      rw [SampleableType.uniformSample_prod_eq_bind,
        SampleableType.uniformSample_prod_eq_bind]
      simpa only [prEvent_norm, preprocessingIncidence] using
        prEvent_eq_rawPathInput_seed_le hb hn hB d
    rwa [prEvent_eq_evalDist_of_discrete, SampleableType.evalDist_uniformSample] at hp
  rw [uniformOn_univ_apply_setOf] at hi
  have hr := ENNReal.toReal_mono (preprocessingIncidence_ne_top b n m) hi
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast] at hr
  unfold preprocessingIncidenceReal
  convert hr using 1
  simp only [Set.indicator_apply]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  rfl

end PointerChainPuzzle.LeanSeal
