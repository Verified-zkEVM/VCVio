/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.EvalDist.IndepProductMeasure
public import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure
public import VCVio.OracleComp.ProbComp.Basic

/-!
# Events on a tuple of independent uniform draws

`answerTape α q` draws `q` independent uniform values of `α` and collects them as a tuple, so
its denotation is the `q`-fold product of the uniform measure (`evalDist_answerTape`). This file
bounds the events a product measure makes cheap.

The basic shape is a *coordinatewise* event: an event constraining the coordinates
`p 0, …, p (k - 1)` by one condition each. `evalDist_answerTape_setOf_forall_mem_le_prod_image`
bounds it by a product over the coordinates `p` uses of the mass of the conjunction of the
conditions placed there, with no constraint on `p`. When `p` is injective each coordinate
carries one condition and the bound becomes the product `∏ ε i` of the individual masses
(`evalDist_answerTape_setOf_forall_mem_le_prod`); when it is not, the conditions sharing a
coordinate are charged jointly. An event that is a union over a finite set of coordinate
choices — the shape an adversary that picks where to place its conditions produces — is
bounded by the sum of the per-choice bounds
(`evalDist_answerTape_le_sum_of_subset_biUnion`).

`evalDist_answerTape_setOf_forall_mem_le_prod_adapted` is the *adapted* form: the condition on
coordinate `i` may depend on the coordinates strictly before `i`. That is what a retroactive
event needs — one of the shape "the answer at position `i` lies in the list of inputs assembled
at some position `j < i`", which constrains a fresh answer by data only the earlier answers
determine, and which no predicate on the answer cache alone expresses. The strict inequality is
load-bearing: a condition allowed to read coordinate `i` itself is not bounded by its own
uniform mass. The adapted form is proved by induction on the tuple length rather than through
`Measure.pi`, using the two bind bounds `evalDist_bind_apply_le_mul_of_forall` and
`evalDist_bind_apply_le_of_forall_notMem_eq_zero`, which localize the mass of a bind to a set of
draws for its first stage.

Every statement here is `ProbComp`-valued, which is why this file sits at the `ProbComp` layer;
the index-free product denotation it rests on is `VCVio.EvalDist.IndepProductMeasure`.
-/

public section

open MeasureTheory
open scoped ENNReal

/-! ## Localizing a bind to a set of first-stage draws -/

/-- A continuation bounded on a set of draws, and impossible off it, bounds the bind by the
product of that set's mass and the bound. -/
theorem evalDist_bind_apply_le_mul_of_forall {α β : Type} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] [MeasurableSpace β] (mx : ProbComp α) (f : α → ProbComp β)
    {E : Set β} (hE : MeasurableSet E) {G : Set α} (hG : MeasurableSet G) (c : ℝ≥0∞)
    (hin : ∀ x ∈ G, 𝒟[f x] E ≤ c) (hout : ∀ x ∉ G, 𝒟[f x] E = 0) :
    𝒟[mx >>= f] E ≤ 𝒟[mx] G * c := by
  rw [evalDist_bind_of_discrete, Measure.bind_apply hE Measurable.of_discrete.aemeasurable]
  calc ∫⁻ x, 𝒟[f x] E ∂𝒟[mx]
      ≤ ∫⁻ x, Set.indicator G (fun _ => c) x ∂𝒟[mx] := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ G
        · simpa [Set.indicator_of_mem hx] using hin x hx
        · simp [Set.indicator_of_notMem hx, hout x hx]
    _ = 𝒟[mx] G * c := by rw [lintegral_indicator_const hG, mul_comm]

/-- A continuation that can only reach `E` from a set `G` of draws bounds the bind by `G`'s
mass. -/
theorem evalDist_bind_apply_le_of_forall_notMem_eq_zero {α β : Type} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] [MeasurableSpace β] (mx : ProbComp α) (f : α → ProbComp β)
    {E : Set β} (hE : MeasurableSet E) {G : Set α} (hG : MeasurableSet G)
    (h : ∀ x ∉ G, 𝒟[f x] E = 0) : 𝒟[mx >>= f] E ≤ 𝒟[mx] G := by
  simpa using evalDist_bind_apply_le_mul_of_forall mx f hE hG 1
    (fun x _ => measure_le_one 𝒟[f x] E) h

namespace AnswerTape

/-! ## The tape draw -/

/-- `q` independent uniform draws from `α`, collected as a tuple. -/
noncomputable def answerTape (α : Type) [SampleableType α] (q : ℕ) : ProbComp (Fin q → α) :=
  Fin.mOfFn q (fun _ => ($ᵗ α : ProbComp α))

variable {α : Type} [SampleableType α] {q : ℕ}

@[simp] theorem answerTape_zero : answerTape α 0 = pure Fin.elim0 := by
  simp [answerTape, Fin.mOfFn]

/-- A tape of `n + 1` draws is one draw followed by a tape of `n`. -/
theorem answerTape_succ (n : ℕ) :
    answerTape α (n + 1) =
      (do let x ← ($ᵗ α : ProbComp α)
          let rest ← answerTape α n
          return (Fin.cons x rest : Fin (n + 1) → α)) := by
  simp [answerTape, Fin.mOfFn]

section Product

variable [MeasurableSpace α]

/-- The tape denotes the product of `q` copies of the uniform measure. -/
theorem evalDist_answerTape :
    𝒟[answerTape α q] = Measure.pi (fun _ : Fin q => 𝒟[($ᵗ α : ProbComp α)]) := by
  rw [answerTape, evalDist_mOfFn]

/-- A coordinatewise event on the tape has the product of the coordinate masses. -/
theorem evalDist_answerTape_univPi (S : Fin q → Set α) :
    𝒟[answerTape α q] (Set.univ.pi S) = ∏ i, 𝒟[($ᵗ α : ProbComp α)] (S i) := by
  rw [evalDist_answerTape, Measure.pi_pi]

/-- The coordinatewise conditions of an assignment `p`: coordinate `j` must satisfy every
condition whose role `p` places at `j`. -/
def piOfAssign {k : ℕ} (p : Fin k → Fin q) (S : Fin k → Set α) : Fin q → Set α :=
  fun j => ⋂ i ∈ ({i | p i = j} : Set (Fin k)), S i

omit [SampleableType α] [MeasurableSpace α] in
/-- The event that every role's coordinate satisfies that role's condition is the
coordinatewise event of `piOfAssign`. -/
theorem setOf_forall_mem_eq_univPi {k : ℕ} (p : Fin k → Fin q) (S : Fin k → Set α) :
    {v : Fin q → α | ∀ i, v (p i) ∈ S i} = Set.univ.pi (piOfAssign p S) := by
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_univ_pi, piOfAssign, Set.mem_iInter]
  exact ⟨fun h j i hi => hi ▸ h i, fun h i => h (p i) i rfl⟩

omit [SampleableType α] [MeasurableSpace α] in
/-- A coordinate satisfies its coordinatewise condition exactly when it satisfies every
condition the assignment places there. -/
theorem mem_piOfAssign {k : ℕ} {p : Fin k → Fin q} {S : Fin k → Set α} {j : Fin q} {x : α} :
    x ∈ piOfAssign p S j ↔ ∀ i, p i = j → x ∈ S i := by
  simp [piOfAssign]

omit [SampleableType α] [MeasurableSpace α] in
/-- At a coordinate that an injective assignment uses, the coordinatewise condition is exactly
the condition of the single role placed there. -/
theorem piOfAssign_apply_of_injective {k : ℕ} {p : Fin k → Fin q} (hp : Function.Injective p)
    (S : Fin k → Set α) (i : Fin k) : piOfAssign p S (p i) = S i := by
  have h : ({i' | p i' = p i} : Set (Fin k)) = {i} := by
    ext i'; exact ⟨fun h => hp h, fun h => by simp_all⟩
  rw [piOfAssign, h, Set.biInter_singleton]

/-- **The product bound at an arbitrary assignment.** The bound is a product over the
coordinates the assignment uses, of the mass of the *conjunction* of the conditions placed
there; coordinates the assignment does not use contribute nothing. No injectivity is required,
so a coordinate carrying several conditions is charged for their conjunction once rather than
for each condition separately. -/
theorem evalDist_answerTape_setOf_forall_mem_le_prod_image {k : ℕ} (p : Fin k → Fin q)
    (S : Fin k → Set α) (δ : Fin q → ℝ≥0∞)
    (hδ : ∀ j ∈ Finset.univ.image p, 𝒟[($ᵗ α : ProbComp α)] (piOfAssign p S j) ≤ δ j) :
    𝒟[answerTape α q] {v | ∀ i, v (p i) ∈ S i} ≤ ∏ j ∈ Finset.univ.image p, δ j := by
  classical
  rw [setOf_forall_mem_eq_univPi, evalDist_answerTape_univPi]
  have hsplit : ∏ j, 𝒟[($ᵗ α : ProbComp α)] (piOfAssign p S j) ≤
      ∏ j ∈ Finset.univ.image p, 𝒟[($ᵗ α : ProbComp α)] (piOfAssign p S j) := by
    rw [← Finset.prod_sdiff (Finset.subset_univ (Finset.univ.image p))]
    exact mul_le_of_le_one_left' (Finset.prod_le_one fun j _ => measure_le_one _ _)
  exact hsplit.trans (Finset.prod_le_prod hδ)

/-- **The product bound at an injective assignment.** If the coordinates `p 0, …, p (k - 1)` are
distinct and the `i`-th condition has uniform mass at most `ε i`, then the tape event that every
listed coordinate satisfies its condition has mass at most `∏ ε i`.

Distinctness is what makes the per-condition masses multiply; without it the conditions sharing
a coordinate must be charged jointly, which is
`evalDist_answerTape_setOf_forall_mem_le_prod_image`. -/
theorem evalDist_answerTape_setOf_forall_mem_le_prod {k : ℕ} {p : Fin k → Fin q}
    (hp : Function.Injective p) (S : Fin k → Set α) (ε : Fin k → ℝ≥0∞)
    (hS : ∀ i, 𝒟[($ᵗ α : ProbComp α)] (S i) ≤ ε i) :
    𝒟[answerTape α q] {v | ∀ i, v (p i) ∈ S i} ≤ ∏ i, ε i := by
  classical
  refine (evalDist_answerTape_setOf_forall_mem_le_prod_image p S
    (fun j => ∏ i ∈ Finset.univ.filter (fun i => p i = j), ε i) fun j hj => ?_).trans
    (le_of_eq (Finset.prod_fiberwise_of_maps_to
      (fun i _ => Finset.mem_image_of_mem p (Finset.mem_univ i)) ε))
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hj
  have hfil : Finset.univ.filter (fun i' => p i' = p i) = {i} := by
    ext i'; simp [hp.eq_iff]
  rw [hfil, Finset.prod_singleton, piOfAssign_apply_of_injective hp]
  exact hS i

/-- **`k` conditions of uniform mass at most `ε`, at distinct coordinates, cost `ε ^ k`.** -/
theorem evalDist_answerTape_setOf_forall_mem_le_pow {k : ℕ} {p : Fin k → Fin q}
    (hp : Function.Injective p) (S : Fin k → Set α) (ε : ℝ≥0∞)
    (hS : ∀ i, 𝒟[($ᵗ α : ProbComp α)] (S i) ≤ ε) :
    𝒟[answerTape α q] {v | ∀ i, v (p i) ∈ S i} ≤ ε ^ k := by
  simpa using evalDist_answerTape_setOf_forall_mem_le_prod hp S (fun _ => ε) hS

/-- **The union over a finite set of choices.** An event covered by the choices `c ∈ C` costs at
most the sum of the per-choice bounds. -/
theorem evalDist_answerTape_le_sum_of_subset_biUnion {γ : Type} (C : Finset γ)
    (E : Set (Fin q → α)) (F : γ → Set (Fin q → α)) (b : γ → ℝ≥0∞)
    (hsub : E ⊆ ⋃ c ∈ C, F c) (hb : ∀ c ∈ C, 𝒟[answerTape α q] (F c) ≤ b c) :
    𝒟[answerTape α q] E ≤ ∑ c ∈ C, b c :=
  (measure_mono hsub).trans <| (measure_biUnion_finset_le C F).trans <| Finset.sum_le_sum hb

end Product

/-! ## The adapted product bound -/

section Adapted

variable [MeasurableSpace α] [DiscreteMeasurableSpace α] [Nonempty α]

/-- **The adapted product bound.** `S i v` is the condition on coordinate `i`, allowed to depend
on the coordinates strictly before `i`. If each condition has uniform mass at most `ε i`
whatever the earlier coordinates, the event that every coordinate satisfies its own condition
has mass at most `∏ ε i`. -/
theorem evalDist_answerTape_setOf_forall_mem_le_prod_adapted :
    ∀ (n : ℕ) (S : Fin n → (Fin n → α) → Set α) (ε : Fin n → ℝ≥0∞),
      (∀ (i : Fin n) (v w : Fin n → α), (∀ j : Fin n, (j : ℕ) < (i : ℕ) → v j = w j) →
        S i v = S i w) →
      (∀ (i : Fin n) (v : Fin n → α), 𝒟[($ᵗ α : ProbComp α)] (S i v) ≤ ε i) →
      𝒟[answerTape α n] {v | ∀ i, v i ∈ S i v} ≤ ∏ i, ε i := by
  intro n
  induction n with
  | zero => intro S ε _ _; simp
  | succ n ih =>
    intro S ε hadapt hS
    set d : Fin (n + 1) → α := fun _ => Classical.arbitrary α with hd
    set G : Set α := S 0 d with hG
    have hS0 : ∀ v : Fin (n + 1) → α, S 0 v = G := fun v =>
      hadapt 0 v d fun j hj => absurd hj (by simp)
    set S' : α → Fin n → (Fin n → α) → Set α :=
      fun x i rest => S i.succ (Fin.cons x rest) with hS'
    have hadapt' : ∀ (x : α) (i : Fin n) (v w : Fin n → α),
        (∀ j : Fin n, (j : ℕ) < (i : ℕ) → v j = w j) → S' x i v = S' x i w := by
      intro x i v w hvw
      refine hadapt i.succ _ _ fun j => ?_
      refine Fin.cases (fun _ => by simp) (fun j' hj => ?_) j
      simp only [Fin.val_succ] at hj
      simpa only [Fin.cons_succ] using hvw j' (by omega)
    have hmem : ∀ (x : α) (rest : Fin n → α),
        ((Fin.cons x rest : Fin (n + 1) → α) ∈ {v | ∀ i, v i ∈ S i v}) ↔
          (x ∈ G ∧ ∀ i, rest i ∈ S' x i rest) := by
      intro x rest
      refine ⟨fun hv => ⟨by simpa [hS0] using hv 0, fun i => by simpa [hS'] using hv i.succ⟩, ?_⟩
      rintro ⟨hx, hrest⟩ i
      refine Fin.cases ?_ (fun i' => ?_) i
      · simpa [hS0] using hx
      · simpa [hS'] using hrest i'
    have hpre : ∀ x : α, 𝒟[answerTape α n >>= fun rest =>
          (pure (Fin.cons x rest) : ProbComp (Fin (n + 1) → α))] {v | ∀ i, v i ∈ S i v} =
        𝒟[answerTape α n]
          ((fun rest : Fin n → α => (Fin.cons x rest : Fin (n + 1) → α)) ⁻¹'
            {v | ∀ i, v i ∈ S i v}) := fun x => by
      rw [bind_pure_comp, evalDist_map_of_discrete,
        Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
    rw [answerTape_succ, Fin.prod_univ_succ]
    refine le_trans (evalDist_bind_apply_le_mul_of_forall ($ᵗ α)
      (fun x => answerTape α n >>= fun rest =>
        (pure (Fin.cons x rest) : ProbComp (Fin (n + 1) → α)))
      (E := {v | ∀ i, v i ∈ S i v}) MeasurableSet.of_discrete
      (G := G) MeasurableSet.of_discrete (∏ i : Fin n, ε i.succ)
      (fun x hx => ?_) (fun x hx => ?_)) (by gcongr; exact hS 0 d)
    · rw [hpre x]
      refine le_trans (le_of_eq (congrArg _ ?_))
        (ih (S' x) (fun i => ε i.succ) (hadapt' x) (fun i v => hS i.succ _))
      ext rest
      simp only [Set.mem_preimage, Set.mem_ofPred_eq]
      exact ⟨fun hv => ((hmem x rest).mp hv).2, fun hr => (hmem x rest).mpr ⟨hx, hr⟩⟩
    · rw [hpre x]
      have hempty : (fun rest : Fin n → α => (Fin.cons x rest : Fin (n + 1) → α)) ⁻¹'
          {v | ∀ i, v i ∈ S i v} = ∅ := by
        ext rest
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact fun hv => hx ((hmem x rest).mp hv).1
      rw [hempty, measure_empty]

end Adapted

end AnswerTape
