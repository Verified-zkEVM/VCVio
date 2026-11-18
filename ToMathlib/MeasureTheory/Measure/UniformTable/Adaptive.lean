/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import ToMathlib.MeasureTheory.Measure.UniformTable.Encoding

/-!
# Adaptive exchanges between table cells and labels

Each exchange swaps the visible part of a table response with one auxiliary label and retains
the response tail. The address may depend on other labels, but is invariant under changing the
label being exchanged and does not depend on the table. This makes the exchange involutive.

Composing exchanges in any order therefore preserves the complete uniform joint law, including
all displaced values. For a causal order of distinct labels, the inverse table is obtained by
writing the supplied labels in reverse order. Each write retains the tail of the current
table response, even when two writes address the same cell.
-/

public section

namespace Equiv

variable {D V M : Type*} {A Tail : V → Type*} [DecidableEq D]

section Exchange

variable [DecidableEq V]

/-- Exchange a visible table response and a label, retaining the complementary response tail. -/
@[expose]
def tableLabelExchangeStep {T : Type*} (v : V) (input : (∀ w, A w) → D)
    (split : M ≃ A v × T) (p : (D → M) × (∀ w, A w)) :
    (D → M) × (∀ w, A w) :=
  (Function.update p.1 (input p.2) (split.symm (p.2 v, (split (p.1 (input p.2))).2)),
    Function.update p.2 v (split (p.1 (input p.2))).1)

/-- An exchange is involutive when its address does not depend on its own label. -/
theorem tableLabelExchangeStep_involutive {T : Type*} (v : V)
    (input : (∀ w, A w) → D) (split : M ≃ A v × T)
    (hinput : ∀ (l : ∀ w, A w) a, input (Function.update l v a) = input l) :
    Function.Involutive (tableLabelExchangeStep v input split) := by
  rintro ⟨H, l⟩
  apply Prod.ext <;> simp [tableLabelExchangeStep, hinput]

/-- The exchanged label records the old visible response. -/
@[simp]
theorem tableLabelExchangeStep_snd_self {T : Type*} (v : V)
    (input : (∀ w, A w) → D) (split : M ≃ A v × T)
    (p : (D → M) × (∀ w, A w)) :
    (tableLabelExchangeStep v input split p).2 v = (split (p.1 (input p.2))).1 := by
  simp [tableLabelExchangeStep]

/-- Splitting the new selected response gives the old label and the original tail. -/
@[simp]
theorem tableLabelExchangeStep_fst_input {T : Type*} (v : V)
    (input : (∀ w, A w) → D) (split : M ≃ A v × T)
    (p : (D → M) × (∀ w, A w)) :
    split ((tableLabelExchangeStep v input split p).1 (input p.2)) =
      (p.2 v, (split (p.1 (input p.2))).2) := by
  simp [tableLabelExchangeStep]

/-- The permutation exchanging one auxiliary label with the visible part of a table cell.
The chosen input is a function of the labels alone and is invariant under its own update. -/
@[expose]
def tableLabelExchange {T : Type*} (v : V) (input : (∀ w, A w) → D)
    (split : M ≃ A v × T)
    (hinput : ∀ (l : ∀ w, A w) a, input (Function.update l v a) = input l) :
    ((D → M) × (∀ w, A w)) ≃ ((D → M) × (∀ w, A w)) :=
  Function.Involutive.toPerm _ (tableLabelExchangeStep_involutive v input split hinput)

/-- The exchange permutation performs its explicit table-and-label update. -/
@[simp]
theorem tableLabelExchange_apply {T : Type*} (v : V) (input : (∀ w, A w) → D)
    (split : M ≃ A v × T)
    (hinput : ∀ (l : ∀ w, A w) a, input (Function.update l v a) = input l)
    (p : (D → M) × (∀ w, A w)) :
    tableLabelExchange v input split hinput p = tableLabelExchangeStep v input split p := rfl

/-- The inverse of a single exchange is the same explicit update. -/
@[simp]
theorem tableLabelExchange_symm_apply {T : Type*} (v : V) (input : (∀ w, A w) → D)
    (split : M ≃ A v × T)
    (hinput : ∀ (l : ∀ w, A w) a, input (Function.update l v a) = input l)
    (p : (D → M) × (∀ w, A w)) :
    (tableLabelExchange v input split hinput).symm p =
      tableLabelExchangeStep v input split p := rfl

/-- Execute a list of adaptive exchanges from its head to its tail. -/
@[expose]
def tableLabelExchangeList (input : V → (∀ w, A w) → D)
    (split : ∀ v, M ≃ A v × Tail v)
    (hinput : ∀ v (l : ∀ w, A w) a, input v (Function.update l v a) = input v l) :
    List V → (((D → M) × (∀ w, A w)) ≃ ((D → M) × (∀ w, A w)))
  | [] => Equiv.refl _
  | v :: vs => (tableLabelExchange v (input v) (split v) (hinput v)).trans
      (tableLabelExchangeList input split hinput vs)

/-- An empty exchange list is the identity. -/
@[simp]
theorem tableLabelExchangeList_nil (input : V → (∀ w, A w) → D)
    (split : ∀ v, M ≃ A v × Tail v)
    (hinput : ∀ v (l : ∀ w, A w) a, input v (Function.update l v a) = input v l) :
    tableLabelExchangeList input split hinput [] = Equiv.refl _ := rfl

/-- Forward execution exchanges the first label and then executes the remaining list. -/
@[simp]
theorem tableLabelExchangeList_cons_apply (input : V → (∀ w, A w) → D)
    (split : ∀ v, M ≃ A v × Tail v)
    (hinput : ∀ v (l : ∀ w, A w) a, input v (Function.update l v a) = input v l)
    (v : V) (vs : List V) (p : (D → M) × (∀ w, A w)) :
    tableLabelExchangeList input split hinput (v :: vs) p =
      tableLabelExchangeList input split hinput vs
        (tableLabelExchangeStep v (input v) (split v) p) := rfl

/-- Inverse execution reverses the list, applying its first exchange last. -/
@[simp]
theorem tableLabelExchangeList_cons_symm_apply (input : V → (∀ w, A w) → D)
    (split : ∀ v, M ≃ A v × Tail v)
    (hinput : ∀ v (l : ∀ w, A w) a, input v (Function.update l v a) = input v l)
    (v : V) (vs : List V) (p : (D → M) × (∀ w, A w)) :
    (tableLabelExchangeList input split hinput (v :: vs)).symm p =
      tableLabelExchangeStep v (input v) (split v)
        ((tableLabelExchangeList input split hinput vs).symm p) := rfl

/-- An observation invariant under each exchanged label update is unchanged by inverse execution. -/
theorem tableLabelExchangeList_symm_snd_invariant {Z : Type*}
    (input : V → (∀ w, A w) → D) (split : ∀ v, M ≃ A v × Tail v)
    (hinput : ∀ v (l : ∀ w, A w) a, input v (Function.update l v a) = input v l)
    (vs : List V) (f : (∀ w, A w) → Z)
    (hf : ∀ v ∈ vs, ∀ (l : ∀ w, A w) a, f (Function.update l v a) = f l)
    (p : (D → M) × (∀ w, A w)) :
    f ((tableLabelExchangeList input split hinput vs).symm p).2 = f p.2 := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    rw [tableLabelExchangeList_cons_symm_apply]
    change f (Function.update _ v _) = _
    rw [hf v List.mem_cons_self]
    exact ih (fun w hw ↦ hf w (List.mem_cons_of_mem _ hw))

end Exchange

/-- Write fixed labels in reverse list order, retaining the current response tail at each write. -/
@[expose]
def tableLabelProgram (input : V → (∀ w, A w) → D)
    (split : ∀ v, M ≃ A v × Tail v) : List V → (D → M) → (∀ w, A w) → D → M
  | [], H, _ => H
  | v :: vs, H, l =>
      let H' := tableLabelProgram input split vs H l
      Function.update H' (input v l) ((split v).symm (l v, (split v (H' (input v l))).2))

/-- A point not written by any label retains its original raw response. -/
theorem tableLabelProgram_apply_of_avoids
    (input : V → (∀ w, A w) → D) (split : ∀ v, M ≃ A v × Tail v)
    (vs : List V) (H : D → M) (l : ∀ w, A w) (d : D)
    (havoid : ∀ v ∈ vs, input v l ≠ d) :
    tableLabelProgram input split vs H l d = H d := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    rw [tableLabelProgram, Function.update_of_ne (Ne.symm (havoid v List.mem_cons_self))]
    exact ih (fun w hw ↦ havoid w (List.mem_cons_of_mem _ hw))

/-- At distinct written cells, programming rejoins each fixed label with that cell's original
response tail. -/
theorem tableLabelProgram_apply_of_injective
    (input : V → (∀ w, A w) → D) (split : ∀ v, M ≃ A v × Tail v)
    (vs : List V) (H : D → M) (l : ∀ w, A w) (hnodup : vs.Nodup)
    (hinj : Function.Injective (fun v ↦ input v l)) {v : V} (hv : v ∈ vs) :
    tableLabelProgram input split vs H l (input v l) =
      (split v).symm (l v, (split v (H (input v l))).2) := by
  classical
  induction vs with
  | nil => simp at hv
  | cons w vs ih =>
    have hn := List.nodup_cons.mp hnodup
    by_cases hvw : v = w
    · subst v
      rw [tableLabelProgram, Function.update_self]
      rw [tableLabelProgram_apply_of_avoids input split vs H l (input w l)
        (fun u hu he ↦ hn.1 (hinj he ▸ hu))]
    · rw [tableLabelProgram, Function.update_of_ne (fun he ↦ hvw (hinj he))]
      exact ih hn.2 ((List.mem_cons.mp hv).resolve_left hvw)

/-- In a causal list of distinct labels, the inverse exchange table writes the supplied labels
in reverse order. No distinctness assumption is imposed on the addressed table cells. -/
theorem tableLabelExchangeList_symm_fst [DecidableEq V]
    (input : V → (∀ w, A w) → D) (split : ∀ v, M ≃ A v × Tail v)
    (hinput : ∀ v (l : ∀ w, A w) a, input v (Function.update l v a) = input v l)
    (vs : List V) (hnodup : vs.Nodup)
    (hcausal : vs.Pairwise fun v w ↦
      ∀ (l : ∀ w, A w) a, input v (Function.update l w a) = input v l)
    (p : (D → M) × (∀ w, A w)) :
    ((tableLabelExchangeList input split hinput vs).symm p).1 =
      tableLabelProgram input split vs p.1 p.2 := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    have hn := List.nodup_cons.mp hnodup
    have hc := List.pairwise_cons.mp hcausal
    have hi := tableLabelExchangeList_symm_snd_invariant input split hinput vs (input v) hc.1 p
    have hl := tableLabelExchangeList_symm_snd_invariant input split hinput vs
      (fun l ↦ l v) (fun w hw l a ↦ by
        have hwv : v ≠ w := fun h ↦ hn.1 (h ▸ hw)
        exact Function.update_of_ne hwv a l) p
    rw [tableLabelExchangeList_cons_symm_apply]
    simp only [tableLabelExchangeStep, tableLabelProgram, hi, hl, ih hn.2 hc.2]

end Equiv

namespace ProbabilityTheory

open MeasureTheory

/-- Reversing an adaptive exchange permutation preserves every finite uniform joint experiment.
The continuation may observe the complete table and all label coordinates together. -/
theorem uniformOn_univ_bind_tableLabelExchangeList_symm
    {D V M : Type*} {A Tail : V → Type*} [DecidableEq D] [DecidableEq V]
    [Finite ((D → M) × (∀ w, A w))]
    [MeasurableSpace ((D → M) × (∀ w, A w))]
    [MeasurableSingletonClass ((D → M) × (∀ w, A w))]
    {Z : Type*} [MeasurableSpace Z]
    (input : V → (∀ w, A w) → D) (split : ∀ v, M ≃ A v × Tail v)
    (hinput : ∀ v (l : ∀ w, A w) a, input v (Function.update l v a) = input v l)
    (vs : List V) (f : ((D → M) × (∀ w, A w)) → Measure Z) :
    (uniformOn Set.univ : Measure ((D → M) × (∀ w, A w))).bind f =
      (uniformOn Set.univ : Measure ((D → M) × (∀ w, A w))).bind
        (fun p ↦ f ((Equiv.tableLabelExchangeList input split hinput vs).symm p)) :=
  uniformOn_univ_bind_equiv (Equiv.tableLabelExchangeList input split hinput vs).symm f

end ProbabilityTheory
