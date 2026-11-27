/-
Copyright (c) 2026 aryaethn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/
module

public import VCVio.CryptoFoundations.Rewinding.BlockRound
public import VCVio.CryptoFoundations.Rewinding.ThresholdEager
public import VCVio.OracleComp.EvalDist.PiSampling

/-!
# The block step against children sampled in advance

`Rewinding.blockChildren` runs a child at a centre and collects, from a pool per coordinate, the
successful children of every coordinate. With a counter for the cost of the children, it runs in
`StateT ℕ ProbComp`, as the threshold step does. A child sampled in advance is a pair of a result
and a cost, read by `Rewinding.tableChild`.

This file reads the block step against children sampled in advance, in three forms.

* On lists of results (`Rewinding.blockTableRun`), the step is a loop over `ProbComp.drawUntil`
  that charges the cost of every entry it reads (`Rewinding.blockTableRun_eq`).
* With probabilistic children (`Rewinding.chargedChild`), the step has the law of the same step run
  on results sampled in advance: the result at the centre and, independently for every coordinate,
  one result per entry of its pool (`Rewinding.blockChildren_eager`).
* When the pools have no repeated entry, no entry in two pools, and do not contain the centre, the
  step has the law of drawing one table of independent results of all children and reading it at
  the centre and along the pools (`Rewinding.blockChildren_eager_table`). This is the form in which
  a bound proved for every table holds in expectation.
-/

public section

open OracleComp OracleSpec

namespace Rewinding

/-- The charged child has an additive counter. -/
theorem counterAdditive_chargedChild {C W : Type} (child : C → ProbComp (Option W × ℕ)) (c : C) :
    CounterAdditive (chargedChild child c) := by
  intro s
  simp only [chargedChild, StateT.run_mk, Functor.map_map, zero_add]

/-- A child read from a table has an additive counter. -/
theorem counterAdditive_tableChild {W : Type} (z : Option W × ℕ) :
    CounterAdditive (tableChild z) := by
  intro s
  simp only [tableChild, StateT.run_mk, map_pure, zero_add]

/-- A collector of children with additive counters has an additive counter. -/
theorem collectChildren_run_add {C W : Type} (sample : (n : ℕ) → ProbComp (Fin (n + 1)))
    (child : C → StateT ℕ ProbComp (Option W)) (hchild : ∀ c, CounterAdditive (child c))
    (n : ℕ) : ∀ (r : ℕ) (pool : List C), pool.length = n →
      CounterAdditive (collectChildren (fun n => StateT.lift (sample n)) child r pool) := by
  induction n with
  | zero =>
      intro r pool hp s
      obtain rfl := List.length_eq_zero_iff.mp hp
      cases r <;> simp
  | succ n ih =>
      intro r pool hp s
      cases r with
      | zero => simp
      | succ r =>
          rw [collectChildren_run_step sample child r pool n hp s,
            collectChildren_run_step sample child r pool n hp 0, map_bind]
          refine bind_congr fun i => ?_
          have hlen : (pool.eraseIdx i).length = n := by
            rw [List.length_eraseIdx_of_lt (by omega)]
            omega
          rw [hchild _ s, bind_map_left, map_bind]
          refine bind_congr fun z => ?_
          cases z.1 with
          | none =>
              simp only
              rw [ih _ _ hlen, ih _ _ hlen z.2, Functor.map_map]
              simp only [Nat.add_assoc]
          | some w =>
              simp only
              rw [ih _ _ hlen, ih _ _ hlen z.2, Functor.map_map, Functor.map_map,
                Functor.map_map]
              simp only [Nat.add_assoc]

/-- Collecting from the image of a pool is collecting from the pool with the relabelled child. -/
theorem collectChildren_map {C D W : Type} (sample : (n : ℕ) → ProbComp (Fin (n + 1)))
    (child : D → StateT ℕ ProbComp (Option W)) (g : C → D) (n : ℕ) :
    ∀ (r : ℕ) (pool : List C), pool.length = n →
      collectChildren (fun n => StateT.lift (sample n)) child r (pool.map g) =
        collectChildren (fun n => StateT.lift (sample n)) (child ∘ g) r pool := by
  induction n with
  | zero =>
      intro r pool hp
      obtain rfl := List.length_eq_zero_iff.mp hp
      cases r <;> simp
  | succ n ih =>
      intro r pool hp
      cases r with
      | zero => simp
      | succ r =>
          refine StateT.ext fun count => ?_
          rw [collectChildren_run_step sample child r (pool.map g) n (by simpa using hp) count,
            collectChildren_run_step sample (child ∘ g) r pool n hp count]
          refine bind_congr fun i => ?_
          have hlen : (pool.eraseIdx i).length = n := by
            rw [List.length_eraseIdx_of_lt (by omega)]
            omega
          simp only [List.getElem_map, Function.comp_apply]
          refine bind_congr fun z => ?_
          cases z.1 <;> simp only [List.eraseIdx_map, ih _ _ hlen]

/-- Running the block step on the image of a centre and pools is running it with the relabelled
child. -/
theorem blockChildren_map {ι : Type} [Fintype ι] {C D W : Type}
    (sample : (n : ℕ) → ProbComp (Fin (n + 1))) (child : D → StateT ℕ ProbComp (Option W))
    (g : C → D) (k : ι → ℕ) (c₀ : C) (pools : ι → List C) :
    blockChildren (fun n => StateT.lift (sample n)) child k (g c₀) (fun j => (pools j).map g) =
      blockChildren (fun n => StateT.lift (sample n)) (child ∘ g) k c₀ pools := by
  simp only [blockChildren, Function.comp_apply,
    fun j => collectChildren_map sample child g _ (k j - 1) (pools j) rfl]

section Block

variable {ι : Type} [Fintype ι] {C W : Type}

/-- The block step run from the counter `count` on results sampled in advance: the result `z₀` at
the centre, and the list `tables j` of results along the pool of coordinate `j`. -/
@[expose] noncomputable def blockTableRun (k : ι → ℕ) (z₀ : Option W × ℕ)
    (tables : ι → List (Option W × ℕ)) (count : ℕ) :
    ProbComp (Option (W × (ι → List W)) × ℕ) :=
  (blockChildren (fun n => StateT.lift (ProbComp.uniformFin n)) tableChild k z₀ tables).run count

/-- **The block step on results.** It reads the centre's result and then, if that succeeded, draws
every coordinate's list without replacement until `k j - 1` results succeed or the list runs out.
It charges the cost of every result it reads. -/
theorem blockTableRun_eq (k : ι → ℕ) (z₀ : Option W × ℕ) (tables : ι → List (Option W × ℕ))
    (count : ℕ) :
    blockTableRun k z₀ tables count =
      match z₀.1 with
      | none => pure (none, count + z₀.2)
      | some w₀ =>
          (fun d : ι → List (Option W × ℕ) =>
            (if ∀ j, ((d j).filterMap Prod.fst).length = k j - 1 then
                some (w₀, fun j => (d j).filterMap Prod.fst)
              else none,
              count + z₀.2 + ∑ j, ((d j).map Prod.snd).sum)) <$>
            Fintype.mPi fun j =>
              ProbComp.drawUntil (fun z : Option W × ℕ => z.1.isSome) (k j - 1) (tables j) := by
  have hg : ∀ j, CounterAdditive (collectChildren (fun n => StateT.lift (ProbComp.uniformFin n))
      tableChild (k j - 1) (tables j)) := fun j =>
    collectChildren_run_add _ _ counterAdditive_tableChild _ _ _ rfl
  unfold blockTableRun blockChildren
  rw [StateT.run_bind]
  simp only [tableChild, StateT.run_mk, pure_bind]
  cases hw : z₀.1 with
  | none => simp
  | some w₀ =>
      simp only
      rw [StateT.run_bind, run_mPi_add _ hg]
      simp only [collectChildren_table _ _ _ rfl 0, ← Fintype.mPi_map, bind_map_left,
        Functor.map_map, StateT.run_pure, zero_add]
      rw [map_eq_bind_pure_comp]
      rfl

/-- **The eager block step.** With probabilistic children, the block step has the law of the step
run on results sampled in advance: the result at the centre and, independently for every
coordinate, one result per entry of its pool. -/
theorem blockChildren_eager (child : C → ProbComp (Option W × ℕ)) (k : ι → ℕ) (c₀ : C)
    (pools : ι → List C) (count : ℕ) :
    (blockChildren (fun n => StateT.lift (ProbComp.uniformFin n)) (chargedChild child) k c₀
        pools).run count =ᵈ
      (do
        let z₀ ← child c₀
        let tables ← Fintype.mPi fun j => (pools j).mapM child
        blockTableRun k z₀ tables count) := by
  have hcharged : ∀ j, CounterAdditive (collectChildren
      (fun n => StateT.lift (ProbComp.uniformFin n)) (chargedChild child) (k j - 1) (pools j)) :=
    fun j => collectChildren_run_add _ _ (counterAdditive_chargedChild child) _ _ _ rfl
  have htable : ∀ (tables : ι → List (Option W × ℕ)) j, CounterAdditive (collectChildren
      (fun n => StateT.lift (ProbComp.uniformFin n)) tableChild (k j - 1) (tables j)) :=
    fun tables j => collectChildren_run_add _ _ counterAdditive_tableChild _ _ _ rfl
  simp only [blockTableRun, blockChildren, StateT.run_bind, chargedChild, StateT.run_mk,
    bind_map_left, tableChild, pure_bind]
  refine EvalDistEq.bind_right _ fun z₀ => ?_
  cases z₀.1 with
  | none =>
      simp only [StateT.run_pure]
      exact (OracleComp.EvalDistEq.bind_const _ _).symm
  | some w₀ =>
      simp only [StateT.run_bind, run_mPi_add _ hcharged, run_mPi_add _ (htable _), bind_map_left,
        StateT.run_pure]
      have heager := Fintype.mPi_evalDistEq fun j =>
        collectChildren_eager ProbComp.uniformFin child _ (k j - 1) (pools j) rfl 0
      refine (heager.bind_left _).trans ?_
      refine ((Fintype.mPi_bind_evalDistEq _ _).bind_left _).trans ?_
      simp only [bind_assoc]
      exact .rfl

/-- **The block step against a table of children.** With probabilistic children, the block step
has the law of drawing a table of independent results of all children in advance and running the
step with the table as the child, when the pools have no repeated entry, no entry in two pools, and
do not contain the centre. -/
theorem blockChildren_eager_table [Fintype C]
    (child : C → ProbComp (Option W × ℕ)) (k : ι → ℕ) (c₀ : C) (pools : ι → List C)
    (hnd : ∀ j, (pools j).Nodup) (hdisj : ∀ j j' c, c ∈ pools j → c ∈ pools j' → j = j')
    (hc₀ : ∀ j, c₀ ∉ pools j) (count : ℕ) :
    (blockChildren (fun n => StateT.lift (ProbComp.uniformFin n)) (chargedChild child) k c₀
        pools).run count =ᵈ
      (do
        let T ← Fintype.mPi child
        (blockChildren (fun n => StateT.lift (ProbComp.uniformFin n)) (tableChild ∘ T) k c₀
          pools).run count) := by
  classical
  refine (blockChildren_eager child k c₀ pools count).trans ?_
  simp only [← blockChildren_map]
  have h := EvalDistEq.bind_left (m := ProbComp)
    (Fintype.mPi_map_eval_lists child c₀ pools hnd hdisj hc₀)
    (fun p => blockTableRun k p.1 p.2 count)
  simp only [bind_map_left, bind_assoc, pure_bind] at h
  exact h.symm

end Block

end Rewinding
