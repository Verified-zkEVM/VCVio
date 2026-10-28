/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.Rewinding.ThresholdRound
public import VCVio.OracleComp.EvalDist.ListSampling
public import VCVio.CryptoFoundations.Rewinding.ThresholdWeights

/-!
# Eager child tables for threshold extraction

A threshold attempt visits each pool position at most once. Sampling all child results before
the attempt therefore preserves its joint output and accumulated child cost distribution.
-/

public section

open OracleComp OracleSpec

namespace Rewinding

/-- One collector step, with its uniform index range identified by the pool length. -/
theorem collectChildren_run_step {C W : Type}
    (sample : (n : ℕ) → ProbComp (Fin (n + 1)))
    (child : C → StateT ℕ ProbComp (Option W)) (r : ℕ) (pool : List C)
    (n : ℕ) (hlen : pool.length = n + 1) (count : ℕ) :
    (collectChildren (fun n => StateT.lift (sample n)) child (r + 1) pool).run count =
      (do
        let i ← sample n
        let z ← (child (pool[(i : ℕ)]'(by omega))).run count
        match z.1 with
        | none => (collectChildren (fun n => StateT.lift (sample n)) child (r + 1)
            (pool.eraseIdx i)).run z.2
        | some w => (fun t : List W × ℕ => (w :: t.1, t.2)) <$>
            (collectChildren (fun n => StateT.lift (sample n)) child r
              (pool.eraseIdx i)).run z.2) := by
  cases pool with
  | nil => simp at hlen
  | cons c cs =>
      have hn : n = cs.length := by simpa using hlen.symm
      subst n
      simp only [collectChildren_cons, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
      congr 1
      funext i
      congr 1
      funext z
      cases z.1 <;> simp only [StateT.run_map]

/-- Execute a probabilistic child and add its reported cost to the running counter. -/
@[expose] def chargedChild {C W : Type} (child : C → ProbComp (Option W × ℕ))
    (c : C) : StateT ℕ ProbComp (Option W) :=
  StateT.mk fun n => (fun z => (z.1, n + z.2)) <$> child c

/-- Read a previously sampled child result and charge its stored cost. -/
@[expose] def tableChild {W : Type} (z : Option W × ℕ) : StateT ℕ ProbComp (Option W) :=
  StateT.mk fun n => pure (z.1, n + z.2)

private def collectTableStep {W : Type}
    (sample : (n : ℕ) → ProbComp (Fin (n + 1))) (r : ℕ) (n : ℕ)
    (table : List (Option W × ℕ)) (count : ℕ) : ProbComp (List W × ℕ) := do
  let i ← sample n
  let z := table[(i : ℕ)]?.getD (none, 0)
  match z.1 with
  | none => (collectChildren (fun n => StateT.lift (sample n)) tableChild (r + 1)
      (table.eraseIdx i)).run (count + z.2)
  | some w => (fun t : List W × ℕ => (w :: t.1, t.2)) <$>
      (collectChildren (fun n => StateT.lift (sample n)) tableChild r
        (table.eraseIdx i)).run (count + z.2)

private theorem collect_table_step {W : Type}
    (sample : (n : ℕ) → ProbComp (Fin (n + 1))) (r : ℕ)
    (table : List (Option W × ℕ)) (n : ℕ) (hlen : table.length = n + 1) (count : ℕ) :
    (collectChildren (fun n => StateT.lift (sample n)) tableChild (r + 1) table).run count =
      collectTableStep sample r n table count := by
  rw [collectChildren_run_step sample tableChild r table n hlen count]
  simp only [tableChild, StateT.run_mk, pure_bind, collectTableStep]
  congr 1
  funext i
  rw [List.getElem?_eq_getElem (by omega)]
  rfl

/-- Sampling every child in advance preserves the collector's output and accumulated cost.
The eager pool contains one independently drawn result for every original pool position. -/
theorem collectChildren_eager {C W : Type}
    (sample : (n : ℕ) → ProbComp (Fin (n + 1)))
    (child : C → ProbComp (Option W × ℕ)) (n : ℕ) :
    ∀ (r : ℕ) (pool : List C), pool.length = n → ∀ count : ℕ,
    (collectChildren (fun n => StateT.lift (sample n)) (chargedChild child) r pool).run count =ᵈ
      (do let table ← pool.mapM child
          (collectChildren (fun n => StateT.lift (sample n)) tableChild r table).run count) := by
  induction n with
  | zero =>
      intro r pool hp count
      obtain rfl := List.length_eq_zero_iff.mp hp
      simp
  | succ n ih =>
      intro r pool hp count
      cases r with
      | zero =>
          simp only [collectChildren_zero, StateT.run_pure]
          exact (OracleComp.EvalDistEq.bind_const (pool.mapM child) (pure ([], count))).symm
      | succ r =>
          have hright :
              (do let table ← pool.mapM child
                  (collectChildren (fun n => StateT.lift (sample n)) tableChild
                    (r + 1) table).run count) =ᵈ
              (do let table ← pool.mapM child
                  collectTableStep sample r n table count) := by
            apply OracleComp.EvalDistEq.bind_congr_of_support
            intro table ht
            rw [collect_table_step sample r table n
              ((List.length_of_mem_support_mapM child pool table ht).trans hp)]
          rw [collectChildren_run_step sample (chargedChild child) r pool n hp count]
          simp only [chargedChild, StateT.run_mk, bind_map_left]
          refine EvalDistEq.trans ?_ hright.symm
          have hswap := OracleComp.EvalDistEq.bind_bind_swap (pool.mapM child) (sample n)
            (fun table i =>
              let z := table[(i : ℕ)]?.getD (none, 0)
              match z.1 with
              | none => (collectChildren (fun n => StateT.lift (sample n)) tableChild
                  (r + 1) (table.eraseIdx i)).run (count + z.2)
              | some w => (fun t : List W × ℕ => (w :: t.1, t.2)) <$>
                  (collectChildren (fun n => StateT.lift (sample n)) tableChild r
                    (table.eraseIdx i)).run (count + z.2))
          refine EvalDistEq.trans ?_ hswap.symm
          apply EvalDistEq.bind_right
          intro i
          have hi : (i : ℕ) < pool.length := by omega
          refine EvalDistEq.trans ?_ (mapM_bind_eraseIdx child pool i hi (none, 0)
            (fun z xs =>
              match z.1 with
              | none => (collectChildren (fun n => StateT.lift (sample n)) tableChild
                  (r + 1) xs).run (count + z.2)
              | some w => (fun t : List W × ℕ => (w :: t.1, t.2)) <$>
                  (collectChildren (fun n => StateT.lift (sample n)) tableChild r
                    xs).run (count + z.2)))
          apply EvalDistEq.bind_right
          intro z
          have hlen : (pool.eraseIdx i).length = n := by
            rw [List.length_eraseIdx_of_lt hi, hp]
            omega
          cases hz : z.1 with
          | none => simpa only [hz] using ih (r + 1) (pool.eraseIdx i) hlen (count + z.2)
          | some w =>
              simpa only [hz, map_bind] using
                (ih r (pool.eraseIdx i) hlen (count + z.2)).map
                  (fun t : List W × ℕ => (w :: t.1, t.2))

private def thresholdTableStep {W : Type}
    (sample : (n : ℕ) → ProbComp (Fin (n + 1))) (r : ℕ) (n : ℕ)
    (table : List (Option W × ℕ)) (count : ℕ) : ProbComp (Option (List W) × ℕ) := do
  let i ← sample n
  let z := table[(i : ℕ)]?.getD (none, 0)
  match z.1 with
  | none => pure (none, count + z.2)
  | some w =>
      (fun t : List W × ℕ =>
        (if t.1.length = r then some (w :: t.1) else none, t.2)) <$>
        (collectChildren (fun n => StateT.lift (sample n)) tableChild r
          (table.eraseIdx i)).run (count + z.2)

private theorem thresholdChildren_run_step {C W : Type}
    (sample : (n : ℕ) → ProbComp (Fin (n + 1)))
    (child : C → StateT ℕ ProbComp (Option W)) (r : ℕ) (pool : List C)
    (n : ℕ) (hlen : pool.length = n + 1) (count : ℕ) :
    (thresholdChildren (fun n => StateT.lift (sample n)) child (r + 1) pool).run count =
      (do
        let i ← sample n
        let z ← (child (pool[(i : ℕ)]'(by omega))).run count
        match z.1 with
        | none => pure (none, z.2)
        | some w =>
            (fun t : List W × ℕ =>
              (if t.1.length = r then some (w :: t.1) else none, t.2)) <$>
              (collectChildren (fun n => StateT.lift (sample n)) child r
                (pool.eraseIdx i)).run z.2) := by
  cases pool with
  | nil => simp at hlen
  | cons c cs =>
      have hn : n = cs.length := by simpa using hlen.symm
      subst n
      simp only [thresholdChildren, StateT.run_bind, StateT.run_lift,
        bind_assoc, pure_bind]
      congr 1
      funext i
      congr 1
      funext z
      cases z.1 with
      | none => rfl
      | some w =>
          rw [StateT.run_bind]
          simp only [StateT.run_pure, bind_pure_comp]

private theorem threshold_table_step {W : Type}
    (sample : (n : ℕ) → ProbComp (Fin (n + 1))) (r : ℕ)
    (table : List (Option W × ℕ)) (n : ℕ) (hlen : table.length = n + 1) (count : ℕ) :
    (thresholdChildren (fun n => StateT.lift (sample n)) tableChild (r + 1) table).run count =
      thresholdTableStep sample r n table count := by
  rw [thresholdChildren_run_step sample tableChild r table n hlen count]
  simp only [tableChild, StateT.run_mk, pure_bind, thresholdTableStep]
  congr 1
  funext i
  rw [List.getElem?_eq_getElem (by omega)]
  rfl

/-- A threshold attempt has the same joint output and accumulated child cost law when all
independent child results are sampled first and their stored costs are charged upon selection. -/
theorem thresholdChildren_eager {C W : Type}
    (sample : (n : ℕ) → ProbComp (Fin (n + 1)))
    (child : C → ProbComp (Option W × ℕ)) (k : ℕ) (pool : List C) (count : ℕ) :
    (thresholdChildren (fun n => StateT.lift (sample n)) (chargedChild child) k pool).run count =ᵈ
      (do let table ← pool.mapM child
          (thresholdChildren (fun n => StateT.lift (sample n)) tableChild k table).run count) := by
  cases k with
  | zero =>
      simp only [thresholdChildren, StateT.run_pure]
      exact (OracleComp.EvalDistEq.bind_const (pool.mapM child)
        (pure (some [], count))).symm
  | succ r =>
      cases pool with
      | nil => simp [thresholdChildren]
      | cons c cs =>
          let n := cs.length
          have hp : (c :: cs).length = n + 1 := rfl
          have hright :
              (do let table ← (c :: cs).mapM child
                  (thresholdChildren (fun n => StateT.lift (sample n)) tableChild
                    (r + 1) table).run count) =ᵈ
              (do let table ← (c :: cs).mapM child
                  thresholdTableStep sample r n table count) := by
            apply OracleComp.EvalDistEq.bind_congr_of_support
            intro table ht
            rw [threshold_table_step sample r table n
              ((List.length_of_mem_support_mapM child (c :: cs) table ht).trans hp)]
          rw [thresholdChildren_run_step sample (chargedChild child) r (c :: cs) n hp count]
          simp only [chargedChild, StateT.run_mk, bind_map_left]
          refine EvalDistEq.trans ?_ hright.symm
          have hswap := OracleComp.EvalDistEq.bind_bind_swap ((c :: cs).mapM child) (sample n)
            (fun table i =>
              let z := table[(i : ℕ)]?.getD (none, 0)
              match z.1 with
              | none => pure (none, count + z.2)
              | some w =>
                  (fun t : List W × ℕ =>
                    (if t.1.length = r then some (w :: t.1) else none, t.2)) <$>
                    (collectChildren (fun n => StateT.lift (sample n)) tableChild r
                      (table.eraseIdx i)).run (count + z.2))
          refine EvalDistEq.trans ?_ hswap.symm
          apply EvalDistEq.bind_right
          intro i
          have hi : (i : ℕ) < (c :: cs).length := by omega
          refine EvalDistEq.trans ?_
            (mapM_bind_eraseIdx child (c :: cs) i hi (none, 0)
              (fun z xs =>
                match z.1 with
                | none => pure (none, count + z.2)
                | some w =>
                    (fun t : List W × ℕ =>
                      (if t.1.length = r then some (w :: t.1) else none, t.2)) <$>
                      (collectChildren (fun n => StateT.lift (sample n)) tableChild r
                        xs).run (count + z.2)))
          apply EvalDistEq.bind_right
          intro z
          have hlen : ((c :: cs).eraseIdx i).length = n := by
            rw [List.length_eraseIdx_of_lt hi, hp]
            omega
          cases hz : z.1 with
          | none =>
              exact (OracleComp.EvalDistEq.bind_const
                (((c :: cs).eraseIdx i).mapM child) (pure (none, count + z.2))).symm
          | some w =>
              simpa only [hz, map_bind] using
                (collectChildren_eager sample child n r ((c :: cs).eraseIdx i) hlen
                  (count + z.2)).map (fun t : List W × ℕ =>
                    (if t.1.length = r then some (w :: t.1) else none, t.2))

/-- Reading a deterministic child table records precisely the successful draws and the sum
of the costs of all selected entries, including unsuccessful ones. -/
theorem collectChildren_table {W : Type} (n : ℕ) :
    ∀ (r : ℕ) (pool : List (Option W × ℕ)), pool.length = n → ∀ count : ℕ,
    (collectChildren (fun n => StateT.lift (ProbComp.uniformFin n)) tableChild r pool).run count =
      (fun d => (d.filterMap Prod.fst, count + (d.map Prod.snd).sum)) <$>
        ProbComp.drawUntil (fun z : Option W × ℕ => z.1.isSome) r pool := by
  induction n with
  | zero =>
      intro r pool hp count
      obtain rfl := List.length_eq_zero_iff.mp hp
      simp
  | succ n ih =>
      intro r pool hp count
      cases r with
      | zero => simp
      | succ r =>
          cases pool with
          | nil => simp
          | cons z zs =>
              rw [collectChildren_run_step _ tableChild r (z :: zs) zs.length rfl count,
                ProbComp.drawUntil_cons]
              simp only [tableChild, StateT.run_mk, pure_bind, map_bind]
              congr 1
              funext i
              have hi : (i : ℕ) < (z :: zs).length := by simpa using i.isLt
              have hlen : ((z :: zs).eraseIdx i).length = n := by
                rw [List.length_eraseIdx_of_lt hi]
                omega
              cases hacc : ((z :: zs)[(i : ℕ)]).1 with
              | none =>
                  simp only [Option.isSome_none, Bool.false_eq_true, ite_false]
                  rw [ih _ _ hlen]
                  simp [Functor.map_map, hacc, Nat.add_assoc]
              | some w =>
                  simp only [Option.isSome_some, ite_true]
                  rw [ih _ _ hlen]
                  simp [Functor.map_map, hacc, Nat.add_assoc]

/-- The positive-threshold attempt on a deterministic table charges the first draw and then,
only if it succeeded, the without-replacement draws needed for the remaining successful children. -/
theorem thresholdChildren_table {W : Type} (r : ℕ) (z : Option W × ℕ)
    (zs : List (Option W × ℕ)) (count : ℕ) :
    (thresholdChildren (fun n => StateT.lift (ProbComp.uniformFin n)) tableChild
      (r + 1) (z :: zs)).run count =
      (do
        let i ← ProbComp.uniformFin zs.length
        let y := (z :: zs)[(i : ℕ)]'(by simpa using i.isLt)
        match y.1 with
        | none => pure (none, count + y.2)
        | some w =>
            (fun d : List (Option W × ℕ) =>
              (if (d.filterMap Prod.fst).length = r then some (w :: d.filterMap Prod.fst)
                else none, count + y.2 + (d.map Prod.snd).sum)) <$>
              ProbComp.drawUntil (fun z : Option W × ℕ => z.1.isSome) r
                ((z :: zs).eraseIdx i)) := by
  rw [thresholdChildren_run_step _ tableChild r (z :: zs) zs.length rfl count]
  simp only [tableChild, StateT.run_mk, pure_bind]
  congr 1
  funext i
  cases h : ((z :: zs)[(i : ℕ)]).1 with
  | none => rfl
  | some w =>
      rw [collectChildren_table _ _ _ rfl]
      simp only [Functor.map_map]

/-- A deterministic child table is evaluated by the threshold drawing procedure, retaining
successful witnesses and charging the sum of all inspected entry costs. -/
theorem thresholdChildren_table_draws {W : Type} (k : ℕ)
    (pool : List (Option W × ℕ)) (count : ℕ) :
    (thresholdChildren (fun n => StateT.lift (ProbComp.uniformFin n)) tableChild k pool).run count =
      (fun d : List (Option W × ℕ) =>
        (if (d.filterMap Prod.fst).length = k then some (d.filterMap Prod.fst) else none,
          count + (d.map Prod.snd).sum)) <$>
        ProbComp.thresholdDraws (fun z : Option W × ℕ => z.1.isSome) k pool := by
  cases k with
  | zero => simp [thresholdChildren]
  | succ r =>
      cases pool with
      | nil => simp [thresholdChildren]
      | cons z zs =>
          rw [thresholdChildren_table, ProbComp.thresholdDraws_cons, map_bind]
          congr 1
          funext i
          cases h : ((z :: zs)[(i : ℕ)]).1 with
          | none => simp [h]
          | some w =>
              simp [h, Functor.map_map, Nat.add_assoc]

end Rewinding
