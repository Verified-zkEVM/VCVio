/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import ToMathlib.Data.List.Count
public import VCVio.CryptoFoundations.Rewinding.Finder
public import VCVio.OracleComp.Constructions.WithoutReplacement

/-!
# Threshold extraction in one round

A threshold attempt samples its first child uniformly and stops immediately when that child
fails. After a successful first child it samples without replacement until it has enough
successful children or the challenge pool is exhausted.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace Rewinding

variable {C W : Type} {m : Type → Type} [Monad m]

/-- Collect `r` successful children, sampling their challenges without replacement. The returned
list contains every successful child encountered, including when the pool is exhausted. -/
@[expose] def collectChildren (sample : (n : ℕ) → m (Fin (n + 1)))
    (child : C → m (Option W)) : ℕ → List C → m (List W)
  | 0, _ => pure []
  | _ + 1, [] => pure []
  | r + 1, c :: cs => do
      let i ← sample cs.length
      let w ← child ((c :: cs)[(i : ℕ)]'(by simpa using i.isLt))
      match w with
      | none => collectChildren sample child (r + 1) ((c :: cs).eraseIdx i)
      | some w => (w :: ·) <$> collectChildren sample child r ((c :: cs).eraseIdx i)
  termination_by _ l => l.length
  decreasing_by
    all_goals
      have hi : (i : ℕ) < (c :: cs).length := by simpa using i.isLt
      rw [List.length_eraseIdx_of_lt hi]
      simp only [List.length_cons] at hi ⊢
      omega

/-- A threshold attempt aborts after an unsuccessful first child. Otherwise it collects the
remaining successful children without replacement and returns them only when all are found. -/
@[expose] def thresholdChildren (sample : (n : ℕ) → m (Fin (n + 1)))
    (child : C → m (Option W)) (k : ℕ) (pool : List C) : m (Option (List W)) := do
  match k, pool with
  | 0, _ => pure (some [])
  | _ + 1, [] => pure none
  | r + 1, c :: cs =>
      let i ← sample cs.length
      let w ← child ((c :: cs)[(i : ℕ)]'(by simpa using i.isLt))
      match w with
      | none => pure none
      | some w =>
          let ws ← collectChildren sample child r ((c :: cs).eraseIdx i)
          pure (if ws.length = r then some (w :: ws) else none)

/-- A Boolean oracle child returns its challenge exactly when the oracle accepts it. -/
@[expose] def acceptanceChild (c : C) :
    OracleComp (unifSpec + rerunSpec C Bool) (Option C) := do
  let b ← (rerunSpec C Bool).query c
  pure (if b then some c else none)

/-- The computable one-round threshold finder, with a finite list of distinct challenges. -/
@[expose] def thresholdRound (k : ℕ) (pool : List C) :
    OracleComp (unifSpec + rerunSpec C Bool) (Option (List C)) :=
  thresholdChildren (fun n => (unifSpec.query n)) acceptanceChild k pool

@[simp] theorem collectChildren_zero (sample : (n : ℕ) → m (Fin (n + 1)))
    (child : C → m (Option W)) (pool : List C) :
    collectChildren sample child 0 pool = pure [] := by rw [collectChildren]

@[simp] theorem collectChildren_nil (sample : (n : ℕ) → m (Fin (n + 1)))
    (child : C → m (Option W)) (r : ℕ) :
    collectChildren sample child r [] = pure [] := by cases r <;> rw [collectChildren]

theorem collectChildren_cons (sample : (n : ℕ) → m (Fin (n + 1)))
    (child : C → m (Option W)) (r : ℕ) (c : C) (cs : List C) :
    collectChildren sample child (r + 1) (c :: cs) = (do
      let i ← sample cs.length
      let w ← child ((c :: cs)[(i : ℕ)]'(by simpa using i.isLt))
      match w with
      | none => collectChildren sample child (r + 1) ((c :: cs).eraseIdx i)
      | some w => (w :: ·) <$> collectChildren sample child r ((c :: cs).eraseIdx i)) := by
  rw [collectChildren]

section Support

variable {ι : Type} {spec : OracleSpec ι}

/-- At most the requested number of successful children is returned. -/
theorem length_collectChildren_le
    (sample : (n : ℕ) → OracleComp spec (Fin (n + 1)))
    (child : C → OracleComp spec (Option W)) (n : ℕ) :
    ∀ (r : ℕ) (pool : List C), pool.length = n →
      ∀ ws ∈ support (collectChildren sample child r pool), ws.length ≤ r := by
  induction n with
  | zero =>
      intro r pool hp ws hw
      obtain rfl := List.length_eq_zero_iff.mp hp
      simp only [collectChildren_nil, support_pure, Set.mem_singleton_iff] at hw
      subst ws
      exact Nat.zero_le _
  | succ n ih =>
      intro r pool hp ws hw
      cases r with
      | zero => simpa using hw
      | succ r =>
          cases pool with
          | nil => simp at hp
          | cons c cs =>
              rw [collectChildren_cons, mem_support_bind_iff] at hw
              obtain ⟨i, -, hw⟩ := hw
              rw [mem_support_bind_iff] at hw
              obtain ⟨w, -, hw⟩ := hw
              have hi : (i : ℕ) < (c :: cs).length := by simpa using i.isLt
              have hlen : ((c :: cs).eraseIdx i).length = n := by
                rw [List.length_eraseIdx_of_lt hi]; omega
              cases w with
              | none => exact ih _ _ hlen ws hw
              | some w =>
                  rw [support_map] at hw
                  obtain ⟨tail, ht, rfl⟩ := hw
                  simp only [List.length_cons]
                  exact Nat.succ_le_succ (ih _ _ hlen tail ht)

/-- A successful threshold attempt returns exactly the requested number of children. -/
theorem length_of_mem_support_thresholdChildren
    (sample : (n : ℕ) → OracleComp spec (Fin (n + 1)))
    (child : C → OracleComp spec (Option W)) (k : ℕ) (pool : List C)
    (ws : List W) (hw : some ws ∈ support (thresholdChildren sample child k pool)) :
    ws.length = k := by
  cases k with
  | zero => simpa [thresholdChildren] using hw
  | succ r =>
      cases pool with
      | nil => simp [thresholdChildren] at hw
      | cons c cs =>
          simp only [thresholdChildren, mem_support_bind_iff] at hw
          obtain ⟨i, -, w, -, hw⟩ := hw
          cases w with
          | none => simp at hw
          | some w =>
              dsimp only at hw
              rw [mem_support_bind_iff] at hw
              obtain ⟨tail, -, hw⟩ := hw
              split at hw
              next h =>
                simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at hw
                subst ws
                simpa using h
              next h => simp at hw

/-- Distinct challenges give distinct keys, and every returned witness satisfies the child's
soundness predicate. -/
theorem sound_collectChildren
    (sample : (n : ℕ) → OracleComp spec (Fin (n + 1)))
    (child : C → OracleComp spec (Option W)) (key : W → C) (P : W → Prop)
    (hchild : ∀ c w, some w ∈ support (child c) → key w = c ∧ P w) (n : ℕ) :
    ∀ (r : ℕ) (pool : List C), pool.length = n → pool.Nodup →
      ∀ ws ∈ support (collectChildren sample child r pool),
        (ws.map key).Nodup ∧ ∀ w ∈ ws, key w ∈ pool ∧ P w := by
  induction n with
  | zero =>
      intro r pool hp hn ws hw
      obtain rfl := List.length_eq_zero_iff.mp hp
      simp only [collectChildren_nil, support_pure, Set.mem_singleton_iff] at hw
      subst ws
      simp
  | succ n ih =>
      intro r pool hp hn ws hw
      cases r with
      | zero =>
          simp only [collectChildren_zero, support_pure, Set.mem_singleton_iff] at hw
          subst ws
          simp
      | succ r =>
          cases pool with
          | nil => simp at hp
          | cons c cs =>
              rw [collectChildren_cons, mem_support_bind_iff] at hw
              obtain ⟨i, -, hw⟩ := hw
              rw [mem_support_bind_iff] at hw
              obtain ⟨w, hc, hw⟩ := hw
              have hi : (i : ℕ) < (c :: cs).length := by simpa using i.isLt
              have hlen : ((c :: cs).eraseIdx i).length = n := by
                rw [List.length_eraseIdx_of_lt hi]; omega
              cases w with
              | none =>
                  obtain ⟨hnd, hmem⟩ := ih _ _ hlen (hn.eraseIdx i) ws hw
                  exact ⟨hnd, fun w hw => ⟨List.mem_of_mem_eraseIdx (hmem w hw).1,
                    (hmem w hw).2⟩⟩
              | some w =>
                  rw [support_map] at hw
                  obtain ⟨tail, ht, rfl⟩ := hw
                  obtain ⟨hnd, hmem⟩ := ih _ _ hlen (hn.eraseIdx i) tail ht
                  obtain ⟨hkey, hP⟩ := hchild _ _ hc
                  constructor
                  · simp only [List.map_cons, List.nodup_cons]
                    refine ⟨?_, hnd⟩
                    intro hm
                    obtain ⟨v, hv, heq⟩ := List.mem_map.mp hm
                    have hh := (hmem v hv).1
                    rw [heq, hkey] at hh
                    exact List.getElem_notMem_eraseIdx hn hi hh
                  · intro v hv
                    rcases List.mem_cons.mp hv with rfl | hv
                    · exact ⟨hkey ▸ List.getElem_mem hi, hP⟩
                    · exact ⟨List.mem_of_mem_eraseIdx (hmem v hv).1, (hmem v hv).2⟩

/-- Every successful threshold attempt has distinct challenge keys and sound child witnesses. -/
theorem sound_thresholdChildren
    (sample : (n : ℕ) → OracleComp spec (Fin (n + 1)))
    (child : C → OracleComp spec (Option W)) (key : W → C) (P : W → Prop)
    (hchild : ∀ c w, some w ∈ support (child c) → key w = c ∧ P w)
    (k : ℕ) (pool : List C) (hn : pool.Nodup)
    (ws : List W) (hw : some ws ∈ support (thresholdChildren sample child k pool)) :
    (ws.map key).Nodup ∧ ∀ w ∈ ws, key w ∈ pool ∧ P w := by
  cases k with
  | zero =>
      simp only [thresholdChildren, support_pure, Set.mem_singleton_iff, Option.some.injEq] at hw
      subst ws
      simp
  | succ r =>
      cases pool with
      | nil => simp [thresholdChildren] at hw
      | cons c cs =>
          simp only [thresholdChildren, mem_support_bind_iff] at hw
          obtain ⟨i, -, w, hc, hw⟩ := hw
          cases w with
          | none => simp at hw
          | some w =>
              dsimp only at hw
              rw [mem_support_bind_iff] at hw
              obtain ⟨tail, ht, hw⟩ := hw
              split at hw
              next h =>
                simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at hw
                subst ws
                have hi : (i : ℕ) < (c :: cs).length := by simpa using i.isLt
                obtain ⟨hnd, hmem⟩ := sound_collectChildren sample child key P hchild
                  _ r _ rfl (hn.eraseIdx i) tail ht
                obtain ⟨hkey, hP⟩ := hchild _ _ hc
                constructor
                · simp only [List.map_cons, List.nodup_cons]
                  refine ⟨?_, hnd⟩
                  intro hm
                  obtain ⟨v, hv, heq⟩ := List.mem_map.mp hm
                  have hh := (hmem v hv).1
                  rw [heq, hkey] at hh
                  exact List.getElem_notMem_eraseIdx hn hi hh
                · intro v hv
                  rcases List.mem_cons.mp hv with rfl | hv
                  · exact ⟨hkey ▸ List.getElem_mem hi, hP⟩
                  · exact ⟨List.mem_of_mem_eraseIdx (hmem v hv).1, (hmem v hv).2⟩
              next h => simp at hw

end Support

/-- Against a fixed Boolean table, collecting children returns exactly the accepting draws,
and its run counter is the number of draws made, including rejected draws. -/
theorem collectChildren_counted (f : C → Bool) (n : ℕ) :
    ∀ (r : ℕ) (pool : List C), pool.length = n → ∀ count : ℕ,
    (simulateQ (coins (S := ℕ) + counted f)
      (collectChildren (fun n => (unifSpec.query n)) acceptanceChild r pool)).run count =
      (fun d => (d.filter f, count + d.length)) <$> ProbComp.drawUntil f r pool := by
  induction n with
  | zero =>
      intro r pool hp count
      obtain rfl := List.length_eq_zero_iff.mp hp
      simp
  | succ n ih =>
      simp only [coins] at ih
      intro r pool hp count
      cases r with
      | zero => simp
      | succ r =>
          cases pool with
          | nil => simp
          | cons c cs =>
              rw [collectChildren_cons, ProbComp.drawUntil_cons]
              simp only [simulateQ_bind, StateT.run_bind, map_bind]
              simp only [QueryImpl.simulateQ_add_liftM_query_left, coins,
                QueryImpl.liftTarget_apply_run, QueryImpl.ofLift_apply, bind_map_left]
              simp only [acceptanceChild, simulateQ_bind, simulateQ_pure,
                QueryImpl.simulateQ_add_liftM_query_right, counted]
              simp only [StateT.run_bind, StateT.run_pure, StateT.run_modify,
                pure_bind]
              congr 1
              funext i
              have hi : (i : ℕ) < (c :: cs).length := by simpa using i.isLt
              have hlen : ((c :: cs).eraseIdx i).length = n := by
                rw [List.length_eraseIdx_of_lt hi]; omega
              cases hacc : f ((c :: cs)[(i : ℕ)]) with
              | false =>
                  simp only [Bool.false_eq_true, ite_false]
                  rw [ih _ _ hlen]
                  simp [Functor.map_map, hacc,
                    Nat.add_comm, Nat.add_left_comm]
              | true =>
                  simp only [ite_true]
                  rw [simulateQ_map, StateT.run_map, ih _ _ hlen]
                  simp [Functor.map_map, hacc,
                    Nat.add_comm, Nat.add_left_comm]

/-- The counted law of a positive threshold attempt on a nonempty challenge pool. -/
theorem thresholdRound_counted (f : C → Bool) (r : ℕ) (c : C) (cs : List C)
    (count : ℕ) :
    (simulateQ (coins (S := ℕ) + counted f) (thresholdRound (r + 1) (c :: cs))).run count =
      (do
        let i ← ProbComp.uniformFin cs.length
        let y := (c :: cs)[(i : ℕ)]'(by simpa using i.isLt)
        if f y then
          (fun d : List C => (if (d.filter f).length = r then some (y :: d.filter f) else none,
            count + 1 + d.length)) <$>
              ProbComp.drawUntil f r ((c :: cs).eraseIdx i)
        else pure (none, count + 1)) := by
  have hcol := collectChildren_counted f
  simp only [coins] at hcol
  simp only [thresholdRound, thresholdChildren, simulateQ_bind, StateT.run_bind,
    QueryImpl.simulateQ_add_liftM_query_left, coins, QueryImpl.liftTarget_apply_run,
    QueryImpl.ofLift_apply, bind_map_left, acceptanceChild, simulateQ_pure,
    QueryImpl.simulateQ_add_liftM_query_right, counted, StateT.run_modify,
    StateT.run_pure, pure_bind]
  congr 1
  funext i
  cases hacc : f ((c :: cs)[(i : ℕ)]) with
  | false => simp
  | true =>
      simp only [ite_true, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
      rw [hcol _ _ _ rfl]
      simp only [bind_pure_comp, Functor.map_map]

private theorem sum_acceptIndicators (f : C → Bool) (pool : List C) :
    (∑ i : Fin pool.length, if f pool[(i : ℕ)] then (1 : ℝ≥0∞) else 0) = pool.countP f := by
  exact_mod_cast List.countP_eq_sum_fin_ite pool f

/-- The acceptance probability of one uniform challenge in a nonempty pool. -/
theorem prEvent_uniformPool (f : C → Bool) (c : C) (cs : List C) :
    Pr{let i ← ProbComp.uniformFin cs.length}[f (c :: cs)[(i : ℕ)] = true] =
      ((c :: cs).countP f : ℝ≥0∞) / (cs.length + 1) := by
  rw [prEvent_eq_evalDist_of_discrete]
  rw [← MeasureTheory.lintegral_indicator_one
    (s := {i : Fin (cs.length + 1) | f (c :: cs)[(i : ℕ)] = true}) (by measurability)]
  rw [ProbComp.lintegral_evalDist_uniformFin]
  congr 1
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
  convert sum_acceptIndicators f (c :: cs) using 1

/-- Without-replacement collection reaches its target precisely when enough accepting
challenges occur in the pool. -/
theorem prEvent_drawUntil_enough (f : C → Bool) (r : ℕ) (pool : List C) :
    Pr{let d ← ProbComp.drawUntil f r pool}[(d.filter f).length = r] =
      if r ≤ pool.countP f then 1 else 0 := by
  calc
    _ = Pr{let _ ← ProbComp.drawUntil f r pool}[r ≤ pool.countP f] := by
      apply prEvent_congr_of_support
      intro d hd
      have hc := ProbComp.countP_of_mem_support_drawUntil f pool.length r pool rfl d hd
      rw [← List.countP_eq_length_filter]
      omega
    _ = _ := by by_cases h : r ≤ pool.countP f <;> simp [h]

/-- Exact success probability of a one-round threshold attempt. -/
theorem prEvent_thresholdRound (f : C → Bool) (r : ℕ) (c : C) (cs : List C) :
    Pr{let z ← (simulateQ (coins (S := ℕ) + counted f)
      (thresholdRound (r + 1) (c :: cs))).run 0}[z.1.isSome] =
      if r + 1 ≤ (c :: cs).countP f then
        ((c :: cs).countP f : ℝ≥0∞) / (cs.length + 1) else 0 := by
  rw [thresholdRound_counted]
  have hh :
      Pr{let z ← (do
        let i ← ProbComp.uniformFin cs.length
        let y := (c :: cs)[(i : ℕ)]'(by simpa using i.isLt)
        if f y then
          (fun d : List C => (if (d.filter f).length = r then some (y :: d.filter f) else none,
            0 + 1 + d.length)) <$>
              ProbComp.drawUntil f r ((c :: cs).eraseIdx i)
        else pure (none, 0 + 1))}[z.1.isSome] =
      Pr{let i ← ProbComp.uniformFin cs.length}[
        f (c :: cs)[(i : ℕ)] = true ∧ r + 1 ≤ (c :: cs).countP f] := by
    apply prEvent_bind_congr _ _ (fun i => pure i)
    intro i
    have hi : (i : ℕ) < (c :: cs).length := by simpa using i.isLt
    cases hacc : f (c :: cs)[(i : ℕ)] with
    | false => simp [hacc]
    | true =>
        simp only [ite_true, prEvent_map, prEvent_pure, hacc, true_and]
        have hc := List.countP_eraseIdx_of_pos hi hacc
        rw [show (Pr{let d ← ProbComp.drawUntil f r ((c :: cs).eraseIdx i)}[
          (if (d.filter f).length = r then some ((c :: cs)[(i : ℕ)] :: d.filter f)
            else none).isSome]) =
          Pr{let d ← ProbComp.drawUntil f r ((c :: cs).eraseIdx i)}[
            (d.filter f).length = r] from by
              apply prEvent_congr
              intro d
              split <;> simp_all]
        rw [prEvent_drawUntil_enough]
        congr 1
        exact propext (by omega)
  rw [hh]
  by_cases hk : r + 1 ≤ (c :: cs).countP f
  · simpa only [hk, and_true, ite_true] using prEvent_uniformPool f c cs
  · simp [hk]

private theorem expectedCalls_drawUntil {B : Type} (out : List C → B)
    (f : C → Bool) (r : ℕ) (pool : List C) :
    expectedCalls ((fun d => (out d, 1 + d.length)) <$> ProbComp.drawUntil f r pool) =
      NegHypergeom.expectedDraws pool.length (pool.countP f) r + 1 := by
  rw [expectedCalls, AddWriterT.expectedCostNat, AddWriterT.expectedCost,
    AddWriterT.costs_def]
  simp only [WriterT.run_mk, Functor.map_map]
  have h := ProbComp.lintegral_evalDist_length_cons_map ()
    ((fun d => d.map (fun _ => ())) <$> ProbComp.drawUntil f r pool)
  simp only [Functor.map_map, List.length_map, List.length_cons] at h
  simp only [toAdd_ofAdd, Nat.add_comm 1]
  rw [h]
  simpa only [Functor.map_map, List.length_map] using
    congrArg (· + 1) (ProbComp.lintegral_evalDist_length_drawUntil f pool.length r pool rfl)

/-- A one-round threshold attempt succeeds with probability at least the acceptance rate minus
`(k - 1)/N`. The estimate holds for every Boolean oracle table. -/
theorem thresholdRound_success (f : C → Bool) (r : ℕ) (c : C) (cs : List C) :
    ((c :: cs).countP f : ℝ≥0∞) / (cs.length + 1) -
        (r : ℝ≥0∞) / (cs.length + 1) ≤
      Pr{let z ← (simulateQ (coins (S := ℕ) + counted f)
        (thresholdRound (r + 1) (c :: cs))).run 0}[z.1.isSome] := by
  rw [prEvent_thresholdRound]
  split
  · exact tsub_le_self
  next h =>
    have hm : (c :: cs).countP f ≤ r := by omega
    have hle : ((c :: cs).countP f : ℝ≥0∞) / (cs.length + 1) ≤
        (r : ℝ≥0∞) / (cs.length + 1) := by gcongr
    rw [tsub_eq_zero_of_le hle]

/-- The unconditional expected number of calls in one threshold attempt, including unsuccessful
attempts, is at most the requested threshold. -/
theorem expectedCalls_thresholdRound (f : C → Bool) (r : ℕ) (c : C) (cs : List C) :
    expectedCalls ((simulateQ (coins (S := ℕ) + counted f)
      (thresholdRound (r + 1) (c :: cs))).run 0) ≤ r + 1 := by
  rw [thresholdRound_counted, expectedCalls_bind]
  let M := (c :: cs).countP f
  let E := NegHypergeom.expectedDraws cs.length (M - 1) r
  have hstep : ∀ i : Fin (cs.length + 1),
      expectedCalls (if f (c :: cs)[(i : ℕ)] then
          (fun d : List C =>
            (if (d.filter f).length = r then some ((c :: cs)[(i : ℕ)] :: d.filter f)
              else none, 0 + 1 + d.length)) <$>
                ProbComp.drawUntil f r ((c :: cs).eraseIdx i)
        else pure (none, 0 + 1)) =
        1 + if f (c :: cs)[(i : ℕ)] then E else 0 := by
    intro i
    have hi : (i : ℕ) < (c :: cs).length := by simpa using i.isLt
    by_cases hacc : f (c :: cs)[(i : ℕ)] = true
    · simp only [hacc, ite_true, zero_add]
      rw [expectedCalls_drawUntil]
      have hlen : ((c :: cs).eraseIdx i).length = cs.length := by
        rw [List.length_eraseIdx_of_lt hi]; simp
      have hcount : ((c :: cs).eraseIdx i).countP f = M - 1 := by
        have hc := List.countP_eraseIdx_of_pos hi hacc
        dsimp only [M]
        omega
      rw [hlen, hcount]
      exact add_comm _ _
    · simp only [hacc]
      rw [expectedCalls, AddWriterT.expectedCostNat, AddWriterT.expectedCost,
        AddWriterT.costs_def]
      simp
  simp only [hstep]
  rw [ProbComp.lintegral_evalDist_uniformFin]
  have hsum : (∑ i : Fin (cs.length + 1),
      if f (c :: cs)[(i : ℕ)] then E else 0) = (M : ℝ≥0∞) * E := by
    calc
      _ = ∑ i : Fin (cs.length + 1),
          (if f (c :: cs)[(i : ℕ)] then (1 : ℝ≥0∞) else 0) * E := by
        apply Finset.sum_congr rfl
        intro i _
        split <;> simp
      _ = (∑ i : Fin (cs.length + 1),
          if f (c :: cs)[(i : ℕ)] then (1 : ℝ≥0∞) else 0) * E :=
        (Finset.sum_mul ..).symm
      _ = _ := by
        convert congrArg (· * E) (sum_acceptIndicators f (c :: cs)) using 1
  rw [Finset.sum_add_distrib, hsum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hN0 : (cs.length : ℝ≥0∞) + 1 ≠ 0 := by positivity
  have hNtop : (cs.length : ℝ≥0∞) + 1 ≠ ⊤ := by finiteness
  simp only [Nat.cast_add, Nat.cast_one]
  rw [ENNReal.add_div, ENNReal.div_self hN0 hNtop, add_comm (r : ℝ≥0∞) 1]
  apply add_le_add_right
  by_cases hM : M = 0
  · simp [hM]
  · have hM0 : 0 < M := Nat.pos_of_ne_zero hM
    have hMle : M ≤ cs.length + 1 := by
      simpa [M] using (List.countP_le_length (p := f) (l := c :: cs))
    have hE : E ≤ (r : ℝ≥0∞) * (cs.length + 1) / M := by
      have h := NegHypergeom.expectedDraws_resample_le (N := cs.length + 1)
        (l := M) (r := r) hM0 hMle
      simpa only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, E] using h
    calc
      (M : ℝ≥0∞) * E / (cs.length + 1) ≤
          (M : ℝ≥0∞) * ((r : ℝ≥0∞) * (cs.length + 1) / M) / (cs.length + 1) := by gcongr
      _ = r := by
        have hM0' : (M : ℝ≥0∞) ≠ 0 := by exact_mod_cast hM
        have hMtop : (M : ℝ≥0∞) ≠ ⊤ := by finiteness
        rw [div_eq_mul_inv, div_eq_mul_inv]
        calc
          _ = (r : ℝ≥0∞) * ((M : ℝ≥0∞) * (M : ℝ≥0∞)⁻¹) *
              (((cs.length : ℝ≥0∞) + 1) * ((cs.length : ℝ≥0∞) + 1)⁻¹) := by ring
          _ = r := by rw [ENNReal.mul_inv_cancel hM0' hMtop,
            ENNReal.mul_inv_cancel hN0 hNtop, mul_one, mul_one]

/-- The strengthened one-round success estimate keeps the multiplicative factor needed when
threshold attempts are nested over several rounds. -/
theorem thresholdRound_success_scaled (f : C → Bool) (r : ℕ) (c : C) (cs : List C)
    (hr : r ≤ cs.length) :
    ((c :: cs).countP f : ℝ≥0∞) / (cs.length + 1) -
        (r : ℝ≥0∞) / (cs.length + 1) ≤
      (1 - (r : ℝ≥0∞) / (cs.length + 1)) *
        Pr{let z ← (simulateQ (coins (S := ℕ) + counted f)
          (thresholdRound (r + 1) (c :: cs))).run 0}[z.1.isSome] := by
  rw [prEvent_thresholdRound]
  split
  next hk =>
    let ε : ℝ≥0∞ := ((c :: cs).countP f : ℝ≥0∞) / (cs.length + 1)
    let a : ℝ≥0∞ := (r : ℝ≥0∞) / (cs.length + 1)
    have hN : (cs.length : ℝ≥0∞) + 1 ≠ 0 := by positivity
    have hNt : (cs.length : ℝ≥0∞) + 1 ≠ ⊤ := by finiteness
    have hε : ε ≤ 1 := by
      calc
        ε ≤ ((cs.length : ℝ≥0∞) + 1) / (cs.length + 1) := by
          dsimp only [ε]
          gcongr
          exact_mod_cast List.countP_le_length (p := f) (l := c :: cs)
        _ = 1 := ENNReal.div_self hN hNt
    have ha : a ≤ 1 := by
      calc
        a ≤ ((cs.length : ℝ≥0∞) + 1) / (cs.length + 1) := by
          dsimp only [a]
          gcongr
          exact_mod_cast (show r ≤ cs.length + 1 from by omega)
        _ = 1 := ENNReal.div_self hN hNt
    apply tsub_le_iff_right.mpr
    change ε ≤ (1 - a) * ε + a
    calc
      ε = ε * ((1 - a) + a) := by rw [tsub_add_cancel_of_le ha, mul_one]
      _ = (1 - a) * ε + ε * a := by ring
      _ ≤ (1 - a) * ε + a :=
        add_le_add le_rfl ((mul_le_mul' hε (le_refl a)).trans_eq (one_mul a))
  next hk =>
    have hm : (c :: cs).countP f ≤ r := by omega
    have hle : ((c :: cs).countP f : ℝ≥0∞) / (cs.length + 1) ≤
        (r : ℝ≥0∞) / (cs.length + 1) := by gcongr
    rw [tsub_eq_zero_of_le hle, mul_zero]

end Rewinding
