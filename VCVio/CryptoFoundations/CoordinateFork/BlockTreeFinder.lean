/-
Copyright (c) 2026 aryaethn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/
module

public import VCVio.CryptoFoundations.CoordinateFork.BlockChildren
public import VCVio.CryptoFoundations.Rewinding.BlockSemantics
public import VCVio.CryptoFoundations.Rewinding.ThresholdBounds

/-!
# The multi-round block finder

`OracleComp.blockTreeFinder n ι S k` is the tree finder for `n` rounds, each a block: round `r` has
coordinates `ι r`, an alphabet `S r i` and a threshold `k r i` at every coordinate, and challenge
`(i : ι r) → S r i`. Every round draws a uniform centre and runs the block step
`Rewinding.blockChildren`, with the finder on the later rounds as the child. The children of a node
are the centre and, at every coordinate `j`, `k r j - 1` neighbours of the centre that differ from
it at `j` alone, `∑ j, (k r j - 1) + 1 = blockArity (k r)` in all.

`OracleComp.isTreeFinder_blockTreeFinder` is its tree-finder contract:

* every returned tree has, at every node, pairwise distinct siblings that form a block star
  (`OracleComp.blockNodeOk`), and accepted leaves;
* when every round error `κ r = ∑ j, (k r j - 1) / |S r j|` is at most one, the acceptance rate `ε`
  and the success probability `p` satisfy `ε ≤ κ + (1 - κ) p` for
  `κ = 1 - ∏ r, (1 - κ r)` (`OracleComp.blockTreeError`);
* the expected number of acceptance-oracle calls is at most `∏ r, blockArity (k r)`.

The proof is an induction on rounds. One round of the counted finder is the block step with
probabilistic children (`OracleComp.runFinder_blockTreeFinder_succ`), whose success and cost
clauses are `OracleComp.prEvent_child_le_blockChildStep` and
`OracleComp.expectedCalls_blockChildStep_le`.

## References

* [Fenzi, G., Moghaddas, H., and Nguyen, N. K., *Lattice-Based Polynomial Commitments: Towards
    Asymptotic and Concrete Efficiency*](https://eprint.iacr.org/2023/846)
* Attema, Cramer and Kohl, *A compressed Σ-protocol theory for lattices*, CRYPTO 2021.
-/

public section

open OracleComp OracleSpec CoordinateWise Rewinding

open scoped ENNReal

namespace OracleComp

/-- The arity of a block round: the centre and `k j - 1` neighbours at every coordinate `j`. -/
@[expose] def blockArity {ι : Type} [Fintype ι] (k : ι → ℕ) : ℕ := ∑ j, (k j - 1) + 1

/-- The children of a successful block step in order: the centre's result, then the collected
results of every coordinate. -/
@[expose] noncomputable def blockChildList {ι : Type} [Fintype ι] {W : Type}
    (z : W × (ι → List W)) : List W :=
  z.1 :: (Finset.univ : Finset ι).toList.flatMap z.2

/-- The child list of a successful block step has the arity of the round. -/
theorem length_blockChildList {ι : Type} [Fintype ι] {W : Type} (k : ι → ℕ)
    (w : W × (ι → List W)) (h : ∀ j, (w.2 j).length = k j - 1) :
    (blockChildList w).length = blockArity k := by
  rw [blockChildList, List.length_cons, List.length_flatMap, blockArity, Finset.sum_map_toList]
  simp only [h]

/-- **The root of a successful block step is a block star.** If the centre's result has key `c₀`,
and every coordinate `j` returned `k j - 1` results with distinct keys from the neighbour pool of
`c₀` at `j`, the keys of the child list are pairwise distinct and form a block star. -/
theorem blockChildList_keys {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] {T : Type} (k : ι → ℕ)
    (c₀ : (i : ι) → S i) (w₀ : ((i : ι) → S i) × T) (ws : ι → List (((i : ι) → S i) × T))
    (h0 : w₀.1 = c₀)
    (hws : ∀ j, ((ws j).map Prod.fst).Nodup ∧ ∀ w ∈ ws j, w.1 ∈ neighbourPool c₀ j)
    (hlen : ∀ j, (ws j).length = k j - 1) :
    ((blockChildList (w₀, ws)).map Prod.fst).Nodup ∧
      IsBlockSpecialSound k ((blockChildList (w₀, ws)).map Prod.fst).toFinset := by
  classical
  have hmem : ∀ j, ∀ y ∈ (ws j).map Prod.fst, y ∈ neighbourPool c₀ j := fun j y hy => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hy
    exact (hws j).2 w hw
  have hmap : (blockChildList (w₀, ws)).map Prod.fst =
      c₀ :: (Finset.univ : Finset ι).toList.flatMap fun j => (ws j).map Prod.fst := by
    simp [blockChildList, List.map_flatMap, h0]
  rw [hmap]
  set N : ι → Finset ((i : ι) → S i) := fun j => ((ws j).map Prod.fst).toFinset
  have hN : ∀ j, ∀ y ∈ N j, Function.DiffersOnlyAt j c₀ y := fun j y hy =>
    differsOnlyAt_of_mem_neighbourPool (hmem j y (List.mem_toFinset.mp hy))
  have hcard : ∀ j, (N j).card = k j - 1 := fun j => by
    rw [List.toFinset_card_of_nodup (hws j).1, List.length_map, hlen j]
  refine ⟨List.nodup_cons.mpr ⟨?_, ?_⟩, ?_⟩
  · simp only [List.mem_flatMap, Finset.mem_toList, Finset.mem_univ, true_and, not_exists]
    intro j hj
    exact centre_notMem_neighbourPool c₀ j (hmem j c₀ hj)
  · refine List.nodup_flatMap.mpr ⟨fun j _ => (hws j).1, ?_⟩
    refine (Finset.nodup_toList _).pairwise_of_forall_ne fun j _ j' _ hne => ?_
    exact List.disjoint_left.mpr fun y hy hy' =>
      hne (eq_of_mem_neighbourPool (hmem j y hy) (hmem j' y hy'))
  · have hset :
        (c₀ :: (Finset.univ : Finset ι).toList.flatMap fun j => (ws j).map Prod.fst).toFinset =
          neighbourFamily c₀ N := by
      ext x
      simp [neighbourFamily, N, List.mem_flatMap]
    rw [hset]
    exact isBlockSpecialSound_neighbourFamily hN hcard

/-- **The multi-round block program.** Round `0` draws a centre with `centre 0` and runs the block
step with the program on the later rounds as the child; the centre's subtree and the collected
subtrees become the children of the root. -/
@[expose] noncomputable def blockTreeProgram {m : Type → Type} [Monad m]
    (sample : (j : ℕ) → m (Fin (j + 1))) :
    (n : ℕ) → (ι : Fin n → Type) → [∀ r, Fintype (ι r)] → [∀ r, DecidableEq (ι r)] →
    (S : (r : Fin n) → ι r → Type) → [∀ r i, Fintype (S r i)] → [∀ r i, DecidableEq (S r i)] →
    (k : (r : Fin n) → ι r → ℕ) → (centre : (r : Fin n) → m ((i : ι r) → S r i)) →
    (((r : Fin n) → (i : ι r) → S r i) → m Bool) →
    m (Option (VecTree (fun r => (i : ι r) → S r i) (fun r => blockArity (k r))))
  | 0, _, _, _, _, _, _, _, _, accept => do
      let b ← accept (fun r => Fin.elim0 r)
      pure (if b then some (VecTree.empty _ _) else none)
  | n + 1, ι, _, _, S, _, _, k, centre, accept => do
      let c₀ ← centre 0
      let z ← blockChildren sample
        (fun c => do
          let t ← blockTreeProgram sample n (fun r => ι r.succ) (fun r => S r.succ)
            (fun r => k r.succ) (fun r => centre r.succ) (fun q => accept (Fin.cons c q))
          pure (t.map fun t => (c, t)))
        (k 0) c₀ (neighbourPool c₀)
      pure (z.bind fun z => assembleChildren (blockChildList z))

/-- The multi-round block program commutes with monad morphisms. -/
theorem map_blockTreeProgram {m m' : Type → Type} [Monad m] [LawfulMonad m] [Monad m']
    [LawfulMonad m'] (φ : m →ᵐ m') (sample : (j : ℕ) → m (Fin (j + 1))) :
    ∀ (n : ℕ) (ι : Fin n → Type) [∀ r, Fintype (ι r)] [∀ r, DecidableEq (ι r)]
      (S : (r : Fin n) → ι r → Type) [∀ r i, Fintype (S r i)] [∀ r i, DecidableEq (S r i)]
      (k : (r : Fin n) → ι r → ℕ) (centre : (r : Fin n) → m ((i : ι r) → S r i))
      (accept : ((r : Fin n) → (i : ι r) → S r i) → m Bool),
      φ (blockTreeProgram sample n ι S k centre accept) =
        blockTreeProgram (fun j => φ (sample j)) n ι S k (fun r => φ (centre r))
          (fun q => φ (accept q))
  | 0, _, _, _, _, _, _, _, _, accept => by
      simp [blockTreeProgram]
  | n + 1, ι, _, _, S, _, _, k, centre, accept => by
      rw [blockTreeProgram, blockTreeProgram, φ.mmap_bind]
      congr 1
      funext c₀
      rw [φ.mmap_bind, map_blockChildren]
      refine congrArg₂ (· >>= ·) ?_ (funext fun z => φ.mmap_pure _)
      congr 1
      funext c
      rw [φ.mmap_bind, map_blockTreeProgram φ sample n]
      simp only [φ.mmap_pure]

/-- **The multi-round block finder.** Every round draws a uniform centre and runs the block step,
with the finder on the later rounds as the child. -/
@[expose] noncomputable def blockTreeFinder (n : ℕ) (ι : Fin n → Type) [∀ r, Fintype (ι r)]
    [∀ r, DecidableEq (ι r)] (S : (r : Fin n) → ι r → Type) [∀ r i, Fintype (S r i)]
    [∀ r i, DecidableEq (S r i)] [∀ r, SampleableType ((i : ι r) → S r i)]
    (k : (r : Fin n) → ι r → ℕ) :
    OracleComp (unifSpec + accSpec fun r => (i : ι r) → S r i)
      (Option (VecTree (fun r => (i : ι r) → S r i) (fun r => blockArity (k r)))) :=
  blockTreeProgram (fun j => liftM (unifSpec.query j)) n ι S k
    (fun r => OracleComp.liftComp ($ᵗ ((i : ι r) → S r i)) _)
    (fun q => liftM ((accSpec fun r => (i : ι r) → S r i).query q))

/-- Against a fixed acceptance function, the counted finder is the block program in the counter
monad, with uniform centres. -/
theorem simulateQ_counted_blockTreeFinder (n : ℕ) (ι : Fin n → Type) [∀ r, Fintype (ι r)]
    [∀ r, DecidableEq (ι r)] (S : (r : Fin n) → ι r → Type) [∀ r i, Fintype (S r i)]
    [∀ r i, DecidableEq (S r i)] [∀ r, SampleableType ((i : ι r) → S r i)]
    (k : (r : Fin n) → ι r → ℕ) (f : ((r : Fin n) → (i : ι r) → S r i) → Bool) :
    simulateQ (coins (S := ℕ) + counted f) (blockTreeFinder n ι S k) =
      blockTreeProgram (fun j => StateT.lift (ProbComp.uniformFin j)) n ι S k
        (fun r => StateT.lift ($ᵗ ((i : ι r) → S r i))) (counted f) := by
  have hcentre : ∀ r, simulateQ (coins (S := ℕ) + counted f)
      (OracleComp.liftComp ($ᵗ ((i : ι r) → S r i))
        (unifSpec + accSpec fun r => (i : ι r) → S r i)) =
      StateT.lift ($ᵗ ((i : ι r) → S r i)) := by
    intro r
    rw [QueryImpl.simulateQ_add_liftComp_left]
    apply StateT.ext
    intro s
    simp [coins, simulateQ_liftTarget]
  rw [blockTreeFinder, ← simulateQ'_apply, map_blockTreeProgram]
  simp only [hcentre]
  rfl

/-- Running the counted program from the counter `count` adds `count` to the finder's count. -/
theorem blockTreeProgram_counted_run (n : ℕ) (ι : Fin n → Type) [∀ r, Fintype (ι r)]
    [∀ r, DecidableEq (ι r)] (S : (r : Fin n) → ι r → Type) [∀ r i, Fintype (S r i)]
    [∀ r i, DecidableEq (S r i)] [∀ r, SampleableType ((i : ι r) → S r i)]
    (k : (r : Fin n) → ι r → ℕ) (f : ((r : Fin n) → (i : ι r) → S r i) → Bool) (count : ℕ) :
    (blockTreeProgram (fun j => StateT.lift (ProbComp.uniformFin j)) n ι S k
        (fun r => StateT.lift ($ᵗ ((i : ι r) → S r i))) (counted f)).run count =
      (fun z => (z.1, count + z.2)) <$> runFinder (blockTreeFinder n ι S k) f := by
  rw [← simulateQ_counted_blockTreeFinder]
  simpa only [Nat.zero_add, Nat.add_zero, Nat.add_comm, runFinder] using
    counted_run_add f (blockTreeFinder n ι S k) 0 count

/-- **One round of the counted finder.** With `n + 1` rounds, the counted finder is the block step
at a uniform centre, with charged children that are counted runs of the finder on the later
rounds. -/
theorem runFinder_blockTreeFinder_succ (n : ℕ) (ι : Fin (n + 1) → Type) [∀ r, Fintype (ι r)]
    [∀ r, DecidableEq (ι r)] (S : (r : Fin (n + 1)) → ι r → Type) [∀ r i, Fintype (S r i)]
    [∀ r i, DecidableEq (S r i)] [∀ r, SampleableType ((i : ι r) → S r i)]
    (k : (r : Fin (n + 1)) → ι r → ℕ) (f : ((r : Fin (n + 1)) → (i : ι r) → S r i) → Bool) :
    runFinder (blockTreeFinder (n + 1) ι S k) f =
      (fun z => (z.1.bind fun z => assembleChildren (blockChildList z), z.2)) <$>
        blockChildStep (fun c =>
          (fun z => (z.1.map fun t => (c, t), z.2)) <$>
            runFinder (blockTreeFinder n (fun r => ι r.succ) (fun r => S r.succ)
              (fun r => k r.succ)) (fun q => f (Fin.cons c q))) (k 0) := by
  rw [runFinder, simulateQ_counted_blockTreeFinder, blockTreeProgram]
  have hchild : (fun c => do
      let t ← blockTreeProgram (fun j => StateT.lift (ProbComp.uniformFin j)) n
        (fun r => ι r.succ) (fun r => S r.succ) (fun r => k r.succ)
        (fun r => StateT.lift ($ᵗ ((i : ι r.succ) → S r.succ i)))
        (fun q => counted f (Fin.cons c q))
      pure (t.map fun t => (c, t))) =
      chargedChild (fun c =>
        (fun z => (z.1.map fun t => (c, t), z.2)) <$>
          runFinder (blockTreeFinder n (fun r => ι r.succ) (fun r => S r.succ)
            (fun r => k r.succ)) (fun q => f (Fin.cons c q))) := by
    funext c
    apply StateT.ext
    intro count
    change ((do
      let t ← blockTreeProgram (fun j => StateT.lift (ProbComp.uniformFin j)) n
        (fun r => ι r.succ) (fun r => S r.succ) (fun r => k r.succ)
        (fun r => StateT.lift ($ᵗ ((i : ι r.succ) → S r.succ i)))
        (counted (fun q => f (Fin.cons c q)))
      pure (t.map fun t => (c, t))) : StateT ℕ ProbComp _).run count = _
    rw [StateT.run_bind, blockTreeProgram_counted_run]
    simp only [chargedChild, StateT.run_mk, StateT.run_pure, bind_pure_comp, Functor.map_map]
  rw [hchild]
  simp only [blockChildStep, StateT.run_bind, StateT.run_lift, map_bind, bind_pure_comp,
    bind_map_left, StateT.run_map]

/-- With no round left, the finder asks the acceptance oracle about the empty challenge, once. -/
theorem runFinder_blockTreeFinder_zero (ι : Fin 0 → Type) [∀ r, Fintype (ι r)]
    [∀ r, DecidableEq (ι r)] (S : (r : Fin 0) → ι r → Type) [∀ r i, Fintype (S r i)]
    [∀ r i, DecidableEq (S r i)] [∀ r, SampleableType ((i : ι r) → S r i)]
    (k : (r : Fin 0) → ι r → ℕ) (f : ((r : Fin 0) → (i : ι r) → S r i) → Bool) :
    runFinder (blockTreeFinder 0 ι S k) f =
      pure (if f (fun r => Fin.elim0 r) then some (VecTree.empty _ _) else none, 1) := by
  rw [runFinder, simulateQ_counted_blockTreeFinder, blockTreeProgram]
  simp [counted]

/-- **The cost of the multi-round block finder.** Its expected number of acceptance-oracle calls
is at most the product of the arities of its rounds. -/
theorem expectedCalls_blockTreeFinder : ∀ (n : ℕ) (ι : Fin n → Type) [∀ r, Fintype (ι r)]
    [∀ r, DecidableEq (ι r)] (S : (r : Fin n) → ι r → Type) [∀ r i, Fintype (S r i)]
    [∀ r i, DecidableEq (S r i)] [∀ r, SampleableType ((i : ι r) → S r i)]
    (k : (r : Fin n) → ι r → ℕ) (f : ((r : Fin n) → (i : ι r) → S r i) → Bool),
    expectedCalls (runFinder (blockTreeFinder n ι S k) f) ≤ ∏ r, (blockArity (k r) : ℝ≥0∞)
  | 0, ι, _, _, S, _, _, _, k, f => by
      rw [runFinder_blockTreeFinder_zero, expectedCalls_pure]
      simp
  | n + 1, ι, _, _, S, _, _, _, k, f => by
      rw [runFinder_blockTreeFinder_succ, Fin.prod_univ_succ]
      refine (le_of_eq (expectedCalls_map_output
        (fun o => Option.bind o fun z => assembleChildren (blockChildList z)) _)).trans ?_
      set T : ℝ≥0∞ := ∏ r : Fin n, (blockArity (k r.succ) : ℝ≥0∞)
      have hchild : ∀ c, expectedCalls ((fun z => (z.1.map fun t => (c, t), z.2)) <$>
          runFinder (blockTreeFinder n (fun r => ι r.succ) (fun r => S r.succ)
            (fun r => k r.succ)) (fun q => f (Fin.cons c q))) ≤ T := by
        intro c
        rw [expectedCalls_map_output (Option.map fun t => (c, t))]
        exact expectedCalls_blockTreeFinder n _ _ _ _
      refine (expectedCalls_blockChildStep_le _ (k 0)).trans ?_
      have havg : (∑ c, expectedCalls ((fun z => (z.1.map fun t => (c, t), z.2)) <$>
            runFinder (blockTreeFinder n (fun r => ι r.succ) (fun r => S r.succ)
              (fun r => k r.succ)) (fun q => f (Fin.cons c q)))) /
            (Fintype.card ((i : ι 0) → S 0 i) : ℝ≥0∞) ≤ T := by
        have hN : (Fintype.card ((i : ι 0) → S 0 i) : ℝ≥0∞) ≠ 0 := by
          exact_mod_cast Fintype.card_ne_zero
        rw [ENNReal.div_le_iff hN (by finiteness)]
        calc _ ≤ ∑ _c : (i : ι 0) → S 0 i, T := Finset.sum_le_sum fun c _ => hchild c
          _ = T * (Fintype.card ((i : ι 0) → S 0 i) : ℝ≥0∞) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
      calc _ ≤ (1 + ∑ j, ((k 0 j - 1 : ℕ) : ℝ≥0∞)) * T := mul_le_mul' le_rfl havg
        _ = (blockArity (k 0) : ℝ≥0∞) * T := by
          rw [blockArity]
          push_cast
          ring

/-- The error of one block round, `∑ j, (k j - 1) / |S j|`. -/
@[expose] noncomputable def blockError {ι : Type} [Fintype ι] {S : ι → Type} [∀ i, Fintype (S i)]
    (k : ι → ℕ) : ℝ≥0∞ :=
  ∑ j, ((k j - 1 : ℕ) : ℝ≥0∞) / (Fintype.card (S j) : ℝ≥0∞)

/-- The error of the multi-round block finder, `1 - ∏ r, (1 - κ r)` for the round errors `κ r`. -/
@[expose] noncomputable def blockTreeError {n : ℕ} {ι : Fin n → Type} [∀ r, Fintype (ι r)]
    (S : (r : Fin n) → ι r → Type) [∀ r i, Fintype (S r i)] (k : (r : Fin n) → ι r → ℕ) :
    ℝ≥0∞ :=
  1 - ∏ r, (1 - blockError (S := S r) (k r))

theorem blockTreeError_le_one {n : ℕ} {ι : Fin n → Type} [∀ r, Fintype (ι r)]
    (S : (r : Fin n) → ι r → Type) [∀ r i, Fintype (S r i)] (k : (r : Fin n) → ι r → ℕ) :
    blockTreeError S k ≤ 1 := tsub_le_self

/-- The error of the finder is at most the sum of the round errors. -/
theorem blockTreeError_le_sum {n : ℕ} {ι : Fin n → Type} [∀ r, Fintype (ι r)]
    (S : (r : Fin n) → ι r → Type) [∀ r i, Fintype (S r i)] (k : (r : Fin n) → ι r → ℕ) :
    blockTreeError S k ≤ ∑ r, blockError (S := S r) (k r) :=
  ENNReal.one_sub_prod_one_sub_le_sum _ _

/-- The error of the first round composes with the error of the later rounds. -/
theorem blockTreeError_succ {n : ℕ} {ι : Fin (n + 1) → Type} [∀ r, Fintype (ι r)]
    (S : (r : Fin (n + 1)) → ι r → Type) [∀ r i, Fintype (S r i)]
    (k : (r : Fin (n + 1)) → ι r → ℕ) (h0 : blockError (S := S 0) (k 0) ≤ 1) :
    blockTreeError S k = blockError (S := S 0) (k 0) +
      (1 - blockError (S := S 0) (k 0)) *
        blockTreeError (ι := fun r => ι r.succ) (fun r => S r.succ) (fun r => k r.succ) := by
  have hprod : ∀ {m : ℕ} {ι : Fin m → Type} [∀ r, Fintype (ι r)]
      (S : (r : Fin m) → ι r → Type) [∀ r i, Fintype (S r i)] (k : (r : Fin m) → ι r → ℕ),
      1 - blockTreeError S k = ∏ r, (1 - blockError (S := S r) (k r)) := by
    intro m ι _ S _ k
    rw [blockTreeError]
    exact ENNReal.sub_sub_cancel (by finiteness)
      (Finset.prod_le_one fun r _ => tsub_le_self)
  rw [blockTreeError, Fin.prod_univ_succ, ← hprod]
  exact ENNReal.one_sub_one_sub_mul_one_sub_eq_add_one_sub_mul h0 (blockTreeError_le_one _ _)

private theorem average_affine {C : Type} [Fintype C] [Nonempty C]
    (b d : ℝ≥0∞) (p : C → ℝ≥0∞) :
    (∑ c, (b + d * p c)) / Fintype.card C = b + d * ((∑ c, p c) / Fintype.card C) := by
  have hN : (Fintype.card C : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum, div_eq_mul_inv, add_mul]
  rw [mul_comm (Fintype.card C : ℝ≥0∞) b, mul_assoc b,
    ENNReal.mul_inv_cancel hN (by finiteness), mul_one, mul_assoc]

/-- **The success of the multi-round block finder.** When the error of every round is at most one,
the acceptance rate `ε` of any acceptance function and the success probability `p` of the finder
satisfy `ε ≤ κ + (1 - κ) p`, for the error `κ = 1 - ∏ r, (1 - κ r)` of `blockTreeError`. -/
theorem blockTreeFinder_success : ∀ (n : ℕ) (ι : Fin n → Type) [∀ r, Fintype (ι r)]
    [∀ r, DecidableEq (ι r)] (S : (r : Fin n) → ι r → Type) [∀ r i, Fintype (S r i)]
    [∀ r i, DecidableEq (S r i)] [∀ r, SampleableType ((i : ι r) → S r i)]
    (k : (r : Fin n) → ι r → ℕ) (_hκ : ∀ r, blockError (S := S r) (k r) ≤ 1)
    (f : ((r : Fin n) → (i : ι r) → S r i) → Bool),
    acceptRate f ≤ blockTreeError S k + (1 - blockTreeError S k) *
      Pr{let z ← runFinder (blockTreeFinder n ι S k) f}[z.1.isSome]
  | 0, ι, _, _, S, _, _, _, k, _, f => by
      rw [runFinder_blockTreeFinder_zero]
      have he : (default : (r : Fin 0) → (i : ι r) → S r i) = (fun r => Fin.elim0 r) :=
        Subsingleton.elim _ _
      cases hf : f (fun r => Fin.elim0 r) with
      | false => simp [blockTreeError, acceptRate, he, hf]
      | true =>
          have hcard : ({c ∈ ({fun r => Fin.elim0 r} : Finset ((r : Fin 0) → (i : ι r) → S r i)) |
              f c = true}).card ≤ 1 := (Finset.card_filter_le _ _).trans (by simp)
          simpa [blockTreeError, acceptRate, he, hf] using hcard
  | n + 1, ι, _, _, S, _, _, _, k, hκ, f => by
      classical
      let tail := fun c : (i : ι 0) → S 0 i =>
        runFinder (blockTreeFinder n (fun r => ι r.succ) (fun r => S r.succ) (fun r => k r.succ))
          (fun q => f (Fin.cons c q))
      let p := fun c : (i : ι 0) → S 0 i => Pr{let z ← tail c}[z.1.isSome]
      let child := fun c : (i : ι 0) → S 0 i =>
        (fun z => (z.1.map fun t => (c, t), z.2)) <$> tail c
      let node := blockChildStep child (k 0)
      have hprob : Pr{let z ← runFinder (blockTreeFinder (n + 1) ι S k) f}[z.1.isSome] =
          Pr{let z ← node}[z.1.isSome] := by
        rw [runFinder_blockTreeFinder_succ, prEvent_map]
        apply prEvent_congr_of_support
        intro z hz
        cases h : z.1 with
        | none => simp
        | some w =>
            have hz' : z ∈ support node := hz
            simp only [node, blockChildStep, mem_support_bind_iff] at hz'
            obtain ⟨c₀, -, hz'⟩ := hz'
            have hlen := length_of_mem_support_blockChildren_run ProbComp.uniformFin _ _ _ _ 0
              z hz' w h
            simp [assembleChildren, length_blockChildList (k 0) w hlen]
      have hstep := prEvent_child_le_blockChildStep child (k 0)
      have havg : Pr{let z ← (do let c ← $ᵗ ((i : ι 0) → S 0 i); child c)}[z.1.isSome] =
          (∑ c, p c) / Fintype.card ((i : ι 0) → S 0 i) := by
        let _ : MeasurableSpace ((i : ι 0) → S 0 i) := ⊤
        let _ : MeasurableSingletonClass ((i : ι 0) → S 0 i) := ⟨fun _ => trivial⟩
        rw [prEvent_bind_eq_lintegral_of_discrete, SampleableType.evalDist_uniformSample,
          ProbabilityTheory.lintegral_uniformOn_univ]
        simp only [child, p, prEvent_map, Option.isSome_map]
      rw [havg] at hstep
      set b := blockTreeError (ι := fun r => ι r.succ) (fun r => S r.succ) (fun r => k r.succ)
      have htail : ∀ c, acceptRate (fun q => f (Fin.cons c q)) ≤ b + (1 - b) * p c := fun c =>
        blockTreeFinder_success n _ _ _ (fun r => hκ r.succ) _
      rw [hprob, blockTreeError_succ S k (hκ 0)]
      apply affine_error_compose (hκ 0) (blockTreeError_le_one _ _)
      calc acceptRate f = (∑ c : (i : ι 0) → S 0 i, acceptRate (fun q => f (Fin.cons c q))) /
            Fintype.card ((i : ι 0) → S 0 i) := acceptRate_cons f
        _ ≤ (∑ c : (i : ι 0) → S 0 i, (b + (1 - b) * p c)) / Fintype.card ((i : ι 0) → S 0 i) :=
          ENNReal.div_le_div_right (Finset.sum_le_sum fun c _ => htail c) _
        _ = b + (1 - b) * ((∑ c, p c) / Fintype.card ((i : ι 0) → S 0 i)) := average_affine _ _ _
        _ ≤ b + (1 - b) * (blockError (S := S 0) (k 0) +
            (1 - blockError (S := S 0) (k 0)) * Pr{let z ← node}[z.1.isSome]) :=
          add_le_add le_rfl (mul_le_mul' le_rfl hstep)

/-- The node predicate of a block round: the siblings are pairwise distinct and form a block
star. -/
@[expose] def blockNodeOk {n : ℕ} {ι : Fin n → Type} [∀ r, Fintype (ι r)]
    {S : (r : Fin n) → ι r → Type} [∀ r i, DecidableEq (S r i)] (k : (r : Fin n) → ι r → ℕ)
    (r : Fin n) (ch : Fin (blockArity (k r)) → (i : ι r) → S r i) : Prop :=
  Function.Injective ch ∧ IsBlockSpecialSound (k r) (Finset.univ.image ch)

/-- **Soundness of the multi-round block program.** Every returned tree has block stars at its
nodes and accepted leaves. -/
theorem blockTreeProgram_sound {ιs : Type} {spec : OracleSpec ιs}
    (sample : (j : ℕ) → OracleComp spec (Fin (j + 1))) :
    ∀ (n : ℕ) (ι : Fin n → Type) [∀ r, Fintype (ι r)] [∀ r, DecidableEq (ι r)]
      (S : (r : Fin n) → ι r → Type) [∀ r i, Fintype (S r i)] [∀ r i, DecidableEq (S r i)]
      (k : (r : Fin n) → ι r → ℕ)
      (centre : (r : Fin n) → OracleComp spec ((i : ι r) → S r i))
      (accept : ((r : Fin n) → (i : ι r) → S r i) → OracleComp spec Bool)
      (f : ((r : Fin n) → (i : ι r) → S r i) → Bool)
      (_haccept : ∀ q, true ∈ support (accept q) → f q = true)
      (t : VecTree (fun r => (i : ι r) → S r i) (fun r => blockArity (k r)))
      (_ht : some t ∈ support (blockTreeProgram sample n ι S k centre accept)),
      t.IsStructured (blockNodeOk k) ∧ ∀ p, f (t.leaf p) = true
  | 0, ι, _, _, S, _, _, k, centre, accept, f, haccept, t, ht => by
      rw [blockTreeProgram, mem_support_bind_iff] at ht
      obtain ⟨b, hb, ht⟩ := ht
      cases b with
      | false => simp at ht
      | true =>
          simp only [ite_true, support_pure, Set.mem_singleton_iff, Option.some.injEq] at ht
          subst t
          exact ⟨fun _ r => Fin.elim0 r, fun _ => haccept _ hb⟩
  | n + 1, ι, _, _, S, _, _, k, centre, accept, f, haccept, t, ht => by
      classical
      rw [blockTreeProgram, mem_support_bind_iff] at ht
      obtain ⟨c₀, -, ht⟩ := ht
      rw [mem_support_bind_iff] at ht
      obtain ⟨z, hz, ht⟩ := ht
      cases z with
      | none => simp at ht
      | some w =>
          obtain ⟨w₀, ws⟩ := w
          simp only [Option.bind_some, support_pure, Set.mem_singleton_iff] at ht
          unfold assembleChildren at ht
          split at ht
          next hlenL =>
            have heq := Option.some.inj ht
            subst t
            set L := blockChildList (w₀, ws) with hL
            let P := fun w : ((i : ι 0) → S 0 i) ×
                VecTree (fun r : Fin n => (i : ι r.succ) → S r.succ i)
                  (fun r : Fin n => blockArity (k r.succ)) =>
              w.2.IsStructured (fun r : Fin n => blockNodeOk k r.succ) ∧
                ∀ p, f (Fin.cons w.1 (w.2.leaf p)) = true
            have hchild : ∀ c w, some w ∈ support (do
                let t ← blockTreeProgram sample n (fun r => ι r.succ) (fun r => S r.succ)
                  (fun r => k r.succ) (fun r => centre r.succ) (fun q => accept (Fin.cons c q))
                pure (t.map fun t => (c, t))) → w.1 = c ∧ P w := by
              intro c w hw
              rw [mem_support_bind_iff] at hw
              obtain ⟨u, hu, hw⟩ := hw
              cases u with
              | none => simp at hw
              | some u =>
                  simp only [Option.map_some, support_pure, Set.mem_singleton_iff,
                    Option.some.injEq] at hw
                  subst w
                  exact ⟨rfl, blockTreeProgram_sound sample n _ _ _ _ _
                    (fun q => f (Fin.cons c q)) (fun q => haccept (Fin.cons c q)) u hu⟩
            obtain ⟨hw₀, hcols⟩ := mem_support_blockChildren sample _ (k 0) c₀ _ w₀ ws hz
            obtain ⟨h0, hP0⟩ := hchild c₀ w₀ hw₀
            have hcol : ∀ j, ((ws j).map Prod.fst).Nodup ∧
                ∀ w ∈ ws j, w.1 ∈ neighbourPool c₀ j ∧ P w := fun j =>
              sound_collectChildren sample _ Prod.fst P hchild _ (k 0 j - 1) (neighbourPool c₀ j)
                rfl (nodup_neighbourPool c₀ j) (ws j) (hcols j).1
            obtain ⟨hnd, hstar⟩ := blockChildList_keys (k 0) c₀ w₀ ws h0
              (fun j => ⟨(hcol j).1, fun w hw => ((hcol j).2 w hw).1⟩) (fun j => (hcols j).2)
            have hPL : ∀ w ∈ L, P w := by
              intro w hw
              rw [hL, blockChildList, List.mem_cons, List.mem_flatMap] at hw
              rcases hw with rfl | ⟨j, -, hj⟩
              · exact hP0
              · exact ((hcol j).2 w hj).2
            have hget : ∀ j : Fin (blockArity (k 0)), (j : ℕ) < L.length := fun j => by
              simpa only [hlenL] using j.isLt
            constructor
            · refine VecTree.cons_isStructured_of (blockNodeOk k) _ ⟨?_, ?_⟩
                fun j => (hPL _ (List.getElem_mem (hget j))).1
              · intro i j hij
                apply Fin.ext
                apply (hnd.getElem_inj_iff
                  (hi := by simpa using hget i) (hj := by simpa using hget j)).mp
                rw [List.getElem_map, List.getElem_map]
                exact hij
              · have himage : (Finset.univ.image fun j : Fin (blockArity (k 0)) =>
                    (L[(j : ℕ)]'(hget j)).1) = (L.map Prod.fst).toFinset := by
                  ext x
                  simp only [Finset.mem_image, Finset.mem_univ, true_and, List.mem_toFinset,
                    List.mem_map]
                  constructor
                  · rintro ⟨j, rfl⟩
                    exact ⟨_, List.getElem_mem (hget j), rfl⟩
                  · rintro ⟨w, hw, rfl⟩
                    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
                    exact ⟨⟨i, by simpa only [hlenL] using hi⟩, rfl⟩
                exact himage ▸ hstar
            · intro p
              exact (hPL _ (List.getElem_mem (hget (p 0)))).2 (fun i => p i.succ)
          next => simp at ht

/-- **Soundness of the multi-round block finder.** Against every acceptance function, every
returned tree has block stars at its nodes and accepted leaves. -/
theorem blockTreeFinder_sound (n : ℕ) (ι : Fin n → Type) [∀ r, Fintype (ι r)]
    [∀ r, DecidableEq (ι r)] (S : (r : Fin n) → ι r → Type) [∀ r i, Fintype (S r i)]
    [∀ r i, DecidableEq (S r i)] [∀ r, SampleableType ((i : ι r) → S r i)]
    (k : (r : Fin n) → ι r → ℕ) (f : ((r : Fin n) → (i : ι r) → S r i) → Bool)
    (z : Option (VecTree (fun r => (i : ι r) → S r i) (fun r => blockArity (k r))) × ℕ)
    (hz : z ∈ support (runFinder (blockTreeFinder n ι S k) f))
    (t : VecTree (fun r => (i : ι r) → S r i) (fun r => blockArity (k r))) (ht : z.1 = some t) :
    t.IsStructured (blockNodeOk k) ∧ ∀ p, f (t.leaf p) = true := by
  have hz' : some t ∈ support (Prod.fst <$> runFinder (blockTreeFinder n ι S k) f) := by
    rw [support_map]
    exact ⟨z, hz, ht⟩
  rw [runFinder, counted_fst, blockTreeFinder, ← simulateQ'_apply, map_blockTreeProgram] at hz'
  refine blockTreeProgram_sound _ n ι S k _ _ f ?_ t hz'
  intro q hq
  rw [simulateQ'_apply, OracleComp.liftM_eq_liftM_liftM, OracleQuery.liftM_add_right_query,
    simulateQ_spec_query] at hq
  change true ∈ support (pure (f q) : ProbComp Bool) at hq
  simpa only [support_pure, Set.mem_singleton_iff, eq_comm] using hq

/-- **The multi-round block finder meets the tree-finder contract**, with block stars at its
nodes, the error `1 - ∏ r, (1 - κ r)` of `blockTreeError` when every round error `κ r` is at most
one, and cost the product of the round arities. -/
theorem isTreeFinder_blockTreeFinder (n : ℕ) (ι : Fin n → Type) [∀ r, Fintype (ι r)]
    [∀ r, DecidableEq (ι r)] (S : (r : Fin n) → ι r → Type) [∀ r i, Fintype (S r i)]
    [∀ r i, DecidableEq (S r i)] [∀ r, SampleableType ((i : ι r) → S r i)]
    (k : (r : Fin n) → ι r → ℕ) (hκ : ∀ r, blockError (S := S r) (k r) ≤ 1) :
    IsTreeFinder (fun r => blockArity (k r)) (blockNodeOk k) (blockTreeFinder n ι S k)
      (blockTreeError S k) (∏ r, (blockArity (k r) : ℝ≥0∞)) where
  one_le _ := Nat.le_add_left 1 _
  sound f z hz t ht := blockTreeFinder_sound n ι S k f z hz t ht
  success := blockTreeFinder_success n ι S k hκ
  cost := expectedCalls_blockTreeFinder n ι S k

end OracleComp
