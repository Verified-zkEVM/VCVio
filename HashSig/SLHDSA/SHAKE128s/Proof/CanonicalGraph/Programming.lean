/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CanonicalGraph.Input
public import HashSig.SLHDSA.SHAKE128s.Proof.CanonicalGraph.Evaluation
public import HashSig.SLHDSA.SHAKE128s.Proof.GraphFreshSampling
public import Mathlib.Data.List.Sort
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Rank-order programming of the actual structural byte oracle

The secret seed is fixed explicitly. Every structural output is a full 240-bit
answer; only its first 128 bits feed child-dependent inputs. A rank-order
traversal has the exact state-and-cache law of an independent full-output table.

`warmup` queries the shared random oracle at every structural node's canonical input, in
increasing rank (`order`). Its final cells and cache are those of a uniformly sampled output
table (`warmup_uniform`), with the cache holding the full answers at exactly the canonical inputs
(`cacheFrom`, `cacheFrom_lookup`, `cacheFrom_canonical`). Splitting the seed and output table
into cells and padding (`splitTable`) is a bijection, so with an independently sampled secret
seed the cells and the padding are independent and uniform (`warmup_seed_uniform`). Any hash
function agreeing with the programmed cache evaluates the algorithms to the sampled cells
(`value_eq_of_cache_agreement`).
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.CanonicalGraph.Programming

/-- A full hash output for every structural node. -/
abbrev Outputs := StructuralNode → HashOutput

/-- The preorder comparing structural nodes by rank. -/
@[expose] def RankLE (left right : StructuralNode) : Prop := left.rank ≤ right.rank

/-- Rank comparison is decided on the ranks. -/
instance : DecidableRel RankLE := fun _ _ => inferInstanceAs (Decidable (_ ≤ _))
/-- Rank comparison is transitive. -/
@[expose] instance : IsTrans StructuralNode RankLE := ⟨fun _ _ _ => Nat.le_trans⟩
/-- Any two structural nodes are comparable by rank. -/
@[expose] instance : Std.Total RankLE := ⟨fun _ _ => Nat.le_total _ _⟩

/-- All structural nodes, listed in nondecreasing rank, so every node comes after its
children. -/
@[expose] noncomputable def order : List StructuralNode :=
  (Finset.univ : Finset StructuralNode).toList.mergeSort (RankLE · ·)

/-- `order` is sorted by rank. -/
theorem order_pairwise : order.Pairwise RankLE :=
  List.pairwise_mergeSort' RankLE _

/-- `order` lists each node once. -/
theorem order_nodup : order.Nodup := by
  unfold order
  exact (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)

/-- `order` lists every structural node. -/
theorem mem_order (node : StructuralNode) : node ∈ order := by
  unfold order
  exact (List.mergeSort_perm _ _).mem_iff.mpr (by simp)

/-- The cells before the traversal: the secret seed at its node and zero elsewhere. -/
@[expose] def initialCells (secretSeed : Digest) : Cells
  | .secretSeed => secretSeed
  | .structural _ => 0

/-- The cells determined by a seed and a full output table: each structural cell is the
truncation of the node's output. -/
@[expose] def cellsOfOutputs (secretSeed : Digest) (outputs : Outputs) : Cells
  | .secretSeed => secretSeed
  | .structural parent => Hashing.truncate (outputs parent)

/-- Records the truncation of a hash output as the cell of the given node. -/
@[expose] def assign (parent : StructuralNode) (cells : Cells) (output : HashOutput) : Cells :=
  Function.update cells (.structural parent) (Hashing.truncate output)

/-- The byte input queried for a node during the traversal: its canonical input under the
current cells. -/
@[expose] def input (publicSeed : Digest) (parent : StructuralNode) (cells : Cells) : Bytes :=
  canonicalInput publicSeed cells parent

/-- The rank-order traversal querying the hash oracle at every structural node's canonical
input and recording each answer's truncation as the node's cell. -/
@[expose] noncomputable def warmup (publicSeed secretSeed : Digest) : OracleComp HashSpec Cells :=
  GraphFreshSampling.evaluate (input publicSeed) assign order (initialCells secretSeed)

/-- The canonical cache written using final cells, rather than partial traversal states. -/
@[expose] def cacheFrom (publicSeed : Digest) (cells : Cells) (outputs : Outputs) :
    List StructuralNode → QueryCache HashSpec → QueryCache HashSpec
  | [], cache => cache
  | parent :: parents, cache => cacheFrom publicSeed cells outputs parents
      (cache.cacheQuery (canonicalInput publicSeed cells parent) (outputs parent))

/-- The cells agree with the target on the secret seed and on every structural node outside the
given list. -/
@[expose] def AgreesOutside (remaining : List StructuralNode) (cells target : Cells) : Prop :=
  cells .secretSeed = target .secretSeed ∧
    ∀ parent ∉ remaining, cells (.structural parent) = target (.structural parent)

/-- Assigning the next node its target cell shrinks the region of possible disagreement. -/
theorem AgreesOutside.assign (remaining : List StructuralNode) (parent : StructuralNode)
    (cells target : Cells) (output : HashOutput)
    (hagrees : AgreesOutside (parent :: remaining) cells target)
    (houtput : Hashing.truncate output = target (.structural parent)) :
    AgreesOutside remaining (assign parent cells output) target := by
  constructor
  · simpa only [Programming.assign,
      Function.update_of_ne (by simp : Node.secretSeed ≠ .structural parent)] using hagrees.1
  · intro other hother
    by_cases heq : other = parent
    · subst other
      simpa only [Programming.assign, Function.update_self] using houtput
    · rw [Programming.assign, Function.update_of_ne (by simpa using heq)]
      exact hagrees.2 other (by simp [heq, hother])

/-- When the remaining nodes are rank-sorted and the cells agree with the target outside them,
the next node is queried at its final canonical input. -/
theorem input_eq_target (publicSeed : Digest) (parent : StructuralNode)
    (remaining : List StructuralNode) (cells target : Cells)
    (horder : (parent :: remaining).Pairwise RankLE)
    (hagrees : AgreesOutside (parent :: remaining) cells target) :
    input publicSeed parent cells = canonicalInput publicSeed target parent := by
  apply canonicalInput_congr
  intro child hchild
  cases child with
  | secretSeed => exact hagrees.1
  | structural child =>
      apply hagrees.2 child
      intro hmem
      have hlt : child.rank < parent.rank := by
        simpa only [Node.rank] using parent.child_rank_lt (.structural child) hchild
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact (Nat.lt_irrefl _ hlt)
      · exact (Nat.not_lt_of_ge ((List.pairwise_cons.mp horder).1 child htail)) hlt

/-- Programming a rank-sorted list of nodes yields the target cells and the canonical cache
written with them. -/
theorem program_eq_cacheFrom (publicSeed : Digest) (outputs : Outputs)
    (parents : List StructuralNode) (horder : parents.Pairwise RankLE)
    (cells target : Cells) (hagrees : AgreesOutside parents cells target)
    (houtputs : ∀ parent, Hashing.truncate (outputs parent) = target (.structural parent))
    (cache : QueryCache HashSpec) :
    GraphFreshSampling.program (input publicSeed) assign outputs parents cells cache =
      (target, cacheFrom publicSeed target outputs parents cache) := by
  induction parents generalizing cells cache with
  | nil =>
      have heq : cells = target := by
        funext node
        cases node with
        | secretSeed => exact hagrees.1
        | structural parent => exact hagrees.2 parent (by simp)
      simp only [GraphFreshSampling.program, cacheFrom, heq]
  | cons parent parents ih =>
      rw [GraphFreshSampling.program, input_eq_target publicSeed parent parents cells target
        horder hagrees]
      exact ih (List.pairwise_cons.mp horder).2
        (assign parent cells (outputs parent))
        (hagrees.assign parents parent cells target (outputs parent) (houtputs parent)) _

/-- Distinct nodes are queried at distinct inputs, whatever the cells. -/
theorem input_separated (publicSeed : Digest) :
    GraphFreshSampling.Separated (input publicSeed) := by
  intro left right hne leftCells rightCells heq
  exact hne (canonicalInput_parent heq)

/-- Exact law under the actual full-output shared random oracle, including its cache. -/
theorem warmup_uniform (publicSeed secretSeed : Digest) :
    (simulateQ randomOracle (warmup publicSeed secretSeed)).run ∅ =ᵈ
      ((fun outputs : Outputs =>
        (cellsOfOutputs secretSeed outputs,
          cacheFrom publicSeed (cellsOfOutputs secretSeed outputs) outputs order ∅)) <$>
        ($ᵗ Outputs : ProbComp Outputs)) := by
  rw [warmup]
  refine (GraphFreshSampling.evalDist_evaluate_eq_uniform_program
    (input publicSeed) assign (input_separated publicSeed) order order_nodup
      (initialCells secretSeed) ∅ (by intro _ _ _; rfl)).trans ?_
  have hprogram : (fun outputs : Outputs => GraphFreshSampling.program (input publicSeed) assign
        outputs order (initialCells secretSeed) ∅) =
      (fun outputs : Outputs =>
        (cellsOfOutputs secretSeed outputs,
          cacheFrom publicSeed (cellsOfOutputs secretSeed outputs) outputs order ∅)) := by
    funext outputs
    apply program_eq_cacheFrom publicSeed outputs order order_pairwise
    · constructor
      · rfl
      · intro parent hnot
        exact (hnot (mem_order parent)).elim
    · intro parent
      rfl
  rw [hprogram]

/-- Every canonical coordinate has its full 240-bit answer installed. -/
theorem cacheFrom_lookup (publicSeed : Digest) (cells : Cells) (outputs : Outputs)
    (parents : List StructuralNode) (cache : QueryCache HashSpec) (parent : StructuralNode) :
    cacheFrom publicSeed cells outputs parents cache (canonicalInput publicSeed cells parent) =
      if parent ∈ parents then some (outputs parent)
      else cache (canonicalInput publicSeed cells parent) := by
  induction parents generalizing cache with
  | nil => simp [cacheFrom]
  | cons current parents ih =>
      rw [cacheFrom, ih]
      by_cases heq : parent = current
      · subst current
        simp [QueryCache.cacheQuery_self]
      · have hinput :
            canonicalInput publicSeed cells parent ≠ canonicalInput publicSeed cells current :=
          fun h => heq (canonicalInput_parent h)
        rw [QueryCache.cacheQuery_of_ne _ _ hinput]
        simp only [List.mem_cons, heq, false_or]

/-- And nothing else is installed: the programmed cache is exactly the canonical entries,
which is the hypothesis every charge takes about the cache it starts from. -/
theorem cacheFrom_canonical (publicSeed : Digest) (cells : Cells) (outputs : Outputs)
    (parents : List StructuralNode) (cache : QueryCache HashSpec)
    (hcache : ∀ input, cache input ≠ none →
      ∃ parent : StructuralNode, input = canonicalInput publicSeed cells parent)
    (input : Bytes) (hinput : cacheFrom publicSeed cells outputs parents cache input ≠ none) :
    ∃ parent : StructuralNode, input = canonicalInput publicSeed cells parent := by
  induction parents generalizing cache with
  | nil => exact hcache input hinput
  | cons current parents ih =>
      refine ih _ ?_ hinput
      intro key hkey
      by_cases heq : key = canonicalInput publicSeed cells current
      · exact ⟨current, heq⟩
      · exact hcache key (by rwa [QueryCache.cacheQuery_of_ne _ _ heq] at hkey)

/-- The programmed cache of a whole walk carries canonical entries and nothing else. -/
theorem cacheFrom_empty_canonical (publicSeed : Digest) (cells : Cells) (outputs : Outputs)
    (parents : List StructuralNode) (input : Bytes)
    (hinput : cacheFrom publicSeed cells outputs parents ∅ input ≠ none) :
    ∃ parent : StructuralNode, input = canonicalInput publicSeed cells parent :=
  cacheFrom_canonical publicSeed cells outputs parents ∅
    (fun key hkey => absurd (by simp) hkey) input hinput

/-- The cache programmed over all of `order` holds every node's full output at its canonical
input. -/
theorem full_cache_lookup (publicSeed secretSeed : Digest) (outputs : Outputs)
    (parent : StructuralNode) :
    cacheFrom publicSeed (cellsOfOutputs secretSeed outputs) outputs order ∅
      (canonicalInput publicSeed (cellsOfOutputs secretSeed outputs) parent) =
        some (outputs parent) := by
  rw [cacheFrom_lookup, ite_eq_left (mem_order parent)]

/-- Every completion of the programmed byte cache evaluates the actual component
algorithms to the sampled cells. Cache agreement is a deterministic consistency
condition, not an assumed component distribution or security property. -/
theorem value_eq_of_cache_agreement [HasQuery HashSpec Id]
    (publicSeed secretSeed : Digest) (outputs : Outputs)
    (hagrees : ∀ input output,
      cacheFrom publicSeed (cellsOfOutputs secretSeed outputs) outputs order ∅ input =
        some output → Hashing.hash (m := Id) input = output) :
    value secretSeed publicSeed = cellsOfOutputs secretSeed outputs := by
  apply value_unique
  · rfl
  · intro parent
    have hhash := hagrees _ _ (full_cache_lookup publicSeed secretSeed outputs parent)
    simp only [Hashing.shortHash, hhash, bind, pure]
    rfl

/-- Split the independently sampled seed and full output table into all short
graph cells (including the seed) and the unused 112-bit suffix at every hash node. -/
@[expose] def splitTable (table : Digest × Outputs) : Cells × Padding :=
  (cellsOfOutputs table.1 table.2, fun parent => (table.2 parent).extractLsb' 0 112)

/-- Splitting a seed and output table into cells and padding loses no information. -/
theorem splitTable_bijective : Function.Bijective splitTable := by
  constructor
  · rintro ⟨seed, outputs⟩ ⟨seed', outputs'⟩ heq
    have hcells := congrArg Prod.fst heq
    have hpadding := congrArg Prod.snd heq
    have hseed := congrFun hcells Node.secretSeed
    have houtputs : outputs = outputs' := by
      funext parent
      have hshort := congrFun hcells (Node.structural parent)
      have hsuffix := congrFun hpadding parent
      change Hashing.truncate (outputs parent) = Hashing.truncate (outputs' parent) at hshort
      change (outputs parent).extractLsb' 0 112 = (outputs' parent).extractLsb' 0 112 at hsuffix
      have hleft : Hashing.truncate (outputs parent) ++
          (outputs parent).extractLsb' 0 112 = outputs parent :=
        BitVec.extractLsb'_append_extractLsb'
      have hright : Hashing.truncate (outputs' parent) ++
          (outputs' parent).extractLsb' 0 112 = outputs' parent :=
        BitVec.extractLsb'_append_extractLsb'
      rw [← hleft, ← hright, hshort, hsuffix]
    exact Prod.ext hseed houtputs
  · rintro ⟨cells, padding⟩
    refine ⟨(cells .secretSeed, fullOutput cells padding), ?_⟩
    apply Prod.ext
    · funext node
      cases node with
      | secretSeed => rfl
      | structural parent => exact truncate_fullOutput _ _ _
    · funext parent
      exact BitVec.extractLsb'_append_eq_right

/-- The split of a uniform seed and output table is a uniform pair of cells and padding. -/
theorem splitTable_uniform :
    (splitTable <$> ($ᵗ (Digest × Outputs) : ProbComp (Digest × Outputs))) =ᵈ
      ($ᵗ (Cells × Padding) : ProbComp (Cells × Padding)) :=
  SampleableType.map_uniformSample_evalDistEq_of_bijective splitTable_bijective

/-- Sampling a uniform pair is sampling its components independently. -/
private theorem uniformSample_prod_eq_bind {α β : Type}
    [SampleableType α] [SampleableType β] :
    ($ᵗ (α × β) : ProbComp (α × β)) =
      (do let left ← $ᵗ α; let right ← $ᵗ β; pure (left, right)) := by
  rw [uniformSample]
  change ((·, ·) <$> ($ᵗ α) <*> ($ᵗ β)) = _
  simp only [seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]

/-- Actual graph presampling with the independently sampled secret seed has an
independent uniform cell table and an independent uniform suffix table. Its cache
still contains the full 240-bit answers at the real seed-dependent byte inputs. -/
theorem warmup_seed_uniform (publicSeed : Digest) :
    (do
      let secretSeed ← $ᵗ Digest
      (simulateQ randomOracle (warmup publicSeed secretSeed)).run ∅) =ᵈ
      ((fun table : Cells × Padding =>
        (table.1, cacheFrom publicSeed table.1 (fullOutput table.1 table.2) order ∅)) <$>
        ($ᵗ (Cells × Padding) : ProbComp (Cells × Padding))) := by
  let result := fun table : Cells × Padding =>
    (table.1, cacheFrom publicSeed table.1 (fullOutput table.1 table.2) order ∅)
  have hstep := EvalDistEq.bind_right ($ᵗ Digest : ProbComp Digest)
    (fun secretSeed => warmup_uniform publicSeed secretSeed)
  have hprog : (do
      let secretSeed ← $ᵗ Digest
      (fun outputs : Outputs =>
        (cellsOfOutputs secretSeed outputs,
          cacheFrom publicSeed (cellsOfOutputs secretSeed outputs) outputs order ∅)) <$>
            ($ᵗ Outputs : ProbComp Outputs)) =
      result <$> (splitTable <$> ($ᵗ (Digest × Outputs) : ProbComp (Digest × Outputs))) := by
    have hfull : ∀ secretSeed outputs,
        fullOutput (cellsOfOutputs secretSeed outputs)
          (fun parent => (outputs parent).extractLsb' 0 112) = outputs := by
      intro secretSeed outputs
      funext parent
      exact BitVec.extractLsb'_append_extractLsb'
    rw [uniformSample_prod_eq_bind]
    simp only [result, splitTable, map_eq_bind_pure_comp, Function.comp_def,
      bind_assoc, pure_bind, hfull]
  rw [hprog] at hstep
  exact hstep.trans (splitTable_uniform.map result)

end SLHDSA.SHAKE128s.CanonicalGraph.Programming
