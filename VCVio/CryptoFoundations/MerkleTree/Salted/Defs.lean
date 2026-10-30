/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.MerkleTree.LabelledPath
public import VCVio.CryptoFoundations.VectorCommitment
public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import Mathlib.Data.List.Rotate

/-!
# Salted Merkle commitments

The commitment of Chiesa, Di, Hu and Zheng, ePrint 2025/2166, Definition 8.2 uses perfect binary
trees and a common oracle for leaf payloads and node labels. Openings carry salts, path labels,
and siblings. The verifier checks a fixed query log of prescribed checks, deduplicated
across paths. One path contains `d + 1` checks, including its leaf; openings from one trapdoor
contain at most `2 * 2 ^ d - 1` distinct checks.
-/

public section

open OracleComp OracleSpec BinaryTree MerkleTreeHashing

universe uX uY uM uS

/-- A fixed tree shape has finitely many decorations by finite labels. -/
instance BinaryTree.FullData.instFinite {α : Type*} [Finite α] (s : Skeleton) :
    Finite (FullData α s) := by
  induction s with
  | leaf =>
      exact Finite.of_surjective FullData.leaf
        (by intro t; cases t; exact ⟨_, rfl⟩)
  | internal left right ihLeft ihRight =>
      let := ihLeft
      let := ihRight
      exact Finite.of_surjective
        (fun p : α × FullData α left × FullData α right =>
          FullData.internal p.1 p.2.1 p.2.2)
        (by
          intro t
          cases t with
          | internal value left right => exact ⟨(value, left, right), rfl⟩)

namespace SaltedMerkle

/-- Optional salts and a typed partial tree of digest labels. -/
abbrev Td (Y : Type uY) (Salt : Type uS) (d : ℕ) :=
  (Fin (2 ^ d) → Option Salt) × FullData (Option Y) (Skeleton.perfect d)

/-- The entirely unknown trapdoor, used for repeated oracle indices. -/
@[expose]
def tdBot {Y : Type uY} {Salt : Type uS} {d : ℕ} : Td Y Salt d :=
  (fun _ => none, populateDown _ (fun _ => (none, none)) none)

/-- Optional salts and typed perfect trees form a finite trapdoor register. -/
noncomputable instance instFintypeTd {Y : Type uY} {Salt : Type uS} [Fintype Y] [Fintype Salt]
    (d : ℕ) : Fintype (Td Y Salt d) := Fintype.ofFinite _

/-- A salt and the path-label/sibling pairs in root-to-leaf order. -/
structure PathProof (Y : Type uY) (Salt : Type uS) (d : ℕ) where
  /-- The salt of the opened leaf. -/
  salt : Salt
  /-- At each edge, the child on the path and its sibling. -/
  path : List.Vector (Y × Y) d
  deriving DecidableEq

/-- An opening has an entry exactly at its answered positions. -/
abbrev Pf (Y : Type uY) (Salt : Type uS) (d : ℕ) :=
  Fin (2 ^ d) → Option (PathProof Y Salt d)

variable {X : Type uX} {Y : Type uY} {Msg : Type uM} {Salt : Type uS} {d : ℕ}

/-- Regard the path vector at a typed leaf of the perfect tree. -/
@[expose]
def PathProof.at (pp : PathProof Y Salt d) (i : SkeletonLeafIndex (Skeleton.perfect d)) :
    List.Vector (Y × Y) i.depth :=
  ⟨pp.path.toList, by simp⟩

/-- Read the requested salts and labelled paths from a partial trapdoor. -/
@[expose]
def opening (d : ℕ) (Q : Finset (Fin (2 ^ d))) (td : Td Y Salt d) : Pf Y Salt d :=
  fun i => if i ∈ Q then
    (td.1 i).bind fun salt => (readPath td.2 (SkeletonLeafIndex.perfectEquiv d i)).map
      fun p => ⟨salt, ⟨p.toList, by simp⟩⟩
  else none

/-- The query log of an opened leaf: the leaf check followed by the prescribed node checks in
root-to-leaf order. Rotating the depth-many node entries places the final leaf entry first. -/
@[expose]
def leafLog (enc : QueryEncoding X Unit Unit (Msg × Salt) Y) (rt : Y)
    (i : Fin (2 ^ d)) (a : Msg) (pp : PathProof Y Salt d) : QueryLog (X →ₒ Y) :=
  (pathLog (enc.node ()) (enc.leaf () (a, pp.salt)) (SkeletonLeafIndex.perfectEquiv d i)
    rt (pp.at _)).rotate d

/-- The query log of the prescribed checks at an answered and opened position. -/
@[expose]
def entryLog (enc : QueryEncoding X Unit Unit (Msg × Salt) Y) (rt : Y) (i : Fin (2 ^ d)) :
    Option Msg → Option (PathProof Y Salt d) → QueryLog (X →ₒ Y)
  | some a, some pp => leafLog enc rt i a pp
  | _, _ => []

/-- Reject mismatched domains; otherwise log each prescribed check once. -/
@[expose]
def pairs [DecidableEq X] [DecidableEq Y]
    (enc : QueryEncoding X Unit Unit (Msg × Salt) Y) (d : ℕ) (rt : Y)
    (ans : PartialVec (2 ^ d) Msg) (pf : Pf Y Salt d) : Option (QueryLog (X →ₒ Y)) :=
  if ∀ i, (pf i).isSome = (ans i).isSome then
    some ((List.finRange (2 ^ d)).flatMap fun i => entryLog enc rt i (ans i) (pf i)).dedup
  else none

/-- Check the prescribed log against a partial oracle table. -/
@[expose]
def checkOn [DecidableEq X] [DecidableEq Y]
    (enc : QueryEncoding X Unit Unit (Msg × Salt) Y) (d : ℕ)
    (D : X → Option Y) (rt : Y) (ans : PartialVec (2 ^ d) Msg) (pf : Pf Y Salt d) : Bool :=
  (pairs enc d rt ans pf).elim false (QueryLog.agreesWith (.ofFn D))

variable (enc : QueryEncoding X Unit Unit (Msg × Salt) Y)

/-- One opening prescribes exactly one check per edge and one leaf check. -/
theorem length_leafLog (rt : Y) (i : Fin (2 ^ d)) (a : Msg) (pp : PathProof Y Salt d) :
    (leafLog enc rt i a pp).length = d + 1 := by
  simp [leafLog, length_pathLog]

/-- An unanswered position contributes no checks. -/
theorem length_entryLog_le (rt : Y) (i : Fin (2 ^ d)) (a : Option Msg)
    (pp : Option (PathProof Y Salt d)) :
    (entryLog enc rt i a pp).length ≤ if a.isSome then d + 1 else 0 := by
  cases a <;> cases pp <;> simp [entryLog, length_leafLog]

/-- A generated opening records exactly its salt and the tree's typed labelled path. -/
theorem path_of_opening_eq_some {Q : Finset (Fin (2 ^ d))} {td : Td Y Salt d}
    {i : Fin (2 ^ d)} {pp : PathProof Y Salt d} (h : opening d Q td i = some pp) :
    td.1 i = some pp.salt ∧
      readPath td.2 (SkeletonLeafIndex.perfectEquiv d i) = some (pp.at _) := by
  simp only [opening] at h
  split_ifs at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨salt, hs, p, hp, rfl⟩ := h
  exact ⟨hs, hp⟩

section Check
variable [DecidableEq X] [DecidableEq Y]
/-- The log has at most `d + 1` entries per opened position. -/
theorem length_pairs_le (rt : Y) (ans : PartialVec (2 ^ d) Msg) (pf : Pf Y Salt d)
    (log : QueryLog (X →ₒ Y)) (h : pairs enc d rt ans pf = some log) :
    log.length ≤ ans.dom.card * (d + 1) := by
  unfold pairs at h
  split_ifs at h with hpf
  obtain rfl := Option.some.inj h.symm
  refine (List.dedup_sublist _).length_le.trans ?_
  rw [List.length_flatMap]
  calc ((List.finRange (2 ^ d)).map fun ι ↦ (entryLog enc rt ι (ans ι) (pf ι)).length).sum
      ≤ ((List.finRange (2 ^ d)).map fun ι ↦ if (ans ι).isSome then d + 1 else 0).sum :=
        List.sum_le_sum fun ι _ ↦ length_entryLog_le enc rt ι _ _
    _ = ∑ ι, if (ans ι).isSome then d + 1 else 0 := by
        rw [← List.sum_ofFn, List.ofFn_eq_map]
    _ = ans.dom.card * (d + 1) := by
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
        rfl

end Check

/-- Root, node, and answered-leaf equations of a partial trapdoor. -/
structure Consistent (G : X → Y → Prop) (enc : QueryEncoding X Unit Unit (Msg × Salt) Y)
    (rt : Y) (ans : PartialVec (2 ^ d) Msg) (td : Td Y Salt d) : Prop where
  /-- The trapdoor carries the claimed root. -/
  root : td.2.getRootValue = some rt
  /-- Present children have their siblings and satisfy the parent hash relation. -/
  closed : PartialTreeConsistent G (enc.node ()) td.2
  /-- Answered leaves carry their salt and the prescribed hash of their payload. -/
  leaf : ∀ i a, ans i = some a → ∃ salt label, td.1 i = some salt ∧
    td.2.get (SkeletonLeafIndex.perfectEquiv d i).toNodeIndex = some label ∧
    G (enc.leaf () (a, salt)) label

namespace Consistent
variable {G : X → Y → Prop} {enc : QueryEncoding X Unit Unit (Msg × Salt) Y}
  {rt : Y} {ans : PartialVec (2 ^ d) Msg} {td : Td Y Salt d}

/-- Every answered leaf has a complete labelled opening whose prescribed checks hold. -/
theorem opening_eq_some (hc : Consistent G enc rt ans td) {i : Fin (2 ^ d)} {a : Msg}
    (ha : ans i = some a) : ∃ pp, opening d ans.dom td i = some pp ∧
      ∀ q ∈ leafLog enc rt i a pp, G q.1 q.2 := by
  obtain ⟨salt, label, hs, hl, hg⟩ := hc.leaf i a ha
  obtain ⟨root, p, hr, hp, hg⟩ := hc.closed.readPath _ hl hg
  rw [hc.root] at hr
  cases hr
  refine ⟨⟨salt, ⟨p.toList, by simp⟩⟩, ?_, ?_⟩
  · simp [opening, PartialVec.mem_dom, ha, hs, hp]
  · intro q hq
    exact hg q (List.mem_rotate.mp hq)

/-- Openings of a consistent trapdoor parse, and all their prescribed relations hold. -/
theorem pairs_opening [DecidableEq X] [DecidableEq Y] (hc : Consistent G enc rt ans td) :
    ∃ log, pairs enc d rt ans (opening d ans.dom td) = some log ∧
      ∀ q ∈ log, G q.1 q.2 := by
  have hpf : ∀ i, (opening d ans.dom td i).isSome = (ans i).isSome := by
    intro i
    cases ha : ans i with
    | none => simp [opening, PartialVec.mem_dom, ha]
    | some a => obtain ⟨pp, hp, _⟩ := hc.opening_eq_some ha; simp [hp]
  refine ⟨_, ite_eq_left hpf, fun q hq => ?_⟩
  rw [List.mem_dedup, List.mem_flatMap] at hq
  obtain ⟨i, _, hq⟩ := hq
  cases ha : ans i with
  | none => simp [ha, entryLog] at hq
  | some a =>
      obtain ⟨pp, hp, hg⟩ := hc.opening_eq_some ha
      rw [ha, hp] at hq
      exact hg q hq
end Consistent

/-- A generated family of paths contains at most one distinct check per tree vertex. -/
theorem length_pairs_opening_le [DecidableEq X] [DecidableEq Y] (rt : Y)
    (ans : PartialVec (2 ^ d) Msg) (Q : Finset (Fin (2 ^ d))) (td : Td Y Salt d)
    (log : QueryLog (X →ₒ Y)) (h : pairs enc d rt ans (opening d Q td) = some log) :
    log.length ≤ 2 * 2 ^ d - 1 := by
  let inputs : SkeletonLeafIndex (Skeleton.perfect d) → Option X := fun i =>
    (ans ((SkeletonLeafIndex.perfectEquiv d).symm i)).bind fun a =>
      (td.1 ((SkeletonLeafIndex.perfectEquiv d).symm i)).map fun salt => enc.leaf () (a, salt)
  have hsub : ∀ q ∈ log, q ∈ treeLog (enc.node ()) td.2 inputs rt := by
    unfold pairs at h
    split_ifs at h
    cases h
    intro q hq
    rw [List.mem_dedup, List.mem_flatMap] at hq
    obtain ⟨i, _, hq⟩ := hq
    cases ha : ans i <;> cases hp : opening d Q td i <;>
      simp only [ha, hp, entryLog, List.not_mem_nil] at hq
    rename_i a pp
    obtain ⟨hs, ht⟩ := path_of_opening_eq_some hp
    exact pathLog_subset_treeLog (enc.node ()) td.2 inputs rt _ _ ht
      (leaf := enc.leaf () (a, pp.salt))
      (by simp [inputs, ha, hs]) q (by simpa only [leafLog, List.mem_rotate] using hq)
  have hn : log.Nodup := by
    unfold pairs at h
    split_ifs at h
    cases h
    exact List.nodup_dedup _
  calc log.length = log.toFinset.card := (List.toFinset_card_of_nodup hn).symm
       _ ≤ (treeLog (enc.node ()) td.2 inputs rt).toFinset.card :=
         Finset.card_le_card (by
           intro q hq
           exact List.mem_toFinset.mpr (hsub q (List.mem_toFinset.mp hq)))
       _ ≤ (treeLog (enc.node ()) td.2 inputs rt).length := List.toFinset_card_le _
       _ ≤ 2 * 2 ^ d - 1 := by
         simpa using length_treeLog_le (enc.node ()) td.2 inputs rt

/-- The honest tree for fixed messages, salts and a fixed hash function. -/
@[expose]
def honestTree (enc : QueryEncoding X Unit Unit (Msg × Salt) Y) (d : ℕ) (H : X → Y)
    (msg : Fin (2 ^ d) → Msg) (γ : Fin (2 ^ d) → Salt) : Y × Td Y Salt d :=
  let leaves := LeafData.ofFun (Skeleton.perfect d) fun i =>
    H (enc.leaf () (msg ((SkeletonLeafIndex.perfectEquiv d).symm i),
      γ ((SkeletonLeafIndex.perfectEquiv d).symm i)))
  let t := populateUp leaves fun a b => H (enc.node () (a, b))
  (t.getRootValue, (fun i => some (γ i), t.map some))

/-- Honest trapdoors satisfy the fixed hash equations for every restriction of the message. -/
theorem consistent_honestTree (enc : QueryEncoding X Unit Unit (Msg × Salt) Y) (d : ℕ)
    (H : X → Y) (msg : Fin (2 ^ d) → Msg) (γ : Fin (2 ^ d) → Salt)
    (Q : Finset (Fin (2 ^ d))) :
    Consistent (fun x y => H x = y) enc (honestTree enc d H msg γ).1
      (PartialVec.restrict msg Q) (honestTree enc d H msg γ).2 := by
  refine ⟨FullData.map_getRootValue _ _, partialTreeConsistent_populateUp _ _ _, ?_⟩
  intro i a ha
  have hmsg : a = msg i := by
    by_cases hi : i ∈ Q <;> simp [hi] at ha
    exact ha.symm
  subst a
  refine ⟨γ i, H (enc.leaf () (msg i, γ i)), rfl, ?_, rfl⟩
  simp [honestTree]


section Commit
variable {X : Type uX} {Y Salt : Type uY} {Msg : Type uM}

/-- Build the commitment with fixed salts through the shared addressed Merkle builder. -/
@[expose]
def commitTree (enc : QueryEncoding X Unit Unit (Msg × Salt) Y) (d : ℕ)
    (msg : Fin (2 ^ d) → Msg) (γ : Fin (2 ^ d) → Salt) :
    OracleComp (X →ₒ Y) (Y × Td Y Salt d) := do
  let t ← AddressedMerkleTree.buildMerkleTreeAddressedM (s := Skeleton.perfect d)
    (fun i => (X →ₒ Y).query (enc.leaf ()
      (msg ((SkeletonLeafIndex.perfectEquiv d).symm i),
        γ ((SkeletonLeafIndex.perfectEquiv d).symm i))))
    (fun _ a b => (X →ₒ Y).query (enc.node () (a, b)))
  pure (t.getRootValue, (fun i => some (γ i), t.map some))

/-- Fixed-function simulation gives equality of the root and every label of the honest tree. -/
theorem simulateQ_commitTree {m : Type uY → Type*} [Monad m] [LawfulMonad m]
    (enc : QueryEncoding X Unit Unit (Msg × Salt) Y) (d : ℕ) (H : X → Y)
    (msg : Fin (2 ^ d) → Msg) (γ : Fin (2 ^ d) → Salt) :
    simulateQ (fun x => (pure (H x) : m Y)) (commitTree enc d msg γ) =
      pure (honestTree enc d H msg γ) := by
  simp only [commitTree, simulateQ_bind, simulateQ_pure]
  rw [AddressedMerkleTree.simulateQ_buildMerkleTreeAddressedM_with]
  simp only [simulateQ_spec_query]
  rw [AddressedMerkleTree.buildMerkleTreeAddressedM_pure, pure_bind,
    AddressedMerkleTree.buildMerkleTreeAddressed_const]
  rfl

end Commit
/-! ## The scheme

`Commit` samples the salts with `unifSpec` and queries `X →ₒ Y`, so this section takes `Y` and
`Salt` in `Type`. -/

section Scheme

variable {X : Type uX} {Y Salt : Type} {Msg : Type uM}

/-- The salted Merkle commitment `MT[σ, Σ, ℓ = 2 ^ d, ν]` (Def 8.2, pp. 52–53). `Commit` samples
the salts uniformly with `unifSpec` and hashes bottom-up, `Open` reads the paths from the
trapdoor, and `Check` rechecks the prescribed query log.
`Open` is deterministic and `Check` is coin-free, so the scheme is a `DetVectorCommitment`. -/
@[expose]
def scheme [DecidableEq X] [DecidableEq Y] [SampleableType Salt]
    (enc : QueryEncoding X Unit Unit (Msg × Salt) Y)
    (d : ℕ) : DetVectorCommitment X Y Msg Y (Td Y Salt d) (Pf Y Salt d) (2 ^ d) where
  commit msg := do
    let γ ← OracleComp.liftComp ($ᵗ (Fin (2 ^ d) → Salt)) (unifSpec + (X →ₒ Y))
    OracleComp.liftComp (commitTree enc d msg γ) (unifSpec + (X →ₒ Y))
  opening := opening d
  check rt ans pf := (pairs enc d rt ans pf).elim (pure false) QueryLog.recheck

/-- The non-adaptive check of `scheme enc d`, with at most `d + 1` checks per opened position. -/
@[expose]
def nonadaptiveCheck [DecidableEq X] [DecidableEq Y] [SampleableType Salt]
    (enc : QueryEncoding X Unit Unit (Msg × Salt) Y) (d : ℕ) :
    (scheme (Msg := Msg) enc d).toVectorCommitment.NonadaptiveCheck where
  log := pairs enc d
  check_eq _ _ _ := rfl
  qVC q := q * (d + 1)
  qVC_mono _ _ h := Nat.mul_le_mul_right _ h
  length_le rt ans pf L h := length_pairs_le enc rt ans pf L h

/-- The table check of `nonadaptiveCheck enc d` is `checkOn enc d`. -/
theorem nonadaptiveCheck_checkOn [DecidableEq X] [DecidableEq Y] [SampleableType Salt]
    (enc : QueryEncoding X Unit Unit (Msg × Salt) Y) (d : ℕ) :
    (nonadaptiveCheck enc d).checkOn = checkOn enc d :=
  rfl

/-- **Perfect completeness** of the salted Merkle commitment against every fixed oracle function
(Def 3.7, p. 27; §8.3, p. 55). -/
theorem perfectlyComplete [DecidableEq X] [DecidableEq Y] [SampleableType Salt]
    (enc : QueryEncoding X Unit Unit (Msg × Salt) Y) (d : ℕ) :
    (scheme (Msg := Msg) enc d).PerfectlyComplete := by
  unfold DetVectorCommitment.PerfectlyComplete
  intro H msg Q z hz
  simp only [scheme, VectorCommitment.fixedOracleImpl, simulateQ_bind] at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨γ, -, hz⟩ := hz
  rw [QueryImpl.simulateQ_add_liftComp_right (QueryImpl.id' unifSpec)
    (fun x ↦ (pure (H x) : ProbComp Y)) (commitTree enc d msg γ)] at hz
  rw [simulateQ_commitTree] at hz
  rw [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  obtain ⟨log, hlog, hG⟩ := (consistent_honestTree enc d H msg γ Q).pairs_opening
  rw [PartialVec.dom_restrict] at hlog
  change evalWithAnswerFn _
    ((pairs enc d _ _ (opening d Q _)).elim (pure false) QueryLog.recheck) = true
  rw [hlog, Option.elim_some, QueryLog.evalWithAnswerFn_recheck, List.all_eq_true]
  intro p hp
  simp [hG p hp]

/-- **Perfect completeness relative to every oracle distribution** (Def 3.7, p. 27): the salted
Merkle commitment, as a general vector commitment, is perfectly complete for every distribution `D`
on oracle functions. -/
theorem perfectlyComplete_toVectorCommitment [DecidableEq X] [DecidableEq Y] [SampleableType Salt]
    [MeasurableSpace (X → Y)] (enc : QueryEncoding X Unit Unit (Msg × Salt) Y) (d : ℕ)
    (D : MeasureTheory.Measure (X → Y)) [MeasureTheory.IsProbabilityMeasure D] :
    (scheme (Msg := Msg) enc d).toVectorCommitment.PerfectlyComplete D :=
  (perfectlyComplete enc d).toVectorCommitment D

end Scheme

end SaltedMerkle
