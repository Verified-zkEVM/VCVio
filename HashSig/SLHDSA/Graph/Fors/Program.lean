/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Graph.Input
public import HashSig.SLHDSA.Graph.Fors.Dependencies
public import HashSig.SLHDSA.SecretProvider
public import VCVio.OracleComp.QueryTracking.RandomOracle.Traversal
import HashSig.SLHDSA.Graph.Encoding
import VCVio.OracleComp.QueryTracking.RandomOracle.Traversal.Frame
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Exact effectful FORS signing as a structural traversal

The existing provider-parametric signer and the existing ordered traversal have the same free
program. The proof records returned answers at full natural addresses, derives persistence of
previous signature cells, and erases only that private proof memory. No finite, uniform,
decidable-equality or inhabited structure on node values is required.
-/

public section

universe u

open OracleComp OracleSpec

namespace SLHDSA.Graph.Fors

/-- Read the existing signature carrier at its selected-provider and authentication cells. -/
@[expose] def reconstruct {p : Params} (core : CorePrimitives p) (key : ForsKey p) (md : List Byte)
    (cells : Node p → core.Y) : ForsSigCore p core :=
  Vector.ofFn fun tree : Fin p.k =>
    ⟨cells (.structural (.forsPrf key (ForsSchedule.selected md tree))),
      Vector.ofFn fun height : Fin p.a =>
        cells (.structural (ForsSchedule.authentication key (ForsSchedule.selected md tree)
            height))⟩

variable {p : Params} (valid : p.Valid) (core : CorePrimitives p)

private abbrev Memory := Adrs → core.Y
private abbrev NativeSpec := (Adrs × List (core.Y)) →ₒ core.Y

private def project (sk : core.Y) (memory : Memory core) :
    Node p → core.Y
  | .secretSeed => sk
  | .structural node => memory node.address

private noncomputable def extendCells (cells : Node p → core.Y) : Memory core :=
  Function.extend StructuralNode.address (fun node => cells (.structural node))
    (fun _ => cells .secretSeed)

/-- Every arbitrary public cell table extends to the full natural-address memory. -/
private theorem project_extend (cells : Node p → core.Y) :
    project core (cells .secretSeed) (extendCells core cells) = cells := by
  funext coordinate
  cases coordinate with
  | secretSeed => rfl
  | structural node =>
      unfold project extendCells
      exact StructuralNode.address_injective.extend_apply _ _ node

/-- Natural-address writes commute with the exact graph-cell projection at every parameter. -/
private theorem project_update (sk value : core.Y) (memory : Memory core)
    (node : StructuralNode p) :
    project core sk (Function.update memory node.address value) =
      Function.update (project core sk memory) (.structural node) value := by
  funext coordinate
  cases coordinate with
  | secretSeed => simp [project]
  | structural other =>
      by_cases same : other = node
      · subst other; simp [project]
      · have addressDifferent : other.address ≠ node.address :=
          fun h => same (StructuralNode.address_injective h)
        simp [project, Function.update_of_ne, addressDifferent, same]

private noncomputable def nativeProgram (sk : core.Y) (md : List Byte)
    (key : ForsKey p) :
    OracleComp (NativeSpec core) (ForsSigCore p core) :=
  forsSignWithSecret core
    (fun address value => query (spec := NativeSpec core) (address, [value]))
    (fun address left right => query (spec := NativeSpec core) (address, [left, right]))
    (fun address => query (spec := NativeSpec core) (address, [sk])) md key.address

/-- Natural labels are interpreted by the exact canonical FORS encoding at every parameter. -/
private def naturalInput (sk : core.Y) (node : StructuralNode p)
    (memory : Memory core) : (NativeSpec core).Domain :=
  (node.address, (node.children valid).map (project core sk memory))

private noncomputable def naturalAssign (node : StructuralNode p)
    (memory : Memory core) (value : core.Y) : Memory core :=
  Function.update memory node.address value

private noncomputable def rawRecorded :
    QueryImpl (NativeSpec core) (StateT (Memory core) (OracleComp (NativeSpec core))) :=
  (QueryImpl.id' (NativeSpec core)).postInsert (fun input answer =>
    (fun memory => pure (PUnit.unit, Function.update memory input.1 answer) :
      StateT (Memory core) (OracleComp (NativeSpec core)) PUnit))

private theorem rawRecorded_run (input : (NativeSpec core).Domain) (memory : Memory core) :
    (rawRecorded core input).run memory =
      (fun answer => (answer, Function.update memory input.1 answer)) <$>
        (query (spec := NativeSpec core) input : OracleComp (NativeSpec core) (core.Y)) := by
  simp only [rawRecorded, QueryImpl.postInsert_apply, QueryImpl.id'_apply,
    StateT.run_bind, liftM_run_StateT, bind_pure_comp]
  rfl

private theorem naturalInput_prf (sk : core.Y) (key : ForsKey p)
    (index : Fin (p.k * 2 ^ p.a)) (memory : Memory core) :
    naturalInput valid core sk (.forsPrf key index) memory =
      ((StructuralNode.forsPrf key index).address, [sk]) := rfl

private theorem naturalInput_leaf (sk : core.Y) (key : ForsKey p)
    (index : Fin (p.k * 2 ^ p.a)) (memory : Memory core) :
    naturalInput valid core sk (ForsSchedule.treeNode key 0 (by omega) index) memory =
      ((ForsSchedule.treeNode key 0 (by omega) index).address,
        [memory (StructuralNode.forsPrf key index).address]) := rfl

private theorem raw_leaf_joint (sk : core.Y) (key : ForsKey p)
    (index : Fin (p.k * 2 ^ p.a)) (memory : Memory core) :
    (simulateQ (rawRecorded core)
      (forsLeafWithSecret core
        (fun address value => query (spec := NativeSpec core) (address, [value]))
        (fun address => query (spec := NativeSpec core) (address, [sk])) key.address index.val :
          OracleComp (NativeSpec core) (core.Y))).run memory =
    (fun final => (final (ForsSchedule.treeNode key 0 (by omega) index).address, final)) <$>
      RandomOracleTraversal.evaluate (naturalInput valid core sk) (naturalAssign core)
        (ForsSchedule.subtree key 0 (by omega) index) memory := by
  have actual : simulateQ (rawRecorded core)
      (forsLeafWithSecret core
        (fun address value => query (spec := NativeSpec core) (address, [value]))
        (fun address => query (spec := NativeSpec core) (address, [sk])) key.address index.val :
          OracleComp (NativeSpec core) (core.Y)) =
      (do
        let secret ← rawRecorded core ((StructuralNode.forsPrf key index).address, [sk])
        rawRecorded core ((ForsSchedule.treeNode key 0 (by omega) index).address, [secret]) :
          StateT (Memory core) (OracleComp (NativeSpec core)) (core.Y)) :=
    (forsLeafWithSecret_natural core (simulateQ' (rawRecorded core))
      (fun address value => query (spec := NativeSpec core) (address, [value]))
      (fun address value => rawRecorded core (address, [value]))
      (fun address => query (spec := NativeSpec core) (address, [sk]))
      (fun address => rawRecorded core (address, [sk]))
      (fun _ _ => simulateQ_spec_query _ _) (fun _ _ => simulateQ_spec_query _ _)
      key.address index.val).trans (by rfl)
  refine (congrArg (fun computation : StateT (Memory core) (OracleComp (NativeSpec core))
    (core.Y) => computation.run memory) actual).trans ?_
  simp only [StateT.run_bind, rawRecorded_run, bind_map_left]
  simp only [ForsSchedule.subtree, RandomOracleTraversal.evaluate, naturalInput_prf,
    naturalInput_leaf, naturalAssign,
    Functor.map_map, map_bind, bind_pure_comp, Function.update_self, HasQuery.instOfMonadLift_query,
    InductiveMerkleTree.range_def]
  apply congrArg (Bind.bind (query (spec := NativeSpec core)
    ((StructuralNode.forsPrf key index).address, [sk]) :
      OracleComp (NativeSpec core) (core.Y)))
  funext answer
  exact congrArg (fun stored : core.Y =>
    (fun leaf => (leaf, Function.update
      (Function.update memory (StructuralNode.forsPrf key index).address answer)
      (ForsSchedule.treeNode key 0 (by omega) index).address leaf)) <$>
        (query (spec := NativeSpec core)
          ((ForsSchedule.treeNode key 0 (by omega) index).address, [stored]) :
            OracleComp (NativeSpec core) (core.Y)))
    (Function.update_self (StructuralNode.forsPrf key index).address answer memory).symm

private noncomputable def leafProgram (sk : core.Y) (key : ForsKey p)
    (index : Nat) : OracleComp (NativeSpec core) (core.Y) :=
  forsLeafWithSecret core
    (fun address value => query (spec := NativeSpec core) (address, [value]))
    (fun address => query (spec := NativeSpec core) (address, [sk])) key.address index

private noncomputable def nodeProgram (key : ForsKey p) (height index : Nat)
    (left right : core.Y) : OracleComp (NativeSpec core) (core.Y) :=
  forsNodeHashWith (fun address left right => query (spec := NativeSpec core) (address, [left,
      right]))
    key.address height index left right

private theorem naturalInput_parent (sk : core.Y) (key : ForsKey p)
    (height : Nat) (bound : height + 1 ≤ p.a)
    (index : Fin (p.k * 2 ^ (p.a - (height + 1)))) (memory : Memory core) :
    naturalInput valid core sk (ForsSchedule.treeNode key (height + 1) bound index) memory =
      ((ForsSchedule.treeNode key (height + 1) bound index).address,
        [memory (ForsSchedule.treeNode key height (by omega)
          ⟨2 * index.val, by simpa using (child_index_lt p.a height p.k (by omega) index
              0)⟩).address,
        memory (ForsSchedule.treeNode key height (by omega)
          ⟨2 * index.val + 1, by simpa using (child_index_lt p.a height p.k (by omega) index
              1)⟩).address]) := rfl

private theorem raw_subtree_joint (sk : core.Y) (key : ForsKey p)
    (height : Nat) (bound : height ≤ p.a)
    (index : Fin (p.k * 2 ^ (p.a - height))) (memory : Memory core) :
    (simulateQ (rawRecorded core)
      (PerfectMerkleTree.merkleRootM (leafProgram core sk key) (nodeProgram core key)
        height index.val)).run memory =
    (fun final => (final (ForsSchedule.treeNode key height bound index).address, final)) <$>
      RandomOracleTraversal.evaluate (naturalInput valid core sk) (naturalAssign core)
        (ForsSchedule.subtree key height bound index) memory := by
  induction height generalizing memory with
  | zero => exact raw_leaf_joint valid core sk key index memory
  | succ height ih =>
      simp only [PerfectMerkleTree.merkleRootM, simulateQ_bind, StateT.run_bind]
      let left : Fin (p.k * 2 ^ (p.a - height)) :=
        ⟨2 * index.val, by simpa using (child_index_lt p.a height p.k (by omega) index 0)⟩
      let right : Fin (p.k * 2 ^ (p.a - height)) :=
        ⟨2 * index.val + 1, by simpa using (child_index_lt p.a height p.k (by omega) index 1)⟩
      rw [ih (by omega) left memory, bind_map_left]
      rw [ForsSchedule.subtree, RandomOracleTraversal.evaluate_append,
          RandomOracleTraversal.evaluate_append]
      simp only [map_bind, bind_assoc, RandomOracleTraversal.evaluate]
      apply congrArg (Bind.bind (RandomOracleTraversal.evaluate (naturalInput valid core sk)
        (naturalAssign core) (ForsSchedule.subtree key height (by omega) left) memory))
      funext leftMemory
      rw [ih (by omega) right leftMemory, bind_map_left]
      apply OracleComp.bind_congr_of_forall_mem_support
      intro rightMemory reachable
      have leftStayed : rightMemory (ForsSchedule.treeNode key height (by omega) left).address =
          leftMemory (ForsSchedule.treeNode key height (by omega) left).address := by
        apply RandomOracleTraversal.read_outside_of_mem_support (naturalInput valid core sk)
          (fun node => node.address) (fun _ answer => answer)
          (ForsSchedule.subtree key height (by omega) right) leftMemory
          (ForsSchedule.treeNode key height (by omega) left).address ?_ rightMemory reachable
        intro node member same
        have equal := StructuralNode.address_injective same
        subst node
        have inside := ForsSchedule.mem_subtree_footprint key height (by omega) right
          (ForsSchedule.treeNode key height (by omega) left) member
        simp only [ForsSchedule.Footprint, ForsSchedule.treeNode, Fin.val_mk,
          Nat.sub_self, pow_zero, Nat.div_one] at inside
        have impossible := inside.2.2
        dsimp only [left, right] at impossible
        omega
      change (simulateQ (rawRecorded core)
        (query (spec := NativeSpec core)
          ((ForsSchedule.treeNode key (height + 1) bound index).address,
            [leftMemory (ForsSchedule.treeNode key height (by omega) left).address,
              rightMemory (ForsSchedule.treeNode key height (by omega) right).address]) :
            OracleComp (NativeSpec core) (core.Y))).run rightMemory = _
      rw [simulateQ_HasQuery_query, rawRecorded_run, naturalInput_parent]
      simp only [map_pure, bind_pure_comp]
      simp only [naturalAssign, Function.update_self,
        InductiveMerkleTree.range_def, HasQuery.instOfMonadLift_query]
      exact congrArg (fun leftValue : core.Y =>
        (fun answer => (answer, Function.update rightMemory
          (ForsSchedule.treeNode key (height + 1) bound index).address answer)) <$>
        (query (spec := NativeSpec core)
          ((ForsSchedule.treeNode key (height + 1) bound index).address,
            [leftValue, rightMemory (ForsSchedule.treeNode key height (by omega) right).address]) :
              OracleComp (NativeSpec core) (core.Y))) leftStayed.symm

private theorem sibling_ne_self (index : Nat) : PerfectMerkleTree.sibling index ≠ index := by
  unfold PerfectMerkleTree.sibling
  split_ifs <;> omega

private theorem sibling_intervals_disjoint (key : ForsKey p) (selected lower upper : Nat)
    (ordered : lower < upper) (node : StructuralNode p) :
    ¬ (ForsSchedule.Footprint key lower (PerfectMerkleTree.sibling (selected / 2 ^ lower)) node ∧
      ForsSchedule.Footprint key upper (PerfectMerkleTree.sibling (selected / 2 ^ upper)) node)
          := by
  have arithmetic (level position : Nat) (levelBound : level ≤ lower)
      (first : position / 2 ^ (lower - level) = PerfectMerkleTree.sibling (selected / 2 ^ lower))
      (second : position / 2 ^ (upper - level) = PerfectMerkleTree.sibling (selected / 2 ^
          upper)) : False := by
    have same : PerfectMerkleTree.sibling (selected / 2 ^ upper) = selected / 2 ^ upper := by
      calc
        PerfectMerkleTree.sibling (selected / 2 ^ upper) = position / 2 ^ (upper - level) :=
            second.symm
        _ = position / 2 ^ (lower - level) / 2 ^ (upper - lower) := by
          rw [PerfectMerkleTree.div_pow_eq_div_pow_div_pow position (lower - level)
            (upper - level) (by omega), show upper - level - (lower - level) = upper - lower by
                omega]
        _ = PerfectMerkleTree.sibling (selected / 2 ^ lower) / 2 ^ (upper - lower) := by rw [first]
        _ = selected / 2 ^ lower / 2 ^ (upper - lower) :=
          PerfectMerkleTree.sibling_div_pow _ _ (by omega)
        _ = selected / 2 ^ upper :=
          (PerfectMerkleTree.div_pow_eq_div_pow_div_pow _ _ _ (by omega)).symm
    exact sibling_ne_self _ same
  cases node with
  | forsPrf location leaf =>
      rintro ⟨⟨_, first⟩, ⟨_, second⟩⟩
      exact arithmetic 0 leaf.val (by omega) first second
  | forsTree location level position =>
      rintro ⟨⟨_, levelBound, first⟩, ⟨_, _, second⟩⟩
      exact arithmetic level.val position.val levelBound first second
  | _ => simp [ForsSchedule.Footprint]

private theorem earlier_auth_not_mem_subtree (key : ForsKey p)
    (selected : Fin (p.k * 2 ^ p.a)) (height : Nat)
    (bound : height + 1 ≤ p.a) (level : Fin height) :
    ForsSchedule.authentication key selected ⟨level.val, by omega⟩ ∉
      ForsSchedule.subtree key height (by omega)
        ⟨PerfectMerkleTree.sibling (selected.val / 2 ^ height),
          ForsSchedule.sibling_bound selected height (by omega)⟩ := by
  intro member
  have first : ForsSchedule.Footprint key level.val
      (PerfectMerkleTree.sibling (selected.val / 2 ^ level.val))
      (ForsSchedule.authentication key selected ⟨level.val, by omega⟩) := by
    simp [ForsSchedule.Footprint, ForsSchedule.authentication, ForsSchedule.treeNode]
  exact sibling_intervals_disjoint key selected.val level.val height level.isLt _
    ⟨first, ForsSchedule.mem_subtree_footprint key height (by omega) _ _ member⟩

private theorem raw_auth_joint (sk : core.Y) (key : ForsKey p)
    (selected : Fin (p.k * 2 ^ p.a)) (height : Nat)
    (bound : height ≤ p.a) (memory : Memory core) :
    (simulateQ (rawRecorded core)
      (PerfectMerkleTree.intrinsicAuthPathM (leafProgram core sk key) (nodeProgram core key)
        selected.val height)).run memory =
    (fun final => (Vector.ofFn (fun level : Fin height => final
      (ForsSchedule.authentication key selected ⟨level.val, by omega⟩).address), final)) <$>
      RandomOracleTraversal.evaluate (naturalInput valid core sk) (naturalAssign core)
        (ForsSchedule.auth key selected height bound) memory := by
  induction height generalizing memory with
  | zero => simp [PerfectMerkleTree.intrinsicAuthPathM, ForsSchedule.auth,
      RandomOracleTraversal.evaluate]
  | succ height ih =>
      let sibling : Fin (p.k * 2 ^ (p.a - height)) :=
        ⟨PerfectMerkleTree.sibling (selected.val / 2 ^ height),
          ForsSchedule.sibling_bound selected height (by omega)⟩
      simp only [PerfectMerkleTree.intrinsicAuthPathM, simulateQ_bind,
        StateT.run_bind, simulateQ_pure, StateT.run_pure]
      rw [ih (by omega) memory, bind_map_left]
      rw [ForsSchedule.auth, RandomOracleTraversal.evaluate_append]
      simp only [map_bind]
      apply congrArg (Bind.bind (RandomOracleTraversal.evaluate (naturalInput valid core sk)
        (naturalAssign core) (ForsSchedule.auth key selected height (by omega)) memory))
      funext before
      rw [raw_subtree_joint valid core sk key height (by omega) sibling before, bind_map_left]
      rw [map_eq_bind_pure_comp]
      apply OracleComp.bind_congr_of_forall_mem_support
      intro final reachable
      have prior (level : Fin height) :
          final (ForsSchedule.authentication key selected ⟨level.val, by omega⟩).address =
          before (ForsSchedule.authentication key selected ⟨level.val, by omega⟩).address := by
        apply RandomOracleTraversal.read_outside_of_mem_support (naturalInput valid core sk)
          (fun node => node.address) (fun _ answer => answer)
          (ForsSchedule.subtree key height (by omega) sibling) before
          (ForsSchedule.authentication key selected ⟨level.val, by omega⟩).address ?_ final
              reachable
        intro node member same
        have equal := StructuralNode.address_injective same
        subst node
        exact earlier_auth_not_mem_subtree key selected height bound level member
      apply congrArg pure
      apply Prod.ext
      · dsimp only
        rw [Vector.ofFn_succ]
        exact congrArg (fun f : Fin height → core.Y =>
          (Vector.ofFn f).push (final (ForsSchedule.treeNode key height (by omega)
              sibling).address))
          (funext fun level => (prior level).symm)
      · rfl

private noncomputable def treeProgram (sk : core.Y) (key : ForsKey p)
    (selected : Fin (p.k * 2 ^ p.a)) :
    OracleComp (NativeSpec core) (ForsTreeSigCore p core) := do
  let secret ← query (spec := NativeSpec core) ((StructuralNode.forsPrf key selected).address, [sk])
  let path ← PerfectMerkleTree.intrinsicAuthPathM (leafProgram core sk key) (nodeProgram core key)
    selected.val p.a
  return ⟨secret, path⟩

private theorem raw_tree_joint (sk : core.Y) (key : ForsKey p)
    (selected : Fin (p.k * 2 ^ p.a)) (memory : Memory core) :
    (simulateQ (rawRecorded core) (treeProgram core sk key selected)).run memory =
    (fun final => ((⟨final (StructuralNode.forsPrf key selected).address,
      Vector.ofFn fun level : Fin p.a =>
        final (ForsSchedule.authentication key selected level).address⟩ :
          ForsTreeSigCore p core), final)) <$>
      RandomOracleTraversal.evaluate (naturalInput valid core sk) (naturalAssign core)
        (.forsPrf key selected :: ForsSchedule.auth key selected p.a le_rfl) memory := by
  simp only [treeProgram, simulateQ_bind, simulateQ_HasQuery_query,
    StateT.run_bind, rawRecorded_run, bind_map_left]
  simp only [RandomOracleTraversal.evaluate, naturalInput_prf, map_bind]
  apply congrArg (Bind.bind (query (spec := NativeSpec core)
    ((StructuralNode.forsPrf key selected).address, [sk]) :
      OracleComp (NativeSpec core) (core.Y)))
  funext secret
  rw [raw_auth_joint valid core sk key selected p.a le_rfl]
  simp only [bind_map_left, simulateQ_pure, StateT.run_pure]
  rw [map_eq_bind_pure_comp]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro final reachable
  have selectedSurvives : final (StructuralNode.forsPrf key selected).address = secret := by
    have saved := RandomOracleTraversal.read_outside_of_mem_support (naturalInput valid core sk)
      (fun node => node.address) (fun _ answer => answer)
      (ForsSchedule.auth key selected p.a le_rfl)
      (Function.update memory (StructuralNode.forsPrf key selected).address secret)
      (StructuralNode.forsPrf key selected).address
      (by
        intro node member same
        have equal := StructuralNode.address_injective same
        subst node
        exact ForsSchedule.selected_prf_not_mem_auth key selected p.a le_rfl member)
      final reachable
    exact saved.trans (Function.update_self _ _ _)
  apply congrArg pure
  apply Prod.ext
  · exact congrArg (fun value : core.Y =>
      (⟨value, Vector.ofFn fun level : Fin p.a =>
        final (ForsSchedule.authentication key selected level).address⟩ :
          ForsTreeSigCore p core)) selectedSurvives.symm
  · rfl

/-- The existing FORS body is exactly the indexed sequence of these selected-provider/auth slots. -/
private theorem nativeProgram_treeProgram (sk : core.Y) (md : List Byte)
    (key : ForsKey p) :
    nativeProgram core sk md key = Vector.ofFnM (fun tree : Fin p.k =>
      treeProgram core sk key (ForsSchedule.selected md tree)) := rfl

private def InForestTree (key : ForsKey p) (tree : Nat) : StructuralNode p → Prop
  | .forsPrf location leaf => location = key ∧ leaf.val / 2 ^ p.a = tree
  | .forsTree location level index =>
      location = key ∧ index.val / 2 ^ (p.a - level.val) = tree
  | _ => False

private theorem footprint_forestTree (key : ForsKey p) (selected height : Nat)
    (bound : height < p.a) (node : StructuralNode p)
    (inside : ForsSchedule.Footprint key height (PerfectMerkleTree.sibling (selected / 2 ^
        height)) node) :
    InForestTree key (selected / 2 ^ p.a) node := by
  have arithmetic (level position : Nat) (levelBound : level ≤ height)
      (descendant : position / 2 ^ (height - level) = PerfectMerkleTree.sibling (selected / 2 ^
          height)) :
      position / 2 ^ (p.a - level) = selected / 2 ^ p.a := by
    calc
      position / 2 ^ (p.a - level) =
          position / 2 ^ (height - level) / 2 ^ (p.a - height) := by
        rw [PerfectMerkleTree.div_pow_eq_div_pow_div_pow position (height - level)
          (p.a - level) (by omega),
          show p.a - level - (height - level) = p.a - height by omega]
      _ = PerfectMerkleTree.sibling (selected / 2 ^ height) / 2 ^ (p.a - height) := by rw
          [descendant]
      _ = selected / 2 ^ height / 2 ^ (p.a - height) := PerfectMerkleTree.sibling_div_pow _ _
          (by omega)
      _ = selected / 2 ^ p.a :=
        (PerfectMerkleTree.div_pow_eq_div_pow_div_pow _ _ _ (by omega)).symm
  cases node with
  | forsPrf location leaf =>
      obtain ⟨same, descendant⟩ := inside
      exact ⟨same, arithmetic 0 leaf.val (by omega) descendant⟩
  | forsTree location level index =>
      obtain ⟨same, levelBound, descendant⟩ := inside
      exact ⟨same, arithmetic level.val index.val levelBound descendant⟩
  | _ => contradiction

private theorem auth_forestTree (key : ForsKey p)
    (selected : Fin (p.k * 2 ^ p.a)) (height : Nat) (bound : height ≤ p.a)
    (node : StructuralNode p) (member : node ∈ ForsSchedule.auth key selected height bound) :
    InForestTree key (selected.val / 2 ^ p.a) node := by
  induction height with
  | zero => simp [ForsSchedule.auth] at member
  | succ height ih =>
      rw [ForsSchedule.auth, List.mem_append] at member
      rcases member with earlier | current
      · exact ih (by omega) earlier
      · exact footprint_forestTree key selected.val height (by omega) node
          (ForsSchedule.mem_subtree_footprint key height (by omega) _ _ current)

private theorem inForestTree_unique (key : ForsKey p) (left right : Nat)
    (node : StructuralNode p) (first : InForestTree key left node)
    (second : InForestTree key right node) : left = right := by
  cases node with
  | forsPrf location leaf | forsTree location level index => exact first.2.symm.trans second.2
  | _ => contradiction

private def slotSchedule (key : ForsKey p) (selected : Fin (p.k * 2 ^ p.a)) :
    List (StructuralNode p) :=
  .forsPrf key selected :: ForsSchedule.auth key selected p.a le_rfl

private theorem slot_forestTree (key : ForsKey p) (md : List Byte) (tree : Fin p.k)
    (node : StructuralNode p) (member : node ∈ slotSchedule key (ForsSchedule.selected md tree)) :
    InForestTree key tree.val node := by
  rcases List.mem_cons.mp member with rfl | auth
  · exact ⟨rfl, ForsSchedule.selected_div md tree⟩
  · have inside := auth_forestTree key (ForsSchedule.selected md tree) p.a le_rfl node auth
    rwa [ForsSchedule.selected_div] at inside

private theorem different_slot_address (key : ForsKey p) (md : List Byte)
    (left right : Fin p.k) (different : left ≠ right)
    (saved : StructuralNode p) (savedIn : saved ∈ slotSchedule key (ForsSchedule.selected md
        left)) :
    ∀ node ∈ slotSchedule key (ForsSchedule.selected md right), node.address ≠ saved.address := by
  intro node member same
  have equal := StructuralNode.address_injective same
  subst node
  exact different (Fin.ext (inForestTree_unique key left.val right.val saved
    (slot_forestTree key md left saved savedIn) (slot_forestTree key md right saved member)))

private def readTree (key : ForsKey p) (selected : Fin (p.k * 2 ^ p.a))
    (memory : Memory core) : ForsTreeSigCore p core :=
  ⟨memory (StructuralNode.forsPrf key selected).address,
    Vector.ofFn fun height : Fin p.a =>
      memory (ForsSchedule.authentication key selected height).address⟩

private noncomputable def forestPrefix (sk : core.Y) (md : List Byte) (key : ForsKey p)
    (count : Nat) (bound : count ≤ p.k) :
    OracleComp (NativeSpec core) (Vector (ForsTreeSigCore p core) count) :=
  Vector.ofFnM fun tree : Fin count =>
    treeProgram core sk key (ForsSchedule.selected md ⟨tree.val, by omega⟩)

private def schedulePrefix (md : List Byte) (key : ForsKey p) (count : Nat)
    (bound : count ≤ p.k) : List (StructuralNode p) :=
  (List.ofFn fun tree : Fin count =>
    slotSchedule key (ForsSchedule.selected md ⟨tree.val, by omega⟩)).flatten

private def readPrefix (md : List Byte) (key : ForsKey p) (count : Nat)
    (bound : count ≤ p.k) (memory : Memory core) :
    Vector (ForsTreeSigCore p core) count :=
  Vector.ofFn fun tree : Fin count =>
    readTree core key (ForsSchedule.selected md ⟨tree.val, by omega⟩) memory

private theorem schedulePrefix_succ (md : List Byte) (key : ForsKey p)
    (count : Nat) (bound : count + 1 ≤ p.k) :
    schedulePrefix md key (count + 1) bound =
      schedulePrefix md key count (by omega) ++
        slotSchedule key (ForsSchedule.selected md ⟨count, by omega⟩) := by
  unfold schedulePrefix
  rw [List.ofFn_succ_last, List.flatten_append]
  simp

private theorem readTree_preserved (sk : core.Y) (key : ForsKey p)
    (md : List Byte) (left right : Fin p.k) (different : left ≠ right)
    (memory final : Memory core) (reachable : final ∈ support
      (RandomOracleTraversal.evaluate (naturalInput valid core sk) (naturalAssign core)
        (slotSchedule key (ForsSchedule.selected md right)) memory)) :
    readTree core key (ForsSchedule.selected md left) final =
      readTree core key (ForsSchedule.selected md left) memory := by
  have saved (node : StructuralNode p)
      (member : node ∈ slotSchedule key (ForsSchedule.selected md left)) :
      final node.address = memory node.address :=
    RandomOracleTraversal.read_outside_of_mem_support (naturalInput valid core sk)
      (fun node => node.address) (fun _ answer => answer)
      (slotSchedule key (ForsSchedule.selected md right)) memory node.address
      (different_slot_address key md left right different node member) final reachable
  have secret := saved (.forsPrf key (ForsSchedule.selected md left)) (by simp [slotSchedule])
  have path : (fun level : Fin p.a =>
      final (ForsSchedule.authentication key (ForsSchedule.selected md left) level).address) =
      (fun level : Fin p.a =>
        memory (ForsSchedule.authentication key (ForsSchedule.selected md left) level).address)
            := by
    funext level
    exact saved (ForsSchedule.authentication key (ForsSchedule.selected md left) level)
      (List.mem_cons_of_mem _ (ForsSchedule.authentication_mem_auth key _ p.a le_rfl level))
  exact congrArg₂ (fun (secret : core.Y) (auth : Vector (core.Y) p.a) =>
    (⟨secret, auth⟩ : ForsTreeSigCore p core)) secret (congrArg Vector.ofFn path)

private theorem forestPrefix_succ (sk : core.Y) (md : List Byte) (key : ForsKey p)
    (count : Nat) (bound : count + 1 ≤ p.k) :
    forestPrefix core sk md key (count + 1) bound =
      (do
        let previous ← forestPrefix core sk md key count (by omega)
        let next ← treeProgram core sk key (ForsSchedule.selected md ⟨count, by omega⟩)
        pure (previous.push next)) := by
  unfold forestPrefix
  rw [Vector.ofFnM_succ]
  rfl

private theorem raw_forest_prefix_joint (sk : core.Y) (md : List Byte)
    (key : ForsKey p) (count : Nat) (bound : count ≤ p.k) (memory : Memory core) :
    (simulateQ (rawRecorded core) (forestPrefix core sk md key count bound)).run memory =
    (fun final => (readPrefix core md key count bound final, final)) <$>
      RandomOracleTraversal.evaluate (naturalInput valid core sk) (naturalAssign core)
        (schedulePrefix md key count bound) memory := by
  induction count generalizing memory with
  | zero => simp [forestPrefix, schedulePrefix, readPrefix, RandomOracleTraversal.evaluate]
  | succ count ih =>
      rw [forestPrefix_succ]
      simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure]
      rw [ih (by omega) memory, bind_map_left, schedulePrefix_succ,
          RandomOracleTraversal.evaluate_append]
      simp only [map_bind]
      apply congrArg (Bind.bind (RandomOracleTraversal.evaluate (naturalInput valid core sk)
        (naturalAssign core) (schedulePrefix md key count (by omega)) memory))
      funext before
      rw [raw_tree_joint valid core sk key (ForsSchedule.selected md ⟨count, by omega⟩) before,
          bind_map_left]
      rw [map_eq_bind_pure_comp]
      apply OracleComp.bind_congr_of_forall_mem_support
      intro final reachable
      have prior (tree : Fin count) :
          readTree core key (ForsSchedule.selected md ⟨tree.val, by omega⟩) final =
          readTree core key (ForsSchedule.selected md ⟨tree.val, by omega⟩) before := by
        apply readTree_preserved valid core sk key md ⟨tree.val, by omega⟩ ⟨count, by omega⟩
          (by
            intro same
            have values := congrArg Fin.val same
            change tree.val = count at values
            omega)
          before final reachable
      apply congrArg pure
      apply Prod.ext
      · dsimp only
        simp only [readPrefix]
        rw [Vector.ofFn_succ]
        exact congrArg (fun f : Fin count → ForsTreeSigCore p core =>
          (Vector.ofFn f).push (readTree core key (ForsSchedule.selected md ⟨count, by omega⟩)
              final))
          (funext fun tree => (prior tree).symm)
      · rfl

private def readSignature (md : List Byte) (key : ForsKey p) (memory : Memory core) :
    ForsSigCore p core :=
  Vector.ofFn fun tree : Fin p.k =>
    readTree core key (ForsSchedule.selected md tree) memory

/-- Full canonical FORS signature and memory agree with the actual signing schedule. -/
private theorem raw_forest_joint (sk : core.Y) (md : List Byte)
    (key : ForsKey p) (memory : Memory core) :
    (simulateQ (rawRecorded core) (nativeProgram core sk md key)).run memory =
    (fun final => (readSignature core md key final, final)) <$>
      RandomOracleTraversal.evaluate (naturalInput valid core sk) (naturalAssign core)
        (ForsSchedule.signing key md) memory := by
  rw [nativeProgram_treeProgram]
  simpa only [forestPrefix, schedulePrefix, readPrefix, slotSchedule,
    ForsSchedule.signing, readSignature] using
      (raw_forest_prefix_joint valid core sk md key p.k le_rfl memory)


private theorem erase_raw {Result : Type} (computation : OracleComp (NativeSpec core) Result)
    (memory : Memory core) :
    Prod.fst <$> (simulateQ (rawRecorded core) computation).run memory = computation := by
  have step (label : (NativeSpec core).Domain) (initial : Memory core) :
      Prod.map id (fun _ : Memory core => PUnit.unit) <$> (rawRecorded core label).run initial =
        ((QueryImpl.id' (NativeSpec core)).liftTarget
          (StateT PUnit (OracleComp (NativeSpec core))) label).run PUnit.unit := by
    rw [rawRecorded_run]
    simp only [Functor.map_map, QueryImpl.liftTarget_apply,
      liftM_run_StateT, QueryImpl.id'_apply, bind_pure_comp]
    rfl
  have same := run'_simulateQ_eq_of_query_map_eq (rawRecorded core)
    ((QueryImpl.id' (NativeSpec core)).liftTarget (StateT PUnit (OracleComp (NativeSpec core))))
    (fun _ : Memory core => PUnit.unit) step computation memory
  simpa only [StateT.run'_eq, simulateQ_liftTarget, liftM_run_StateT,
    bind_pure_comp, Functor.map_map, Function.comp_def, id_map', simulateQ_id'] using same

private theorem natural_projection (seedValue : core.Y) (nodes : List (StructuralNode p))
    (memory : Memory core) :
    project core seedValue <$>
      RandomOracleTraversal.evaluate (naturalInput valid core seedValue) (naturalAssign core)
          nodes memory =
        RandomOracleTraversal.evaluate (StructuralNode.input valid)
          updateCell nodes (project core seedValue memory) := by
  induction nodes generalizing memory with
  | nil => simp [RandomOracleTraversal.evaluate]
  | cons node nodes ih =>
      simp only [RandomOracleTraversal.evaluate, map_bind]
      change ((query (spec := NativeSpec core) (naturalInput valid core seedValue node memory) :
        OracleComp (NativeSpec core) core.Y) >>= _) = _
      apply congrArg (Bind.bind (query (spec := NativeSpec core)
        (naturalInput valid core seedValue node memory) : OracleComp (NativeSpec core) core.Y))
      funext answer
      rw [ih]
      exact congrArg (RandomOracleTraversal.evaluate (StructuralNode.input valid)
        updateCell nodes) (project_update core seedValue answer memory node)

/-- The callback-based FORS signer executes the exact ordered structural traversal.
The explicit provider queries its natural address with the supplied seed value; all nonseed
initial cells and all digest lists are unrestricted. -/
theorem forsSignWithSecret_eq_evaluate (p : Params) (valid : p.Valid)
    (core : CorePrimitives p) (seedValue : core.Y) (key : ForsKey p) (md : List Byte)
    (cells : Node p → core.Y) (sameSeed : cells .secretSeed = seedValue) :
    forsSignWithSecret core
      (fun address value => query (spec := (Adrs × List core.Y) →ₒ core.Y) (address, [value]))
      (fun address left right =>
        query (spec := (Adrs × List core.Y) →ₒ core.Y) (address, [left, right]))
      (fun address => query (spec := (Adrs × List core.Y) →ₒ core.Y) (address, [seedValue]))
      md key.address =
      reconstruct core key md <$>
        RandomOracleTraversal.evaluate (StructuralNode.input valid) updateCell
          (ForsSchedule.signing key md) cells := by
  have joint := congrArg (fun computation => Prod.fst <$> computation)
    (raw_forest_joint valid core seedValue md key (extendCells core cells))
  rw [erase_raw] at joint
  simp only [Functor.map_map] at joint
  have reconstruction : (fun memory : Memory core =>
      reconstruct core key md (project core seedValue memory)) =
        readSignature core md key := rfl
  rw [← reconstruction, ← Functor.map_map, natural_projection] at joint
  have initial : project core seedValue (extendCells core cells) = cells := by
    rw [← sameSeed]
    exact project_extend core cells
  rw [initial] at joint
  exact joint

/-- Interpreting the structural traversal gives the same existing FORS body in any lawful
monad, with the same ordered natural-label handler and explicit seed provider. -/
theorem forsSignWithSecret_eq_simulateQ_evaluate (p : Params) (valid : p.Valid)
    (core : CorePrimitives p) (seedValue : core.Y) (key : ForsKey p) (md : List Byte)
    (cells : Node p → core.Y) (sameSeed : cells .secretSeed = seedValue)
    (m : Type → Type u) [Monad m] [LawfulMonad m]
    (hash : QueryImpl ((Adrs × List core.Y) →ₒ core.Y) m) :
    forsSignWithSecret core (fun address value => hash (address, [value]))
      (fun address left right => hash (address, [left, right]))
      (fun address => hash (address, [seedValue])) md key.address =
      reconstruct core key md <$>
        simulateQ hash (RandomOracleTraversal.evaluate (StructuralNode.input valid) updateCell
          (ForsSchedule.signing key md) cells) := by
  have natural := forsSignWithSecret_natural core (simulateQ' hash)
    (fun address value => query (spec := (Adrs × List core.Y) →ₒ core.Y) (address, [value]))
    (fun address value => hash (address, [value]))
    (fun address left right =>
      query (spec := (Adrs × List core.Y) →ₒ core.Y) (address, [left, right]))
    (fun address left right => hash (address, [left, right]))
    (fun address => query (spec := (Adrs × List core.Y) →ₒ core.Y) (address, [seedValue]))
    (fun address => hash (address, [seedValue]))
    (fun _ _ => simulateQ_spec_query _ _) (fun _ _ _ => simulateQ_spec_query _ _)
    (fun _ _ => simulateQ_spec_query _ _) md key.address
  change simulateQ hash _ = _ at natural
  rw [forsSignWithSecret_eq_evaluate p valid core seedValue key md cells sameSeed,
    simulateQ_map] at natural
  exact natural.symm

end SLHDSA.Graph.Fors
