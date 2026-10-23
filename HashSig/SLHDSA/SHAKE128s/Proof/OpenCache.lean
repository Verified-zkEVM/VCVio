/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.StalledRun
public import HashSig.SLHDSA.SHAKE128s.Proof.HandlerCarrier
public import HashSig.SLHDSA.SHAKE128s.Proof.SensitiveShape
public import HashSig.SLHDSA.SHAKE128s.Proof.CanonicalGraph.Programming

/-!
# The handler that answers only what a run may legitimately compute

The charge of `SensitiveQuery` is stated for a run that does not read the cells it is charged
against, and `StalledRun` reduces that to a per-step condition demanded only while the cell in
question is still unavailable. This file supplies the handler that condition is about.

It answers every query with a fresh uniform value, except at the canonical input of a node all
of whose children's cells the signatures make available, which it answers from the table. That
is the most a run may legitimately learn, and `CanonicalGraph.available_of_children_available`
is why it is not more: such a node's own cell is available too, so the answer discloses nothing
the signatures had not already disclosed. The entries it may serve are collected in
`openCache`, which is `CanonicalGraph.Programming.cacheFrom` over the nodes that pass that
test, so the existing lookup and shape lemmas apply to it unchanged.

Two things about the table are easy to get wrong.

* **It is cells *and padding*.** An available node's canonical input is answered with the full
  thirty-byte value, of which only the first sixteen are the node's cell; the other fourteen are
  independent padding. So the thing a run must be blind to is a pair, and `AgreeOff` below is a
  relation on that pair — agreement off one coordinate means agreement on that coordinate's
  cell *and* on that node's padding.
* **A probe names at most one cell.** `SensitiveQuery.Stakes.locate` reads the node off the
  address before any cell is consulted, so the events "this probe is charged against cell `i`"
  are disjoint as `i` ranges over the cells. The sum over cells is therefore a sum over disjoint
  events and contributes one unit per *probe*. Read the other way — stall at each cell, bound at
  each cell, add — it would come to `|Index| · q / 2 ^ 128` and the whole approach would
  collapse.

`openCache_congr_of_agreeOff` is the per-step condition in the form `StalledRun` consumes: at a
state where cell `i` is unavailable, the entries this handler may serve do not mention `i`.
-/

@[expose] public section

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.OpenCache

open CanonicalGraph CanonicalGraph.Programming

/-! ## Two programmed caches that agree -/

/-- Programming the same nodes from tables that give them the same inputs and the same answers
gives the same cache. -/
theorem cacheFrom_congr (publicSeed : Digest) (leftCells rightCells : Cells)
    (leftOutputs rightOutputs : Outputs) (parents : List StructuralNode)
    (cache : QueryCache HashSpec)
    (hkeys : ∀ parent ∈ parents,
      canonicalInput publicSeed leftCells parent = canonicalInput publicSeed rightCells parent)
    (hvalues : ∀ parent ∈ parents, leftOutputs parent = rightOutputs parent) :
    cacheFrom publicSeed leftCells leftOutputs parents cache =
      cacheFrom publicSeed rightCells rightOutputs parents cache := by
  induction parents generalizing cache with
  | nil => rfl
  | cons current rest ih =>
    rw [cacheFrom, cacheFrom, hkeys current (by simp), hvalues current (by simp)]
    exact ih _ (fun other hother => hkeys other (by simp [hother]))
      (fun other hother => hvalues other (by simp [hother]))

/-! ## The entries a run may legitimately read -/

variable (publicSeed : Digest) (available : Node → Prop)

open scoped Classical in
/-- The nodes all of whose children's cells the signatures make available. -/
noncomputable def openNodes : List StructuralNode :=
  Programming.order.filter (fun parent => decide (∀ child ∈ parent.children, available child))

open scoped Classical in
theorem mem_openNodes (parent : StructuralNode) :
    parent ∈ openNodes available ↔ ∀ child ∈ parent.children, available child := by
  rw [openNodes, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨Programming.mem_order parent, h⟩⟩

open scoped Classical in
/-- **The entries a run may legitimately read**: the canonical inputs of those nodes, with
their full thirty-byte answers. -/
noncomputable def openCache (table : Cells × Padding) : QueryCache HashSpec :=
  cacheFrom publicSeed table.1 (fullOutput table.1 table.2) (openNodes available) ∅

/-! ## Blindness to one cell

Two tables agreeing everywhere but at one coordinate — its cell and that node's padding — give
the same readable entries, provided that coordinate is unavailable. The keys mention only the
children's cells, which are available; the values mention only the node's own cell, which
`available_of_children_available` makes available too, and its padding. -/

/-- Two tables agreeing off one coordinate: the same cells everywhere else, and the same
padding at every node but that one. -/
def AgreeOff (index : Node) (left right : Cells × Padding) : Prop :=
  (∀ other, other ≠ index → left.1 other = right.1 other) ∧
    ∀ parent : StructuralNode, Node.structural parent ≠ index → left.2 parent = right.2 parent

/-- **The readable entries do not mention an unavailable cell.** -/
theorem openCache_congr_of_agreeOff
    (hclosed : ∀ parent : StructuralNode,
      (∀ child ∈ parent.children, available child) → available (.structural parent))
    (index : Node) (hindex : ¬ available index) (left right : Cells × Padding)
    (hagree : AgreeOff index left right) :
    openCache publicSeed available left = openCache publicSeed available right := by
  classical
  have hne : ∀ other, available other → other ≠ index := fun other hother heq =>
    hindex (heq ▸ hother)
  refine cacheFrom_congr publicSeed _ _ _ _ _ ∅ (fun parent hparent => ?_)
    (fun parent hparent => ?_)
  · refine canonicalInput_congr publicSeed _ _ parent fun child hchild => ?_
    exact hagree.1 child (hne child ((mem_openNodes available parent).mp hparent child hchild))
  · have hcell : available (Node.structural parent) :=
      hclosed parent ((mem_openNodes available parent).mp hparent)
    rw [fullOutput, fullOutput, hagree.1 _ (hne _ hcell), hagree.2 parent (hne _ hcell)]

/-! ## Two availability predicates differ only at the sensitive inputs

The comparison a lazy presentation needs against an eager one is between this handler at the
real availability and the same handler at total availability — the one that answers every
canonical input, which is the eager programmed cache read on demand. They differ at exactly the
canonical inputs of the nodes the real availability calls sensitive, and nowhere else: a
candidate that is not a canonical input is in neither, and a canonical input of a node whose
children are all available is in both with the same answer.

Closure is not what makes this true; it is what makes the handler blind to the unavailable
cells. This is the plainer fact that the readable entries are determined by which nodes pass
the test. -/

open scoped Classical in
/-- **A non-canonical input is not among the entries a handler may serve.** The entries are
keyed by canonical inputs, so anything of another shape — a randomiser's, a message digest's —
falls through to whatever else is answering. -/
theorem openCache_eq_none_of_not_canonical (table : Cells × Padding) (input : Bytes)
    (hnot : ∀ parent : StructuralNode, canonicalInput publicSeed table.1 parent ≠ input) :
    openCache publicSeed available table input = none := by
  classical
  by_contra hsome
  obtain ⟨parent, hparent⟩ := cacheFrom_empty_canonical publicSeed table.1
    (fullOutput table.1 table.2) (openNodes available) input hsome
  exact hnot parent hparent.symm

/-! ## The handler

Its state is the cache, the inputs it has been asked for with the cache each was asked
against, and the number of queries charged — the same shape the charge records,
so the charge consumes it unchanged. The only new behaviour is that a miss at a readable input
is answered from the table rather than drawn. -/

/-- The cache, the probes with the cache each was issued against, and the charged count. -/
abbrev HandlerState := HandlerCarrier.State × List (Bytes × HandlerCarrier.State) × Nat

open scoped Classical in
/-- **The handler.** Fresh uniform everywhere, except at an input the run may legitimately
read, which is answered from the table. -/
noncomputable def lazyProgram (availableAt : HandlerCarrier.State → Node → Prop)
    (table : Cells × Padding) : QueryImpl OracleWorld (StateT HandlerState ProbComp) :=
  fun queried state =>
    match queried with
    | Sum.inl coin => do
        let value ← ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _)
        pure (value, state)
    | Sum.inr input => do
        let step ←
          (match state.1.cache input with
            | some cached => (pure (cached, state.1) : ProbComp _)
            | none =>
              match openCache publicSeed (availableAt state.1) table input with
              | some answer => pure (answer, HandlerCarrier.cacheAnswer state.1 input answer)
              | none =>
                (fun answer => (answer, HandlerCarrier.cacheAnswer state.1 input answer)) <$>
                  ($ᵗ HashOutput : ProbComp HashOutput))
        pure (step.1, (step.2, state.2.1 ++ [(input, state.1)], state.2.2 + 1))

end SlhDsaSecurity.OpenCache
