/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CanonicalGraph.Children
public import HashSig.SLHDSA.SHAKE128s.Proof.CanonicalGraph.Correspondence

/-!
# Why a sensitive query costs one unit and not several

The input half charges one event: the adversary queries the canonical input of a node one of
whose children's cells the signatures so far do not make available. A canonical input is
`PK.seed ‖ ADRS ‖ (its children's cells)`, so the address says which node, and the query
matches only if its payload reproduces that node's children exactly. If a node had *two*
children the signatures withhold, the adversary would have to match both — harmless — but if a
node had two children of which only one is withheld in some runs and the other in others, the
rate would be a union over the possibilities rather than a single `2 ^ -128`.

The budget allows exactly two units of `2 ^ -129` for this event, so the rate has to be
`2 ^ -128` on the nose. That is a fact about the shape of the graph, proved here and
independent of what "available" ends up meaning: **every node either has only children whose
cells no signature can withhold, or has exactly one child.**

The cells the charge has to protect are the secret seed, the WOTS chain values *below* the
endpoint, and the FORS secrets. A chain's endpoint is excluded, and the reason is not that no
run could fail to hold it — a WOTS key nobody ever signed with reveals none of its chain — but
that the charge never needs it: what a hypertree fault leaves in the adversary's hands is a
chain value strictly below the revealed digit, hence strictly below `w - 1`, and the queries
that could have produced it are at lower positions still. Excluding the endpoint is what keeps
`wotsPk`, with its `chains` children, on the harmless side. Merkle and FORS tree nodes collect
tree cells and `forsRoots` collects tree roots, which are public outright.
-/

@[expose] public section

namespace SlhDsaSecurity.CanonicalGraph

/-- The cells the input half does not have to protect: everything except the secret seed, a
WOTS chain value strictly below the endpoint, and a FORS secret. -/
def AlwaysAvailable : Node → Prop
  | .secretSeed => False
  | .structural (.wotsPrf _ _) => False
  | .structural (.wotsHash _ _ step) => step.val = w - 2
  | .structural (.forsPrf _ _) => False
  | .structural (.wotsPk _) => True
  | .structural (.tree _ _ _) => True
  | .structural (.forsTree _ _ _) => True
  | .structural (.forsRoots _) => True

/-- A Merkle node is a subtree node or a WOTS public key, never a protected cell. -/
theorem alwaysAvailable_merkleNode (tree : Tree) (height : Nat) (hheight : height ≤ subtreeHeight)
    (index : Fin (2 ^ (subtreeHeight - height))) :
    AlwaysAvailable (.structural (merkleNode tree height hheight index)) := by
  rw [merkleNode]
  split <;> exact True.intro

/-- A Merkle child is a subtree node or a WOTS public key, never a protected cell. -/
theorem alwaysAvailable_merkleChild (tree : Tree) (height : Fin subtreeHeight)
    (index : Fin (2 ^ (subtreeHeight - (height.val + 1)))) (side : Fin 2) :
    AlwaysAvailable (.structural (merkleChild tree height index side)) := by
  rw [merkleChild, merkleNode]
  split <;> exact True.intro

/-- **Every node has only unprotected children, or exactly one child.** -/
theorem children_alwaysAvailable_or_singleton (parent : StructuralNode) :
    (∀ child ∈ parent.children, AlwaysAvailable child) ∨
      ∃ child : Node, parent.children = [child] := by
  cases parent with
  | wotsPrf key chain => exact Or.inr ⟨.secretSeed, rfl⟩
  | wotsHash key chain step =>
    refine Or.inr ?_
    rw [StructuralNode.children]
    split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  | wotsPk key =>
    refine Or.inl fun child hchild => ?_
    rw [StructuralNode.children, List.mem_ofFn] at hchild
    obtain ⟨chain, rfl⟩ := hchild
    exact rfl
  | tree location height index =>
    refine Or.inl fun child hchild => ?_
    rw [StructuralNode.children] at hchild
    rcases List.mem_cons.mp hchild with rfl | hchild
    · exact alwaysAvailable_merkleChild location height index 0
    · rw [List.mem_singleton] at hchild
      subst hchild
      exact alwaysAvailable_merkleChild location height index 1
  | forsPrf key index => exact Or.inr ⟨.secretSeed, rfl⟩
  | forsTree key height index =>
    rw [StructuralNode.children]
    split
    · exact Or.inr ⟨_, rfl⟩
    · refine Or.inl fun child hchild => ?_
      rcases List.mem_cons.mp hchild with rfl | hchild
      · exact True.intro
      · rw [List.mem_singleton] at hchild
        subst hchild
        exact True.intro
  | forsRoots key =>
    refine Or.inl fun child hchild => ?_
    rw [StructuralNode.children, List.mem_ofFn] at hchild
    obtain ⟨tree, rfl⟩ := hchild
    exact True.intro

/-! ## Availability, and the corollary the rate rests on

`AlwaysAvailable` is the part that does not depend on the run. The rest does: a WOTS chain
value is available once the signature on that key reveals its chain at or below that position,
and a FORS secret once some signing request selected it.

Both are left abstract here — the revealed digit as a function of key and chain, the signed
positions as a function of FORS key — because only one property of them matters for the rate,
and it is the obvious one: a digit never exceeds `w - 1`, so a chain's endpoint is always
available. Whoever instantiates supplies the honest message each WOTS key signs and the signing
log; nothing below needs to know what they are.

What comes out is the corollary the charge consumes: a *sensitive* node — one with a child the
signatures do not make available — has exactly one child, so a query at its address puts
exactly one cell at stake. -/

variable (revealed : WotsKey → Fin chains → Nat)
    (signed : ForsKey → Finset (Fin (forsTrees * 2 ^ forsHeight)))

/-- The cells the signatures issued so far make available. -/
def Available : Node → Prop
  | .secretSeed => False
  | .structural (.wotsPrf key chain) => revealed key chain = 0
  | .structural (.wotsHash key chain step) => revealed key chain ≤ step.val + 1
  | .structural (.forsPrf key index) => index ∈ signed key
  | .structural (.wotsPk _) => True
  | .structural (.tree _ _ _) => True
  | .structural (.forsTree _ _ _) => True
  | .structural (.forsRoots _) => True

/-- A node the signatures leave a child of unavailable. -/
def Sensitive (parent : StructuralNode) : Prop :=
  ∃ child ∈ parent.children, ¬ Available revealed signed child

/-- An unprotected cell is available, whatever the signatures were — the only thing the rate
needs of the revealed digits being that a digit never exceeds `w - 1`. -/
theorem available_of_alwaysAvailable (hrevealed : ∀ key chain, revealed key chain ≤ w - 1)
    {child : Node} (halways : AlwaysAvailable child) : Available revealed signed child := by
  cases child with
  | secretSeed => exact halways.elim
  | structural parent =>
    cases parent with
    | wotsPrf key chain => exact halways.elim
    | wotsHash key chain step =>
      show revealed key chain ≤ step.val + 1
      rw [show step.val = w - 2 from halways]
      exact le_trans (hrevealed key chain) (by omega)
    | forsPrf key index => exact halways.elim
    | wotsPk key => exact True.intro
    | tree location height index => exact True.intro
    | forsTree key height index => exact True.intro
    | forsRoots key => exact True.intro

/-! ## What a hypertree fault leaves unavailable

The reduction of a hypertree fault ends with the forgery holding the chain value at some
position strictly below the digit that key's honest message encodes — `WotsResidueReduction`
names the key, the chain and the position, and `heldValue_eq_cell` identifies the value with
the cell of `wotsPosition`. This says that cell is one the signatures do not make available,
which is what puts the fault inside the charged event.

Position zero is the PRF-derived secret, available only when the revealed digit is zero;
position `p + 1` is `wotsHash` at step `p`, available only when the revealed digit is at most
`p + 1`. Below the revealed digit, neither holds. -/

/-- **A chain value below the revealed digit is unavailable.** -/
theorem not_available_wotsPosition (key : WotsKey) (chain : Fin chains) (position : Fin w)
    (hbelow : position.val < revealed key chain) :
    ¬ Available revealed signed (.structural (wotsPosition key chain position)) := by
  rw [wotsPosition]
  split
  · rename_i hzero
    show ¬ revealed key chain = 0
    omega
  · rename_i hzero
    show ¬ revealed key chain ≤ position.val - 1 + 1
    omega

/-! ## Availability is closed under the structure

A charge on sensitive queries is worth nothing without this, and the counterexample is short.
Suppose some node `c` were *not* sensitive — every cell its canonical input mentions is
available — and yet `c`'s own cell were unavailable. A run may query `c` outright, read its
cell off the answer, and from then on form the canonical input of the node above `c` at will.
That node is sensitive for the rest of the run, so a sensitive query happens with probability
one and no per-query bound survives.

So the charge needs availability *closed*: a node all of whose children are available has an
available cell. In this graph it holds, and the proof is a case check — every node with an
unavailable cell has an unavailable child. Reading it the other way round: the only way to
reach a protected cell is through a sensitive query, which is what makes the charge the first
place a run can get one. -/

/-- **A node whose children are all available has an available cell.** -/
theorem available_of_children_available {parent : StructuralNode}
    (hchildren : ∀ child ∈ parent.children, Available revealed signed child) :
    Available revealed signed (.structural parent) := by
  cases parent with
  | wotsPrf key chain =>
    exact (hchildren .secretSeed (by rw [StructuralNode.children]; exact List.mem_singleton_self _)
      : Available revealed signed .secretSeed).elim
  | wotsHash key chain step =>
    show revealed key chain ≤ step.val + 1
    rw [StructuralNode.children] at hchildren
    split at hchildren
    · rename_i hzero
      have := hchildren _ (List.mem_singleton_self _)
      show revealed key chain ≤ step.val + 1
      have hprf : revealed key chain = 0 := this
      omega
    · rename_i hzero
      have := hchildren _ (List.mem_singleton_self _)
      have hhash : revealed key chain ≤ step.val - 1 + 1 := this
      omega
  | wotsPk key => exact True.intro
  | tree location height index => exact True.intro
  | forsPrf key index =>
    exact (hchildren .secretSeed (by rw [StructuralNode.children]; exact List.mem_singleton_self _)
      : Available revealed signed .secretSeed).elim
  | forsTree key height index => exact True.intro
  | forsRoots key => exact True.intro

end SlhDsaSecurity.CanonicalGraph
