/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.SensitiveQuery
public import HashSig.SLHDSA.SHAKE128s.Proof.SensitiveShape
public import HashSig.SLHDSA.SHAKE128s.Proof.CollisionToDeviating
public import HashSig.SLHDSA.SHAKE128s.Proof.Extraction.HypertreeChain
public import HashSig.SLHDSA.SHAKE128s.Proof.Extraction.Fors
public import HashSig.SLHDSA.SHAKE128s.Proof.CacheReplay

/-!
# The canonical graph as a stakes structure

`SensitiveQuery` charges a query at a node one of whose children's cells is unavailable, against
an abstract `Stakes` structure: a node type, the canonical input as a function of the one cell at
stake, a way to read the node back off a candidate input, and the cell that child contributes.
This file builds that structure for the canonical graph, and discharges the closure condition
the charge is worthless without.

Three choices make it fit.

* **The node type carries its own singleton witness.** `Stakes` needs `inputOf` to take exactly
  one cell, and a bare `StructuralNode` with two children has no single cell at stake. So the
  node is a structural node bundled with a proof that it has exactly one child, which is where
  the single-unavailable-child hypothesis is spent rather than assumed.
* **`locate` needs no parser.** `CanonicalGraph.canonicalInput_eq_iff` already says the address
  determines the node and the payload determines the children's cells, so reading the node back
  is a choice from the (unique) preimage rather than a byte-level parse.
* **The closure graph is a different graph.** A run computes a node's cell from *all* of that
  node's children, sensitive or not, so `Graph` is built on bare `StructuralNode` while `Stakes`
  is built on the bundled one. `SensitiveQuery` keeps the two apart for exactly this reason.

The revealed digit is instantiated concretely. Each WOTS key of the hypertree signs exactly one
message and that message is a function of the key and the seeds alone — the honest node one
layer down, or at the bottom layer the honest FORS public key at that leaf — so the digit each
key discloses is fixed before the adversary runs. Nothing about it waits on the signing log,
which is what lets the WOTS clause be read off the walk. The FORS side is the opposite and stays
a function of the state.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.GraphStakes

open CanonicalGraph SensitiveQuery

/-! ## The node a sensitive query names

`SensitiveQuery.Stakes` wants a node type on which `stake` is total and `inputOf` takes exactly
one cell. A bare `StructuralNode` is neither: a node with two children has no single cell at
stake. So the node type carries its own witness of having exactly one child, which is where the
whole single-unavailable-child hypothesis is spent. -/

/-- A structural node together with the single child a sensitive node has. -/
structure SensitiveNode where
  /-- The node itself. -/
  parent : StructuralNode
  /-- Its only child. -/
  child : Node
  /-- Having only that child. -/
  children_eq : parent.children = [child]

/-- Two sensitive nodes with the same structural node are equal: the child is determined by the
node's children list. -/
theorem SensitiveNode.ext {left right : SensitiveNode} (hparent : left.parent = right.parent) :
    left = right := by
  obtain ⟨leftParent, leftChild, leftEq⟩ := left
  obtain ⟨rightParent, rightChild, rightEq⟩ := right
  cases hparent
  cases List.head_eq_of_cons_eq (leftEq.symm.trans rightEq)
  rfl

variable (publicSeed : Digest)

/-- The canonical input of a sensitive node, as a function of the one cell at stake. -/
@[expose] def inputOf (node : SensitiveNode) (cell : Cell) : Bytes :=
  Hashing.tweakableInput publicSeed node.parent.address (bytesBE n cell)

/-- It is the node's canonical input, with the staked cell taking that value. -/
theorem inputOf_eq_canonicalInput (node : SensitiveNode) (cells : Cells) :
    inputOf publicSeed node (cells node.child) =
      canonicalInput publicSeed cells node.parent := by
  rw [inputOf, canonicalInput, node.children_eq, CollisionToDeviating.childBytes_single]

/-- **A candidate input determines both the node and the cell**: the address is in the clear
and so is the payload. -/
theorem inputOf_inj {left right : SensitiveNode} {leftCell rightCell : Cell}
    (hinput : inputOf publicSeed left leftCell = inputOf publicSeed right rightCell) :
    left = right ∧ leftCell = rightCell := by
  obtain ⟨-, haddress, hpayload⟩ := Hashing.tweakableInput_injective hinput
  exact ⟨SensitiveNode.ext (StructuralNode.address_injective haddress),
    bytesBE_injective n hpayload⟩

open scoped Classical in
/-- The node a candidate input's address names, if any. -/
@[expose] noncomputable def locate (input : Bytes) : Option SensitiveNode :=
  if hsome : ∃ node : SensitiveNode, ∃ cell : Cell, inputOf publicSeed node cell = input
    then some hsome.choose else none

/-- `locate` reads a canonical input's node back. -/
theorem locate_inputOf (node : SensitiveNode) (cell : Cell) :
    locate publicSeed (inputOf publicSeed node cell) = some node := by
  classical
  have hsome : ∃ other : SensitiveNode, ∃ value : Cell,
      inputOf publicSeed other value = inputOf publicSeed node cell := ⟨node, cell, rfl⟩
  rw [locate, dite_eq_left hsome]
  obtain ⟨value, hvalue⟩ := hsome.choose_spec
  exact congrArg some (inputOf_inj publicSeed hvalue).1

/-- **The canonical graph, as the charge's stakes structure.** -/
@[expose] noncomputable def stakes : Stakes SensitiveNode Node where
  inputOf := inputOf publicSeed
  locate := locate publicSeed
  stake := SensitiveNode.child
  locate_inputOf := locate_inputOf publicSeed
  inputOf_injective := fun _ _ _ hinput => (inputOf_inj publicSeed hinput).2

/-! ## Availability, and its closure

The graph the closure condition speaks about is the whole structure, not only its sensitive
part: a run computes a node's cell from *all* of that node's children, sensitive or not. So the
two structures have different node types, which is why `SensitiveQuery` keeps `Stakes` and
`Graph` apart. -/

/-- The structure availability has to be closed under. -/
@[expose] def graph : Graph StructuralNode Node where
  cellOf := fun parent => .structural parent
  children := fun parent index => index ∈ parent.children

variable {State : Type} (revealed : WotsKey → Fin chains → Nat)
    (signedAt : State → ForsKey → Finset (Fin (forsTrees * 2 ^ forsHeight)))

/-- The cells the signatures issued by a given state do not make available. -/
@[expose] def unavailableAt (state : State) (index : Node) : Prop :=
  ¬ Available revealed (signedAt state) index

/-- **Availability is closed under the structure.** -/
theorem closed : Closed graph (unavailableAt revealed signedAt) := by
  classical
  intro state parent hchildren hbad
  exact hbad (available_of_children_available revealed (signedAt state)
    fun child hchild => not_not.mp (hchildren child hchild))

/-- **Nothing a run can compute from the available cells is unavailable.** The instance of
`SensitiveQuery.not_unavailable_of_obtainable` at this graph: the only way to an unavailable
cell is a query at a sensitive node. -/
theorem not_unavailable_of_obtainable (state : State) {index : Node}
    (hobtain : Obtainable graph (fun other => ¬ unavailableAt revealed signedAt state other)
      index) :
    Available revealed (signedAt state) index := by
  classical
  exact not_not.mp
    (SensitiveQuery.not_unavailable_of_obtainable graph (unavailableAt revealed signedAt)
      (closed revealed signedAt) state hobtain)

/-! ## The digit each hypertree key reveals

Each WOTS key of the hypertree signs exactly one message, and that message is a function of the
key and the seeds alone: the honest node one layer down, or — at the bottom layer — the honest
FORS public key at that leaf. So the revealed digit is fixed before the adversary runs, which is
what lets the WOTS clause be read off the walk rather than off the signing log. -/

section HonestDigit

variable [HasQuery HashSpec Id]

/-- The message the honest key at `key` signs. -/
@[expose] def honestMessage (secretSeed publicSeed : Digest) (key : WotsKey) : Digest :=
  match key.tree.layer.val with
  | 0 => value secretSeed publicSeed (.structural (.forsRoots ⟨key.tree.tree, key.leaf⟩))
  | layer + 1 => Extraction.HypertreeChain.honestNode secretSeed publicSeed layer
      (key.tree.tree.val * 2 ^ subtreeHeight + key.leaf.val)

/-- The digit that message encodes on a chain: the position the signature on this key
discloses. -/
@[expose]
def honestRevealed (secretSeed publicSeed : Digest) (key : WotsKey) (chain : Fin chains) : Nat :=
  (Checksum.encode (honestMessage secretSeed publicSeed key) chain).val

/-- A revealed digit never exceeds `w - 1`, which is the only thing the rate needs of it. -/
theorem honestRevealed_le (secretSeed publicSeed : Digest) :
    ∀ (key : WotsKey) (chain : Fin chains),
      honestRevealed secretSeed publicSeed key chain ≤ w - 1 := by
  intro key chain
  have := (Checksum.encode (honestMessage secretSeed publicSeed key) chain).isLt
  simp only [honestRevealed, w, winternitzBits] at this ⊢
  omega

end HonestDigit

/-- **The chain value a signature discloses is available.** The position it opens is the digit
the key's own message encodes, and that digit is what `revealed` records — so the cell at that
position is one the signature has made available, whether it is the chain's start or a value
along it.

The message is the *key's own*, not the forgery's. Read with the wrong one the statement still
typechecks and says nothing: a position the forgery would open need not be one any signature
discloses. -/
theorem available_wotsPosition (revealed : WotsKey → Fin chains → Nat)
    (signed : ForsKey → Finset (Fin (forsTrees * 2 ^ forsHeight)))
    (key : WotsKey) (chain : Fin chains) (position : Fin w)
    (hposition : position.val = revealed key chain) :
    CanonicalGraph.Available revealed signed
      (.structural (CanonicalGraph.wotsPosition key chain position)) := by
  rw [CanonicalGraph.wotsPosition]
  split
  · rename_i hzero
    change revealed key chain = 0
    omega
  · rename_i hzero
    change revealed key chain ≤ (position.val - 1) + 1
    omega

/-! ## The FORS disclosure is coverage or a sensitive query

The split's third branch says the forgery holds the honest FORS secret at every position its
digest selects. A FORS secret is available exactly when its index is in the signed set, so
position by position there are only two possibilities: the signing log selected that index — the
coverage event — or the cell is unavailable, and then by the closure it is not obtainable
either, so the run reached it by a query at a sensitive node.

Nothing here decides which; it is the honest statement of the fork. -/

/-- **An unsigned FORS secret is not obtainable.** -/
theorem not_obtainable_forsPrf (state : State) (key : ForsKey)
    (index : Fin (forsTrees * 2 ^ forsHeight)) (hunsigned : index ∉ signedAt state key) :
    ¬ Obtainable graph (fun other => ¬ unavailableAt revealed signedAt state other)
      (.structural (.forsPrf key index)) := fun hobtain =>
  hunsigned (not_unavailable_of_obtainable revealed signedAt state hobtain)

/-- The position a FORS tree's selected leaf sits at, as a graph index. -/
@[expose] def forsIndex (indices : SLHDSA.SHAKE128s.Fors.Indices) (tree : Fin forsTrees) :
    Fin (forsTrees * 2 ^ forsHeight) :=
  ⟨Extraction.Fors.leafIndex indices tree, by
    have htree := tree.isLt
    have hleaf := (indices tree).isLt
    have hstep : tree.val * 2 ^ forsHeight + (indices tree).val <
        (tree.val + 1) * 2 ^ forsHeight := by
      rw [Nat.succ_mul]
      omega
    exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right _ htree)⟩

/-- **The FORS disclosure, position by position: signed, or not obtainable.** -/
theorem forsSecret_signed_or_not_obtainable (cache : QueryCache HashSpec)
    (secretSeed : Digest) (key : ForsKey) (indices : SLHDSA.SHAKE128s.Fors.Indices)
    (signature : ForsSignature) (state : State)
    (hsecrets : ∀ tree : Fin forsTrees, (signature tree).secret =
      @SLHDSA.SHAKE128s.Fors.secret Id Id.instMonad (CacheReplay.replayQuery cache)
        secretSeed publicSeed key.address (Extraction.Fors.leafIndex indices tree))
    (tree : Fin forsTrees) :
    (signature tree).secret =
        @value (CacheReplay.replayQuery cache) secretSeed publicSeed
          (.structural (.forsPrf key (forsIndex indices tree))) ∧
      (forsIndex indices tree ∈ signedAt state key ∨
        ¬ Obtainable graph (fun other => ¬ unavailableAt revealed signedAt state other)
          (.structural (.forsPrf key (forsIndex indices tree)))) := by
  classical
  refine ⟨(hsecrets tree).trans (@fors_secret_cell (CacheReplay.replayQuery cache) secretSeed
    publicSeed key (forsIndex indices tree)), ?_⟩
  by_cases hsigned : forsIndex indices tree ∈ signedAt state key
  · exact Or.inl hsigned
  · exact Or.inr (not_obtainable_forsPrf revealed signedAt state key _ hsigned)

/-! ## The forgery's own claimed cells, as candidates

Nothing turns a run's transcript into `Obtainable`, and nothing needs to. A forgery that claims
a value for a cell contributes a candidate of its own: `inputOf node value`, which by `inputOf`'s
injectivity in the cell is the node's canonical input exactly when the claimed value is the one
the table gives. So "the forgery holds the unavailable cell" is the same event as "this
candidate is sensitive", and recording the claims alongside the queries charges both at once.

The two shapes of claim are a chain value and a FORS secret, and the nodes above them have
exactly one child whether or not they are sensitive — a chain step's child is the position below
it, a FORS leaf's child is its secret — so the candidates are built unconditionally. -/

/-- The chain-step node above a chain position, which always has exactly one child. -/
@[expose]
def wotsHashNode (key : WotsKey) (chain : Fin chains) (step : Fin (w - 1)) : SensitiveNode :=
  ⟨.wotsHash key chain step,
    .structural (wotsPosition key chain ⟨step.val, by have := step.isLt; omega⟩),
    by by_cases hzero : step.val = 0 <;>
      simp [StructuralNode.children, wotsPosition, hzero]⟩

/-! ### The stake is one position lower than the probe

`wotsHashNode key chain step` sits at the chain step whose address is `step`, and its single
child is `wotsPosition key chain step`, the cell that step *reads*, not the one it writes. So a
probe at a chain step stakes the position being guessed, and the honest signer, walking a chain
from its start up to the digit it reveals, stakes exactly the positions it is walking through
and has not yet revealed. Every one of them is unavailable, so no test on availability can drop
the honest phase's probes from a charge; they are kept out by stripping instead.

The witness that the probes are really made is `WotsEntry.queriesUnder_chain`: every step of a
chain consults its canonical input at the chain's own partial value. -/

/-- The FORS leaf node above a FORS secret, which always has exactly one child. -/
@[expose]
def forsLeafNode (key : ForsKey) (index : Fin (forsTrees * 2 ^ forsHeight)) : SensitiveNode :=
  ⟨.forsTree key ⟨0, by omega⟩ ⟨index.val, by simp [index.isLt]⟩,
    .structural (.forsPrf key index), by
      rw [StructuralNode.children, dite_eq_left rfl]⟩

/-- **A claim at an unavailable cell is a sensitive candidate.** -/
theorem sensitive_inputOf (node : SensitiveNode) (table : Cells) (state : State) (value : Cell)
    (hunavailable : unavailableAt revealed signedAt state node.child)
    (hvalue : value = table node.child) :
    SensitiveQuery.Sensitive (stakes publicSeed) (unavailableAt revealed signedAt) table state
      (inputOf publicSeed node value) :=
  ⟨node, hunavailable, by rw [hvalue]; rfl⟩

/-- **A chain value the forgery claims below the revealed digit is a sensitive candidate.** -/
theorem sensitive_wotsClaim (table : Cells) (state : State) (key : WotsKey)
    (chain : Fin chains) (step : Fin (w - 1)) (value : Cell)
    (hbelow : step.val < revealed key chain)
    (hvalue : value = table (.structural (wotsPosition key chain
      ⟨step.val, by have := step.isLt; omega⟩))) :
    SensitiveQuery.Sensitive (stakes publicSeed) (unavailableAt revealed signedAt) table state
      (inputOf publicSeed (wotsHashNode key chain step) value) :=
  sensitive_inputOf publicSeed revealed signedAt _ table state value
    (not_available_wotsPosition revealed (signedAt state) key chain _ hbelow) hvalue

/-- **A FORS secret the forgery claims at an unsigned position is a sensitive candidate.** -/
theorem sensitive_forsClaim (table : Cells) (state : State) (key : ForsKey)
    (index : Fin (forsTrees * 2 ^ forsHeight)) (value : Cell)
    (hunsigned : index ∉ signedAt state key)
    (hvalue : value = table (.structural (.forsPrf key index))) :
    SensitiveQuery.Sensitive (stakes publicSeed) (unavailableAt revealed signedAt) table state
      (inputOf publicSeed (forsLeafNode key index) value) :=
  sensitive_inputOf publicSeed revealed signedAt _ table state value hunsigned hvalue

/-! ## The record the charge takes

One candidate per claimed cell: the fourteen FORS secrets the signature reveals, and one WOTS
value per layer and chain. The position each WOTS value sits at is the digit that layer's
message encodes, which the residue reduction supplies; it is a parameter here so that the list
is a function of the forgery alone. Its length is a constant — `forsTrees + layers * chains`,
which is `259` — not a function of the budget, which is what makes it affordable. -/

/-- One candidate per cell the forgery claims. -/
@[expose] def claimedCandidates (forsKey : ForsKey) (indices : SLHDSA.SHAKE128s.Fors.Indices)
    (signature : Signature) (keyAt : Fin layers → WotsKey)
    (stepAt : Fin layers → Fin chains → Fin (w - 1)) : List Bytes :=
  (List.finRange forsTrees).map (fun tree =>
      inputOf publicSeed (forsLeafNode forsKey (forsIndex indices tree))
        (signature.fors tree).secret) ++
    (List.finRange layers).flatMap fun layer =>
      (List.finRange chains).map fun chain =>
        inputOf publicSeed (wotsHashNode (keyAt layer) chain (stepAt layer chain))
          ((signature.hypertree layer).wots chain)

end SLHDSA.SHAKE128s.GraphStakes
