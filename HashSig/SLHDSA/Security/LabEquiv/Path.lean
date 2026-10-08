/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.LabScheme
public import VCVio.OracleComp.SimSemantics.StateT.EqDistTriple.Simulate
import ToMathlib.Data.List.Forall2

/-!
# Honest and lab steps in the eager game

In the eager game `(slhGraph core pkSeed).eagerImpl`, the honest SLH-DSA programs over
`labSpec core` (the secret-free programs with every secret value read by `labSecret`) and the lab
programs of `HashSig.SLHDSA.Security.LabScheme` have equal distributions, step for step, when the
state records the values the honest program hashes. `LabTriple core pkSeed P oa ob Q` is the
equal-distribution triple (`QueryImpl.EqDistTriple`) of two programs over `labSpec core` in that
game, along the growth `≤` of the state; its postcondition is on the lab program `ob`.

The relation between a value and the state is `CellHolds core st c y`: the optional cell `c` (a
derivation or a node label) exists and is drawn at `y`. This file proves the triples of single
steps and of hash paths.

* **A node step** (`tl_labTriple`). At a ledger address `a`, from a state in which the cells of
  the structural children of `a` hold the inputs `xs`, the honest tweakable hash
  `PublicHash.tl core pkSeed a xs` is the public query at the point of the node of `a` at its
  drawn children values, which the relabelled game answers by drawing the node's label; the lab
  program reads that label. Both runs are the same draw, and the node's cell then holds the
  output. This uses the key discipline: the children of the node at the key of `a` are those of
  `a` (`CorePrimitives.KeyDiscipline.slhGraph_ch_of_nodeKeyOf_eq_some`). At an address with one
  or two structural children the step is `F` or `H` (`f_labTriple`, `h_labTriple`), from a state
  in which the children's cells hold its inputs.
* **A secret read** (`labSecret_labTriple`) draws the derivation at the secret's key.
* **WOTS+ chains.** `chainWith_labTriple` runs `s` honest `F` steps against `s` lab steps from any
  input held by chain cell `j` (`wotsChainCell`); the result is held by chain cell `j + s`. In the
  eager game the lab chain `labChain`, a touch-then-read, reads the secret and every step and
  keeps the last value (`simulateQ_eagerImpl_labChain`), so a chain from its secret is related to
  `labChain` (`labChain_labTriple`).
* **FORS leaves.** The lab leaf `labForsLeaf` reads the secret and the leaf in the eager game
  (`simulateQ_eagerImpl_labForsLeaf`), so the honest leaf from its secret is related to it
  (`labForsLeaf_labTriple`).
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.Security

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

/-! ## The state relation -/

/-- The optional cell `c` exists and holds `y` in the state `st`. -/
@[expose] def CellHolds (st : LabState core) (c : Option (DeriveQuery core ⊕ NodeKey core))
    (y : core.Y) : Prop :=
  ∃ c', c = some c' ∧ st.2 c' = some y

variable {core} in
/-- An existing cell holds `y` exactly when it is drawn at `y`. -/
@[simp]
theorem cellHolds_some_iff {st : LabState core} {c : DeriveQuery core ⊕ NodeKey core}
    {y : core.Y} : CellHolds core st (some c) y ↔ st.2 c = some y := by
  simp [CellHolds]

variable {core} in
/-- A held cell stays held as the state grows. -/
theorem CellHolds.mono {st st' : LabState core} (hle : st ≤ st')
    {c : Option (DeriveQuery core ⊕ NodeKey core)} {y : core.Y} (h : CellHolds core st c y) :
    CellHolds core st' c y :=
  h.imp fun _ h' ↦ ⟨h'.1, hle.2 h'.2⟩

/-! ## WOTS+ chain cells -/

/-- The cells of WOTS+ chain `i` at `adrs`: cell `0` holds the secret and cell `j + 1` the value
after hash step `j`. The lab chain `labChain core adrs i s` is a touch-then-read along them. -/
abbrev wotsChainCell (adrs : Adrs) (i : ℕ) : ℕ → Option (DeriveQuery core ⊕ NodeKey core) :=
  pathCell core (wotsSkAdrs adrs i) ((wotsChainAdrs adrs i).setHashAddress ·)

/-- The single structural child of hash step `j` of a WOTS+ chain is chain cell `j`. -/
theorem map_childCell_childAdrs_wotsChainAdrs (adrs : Adrs) (i j : ℕ) :
    (childAdrs vp ((wotsChainAdrs adrs i).setHashAddress j)).map (childCell core) =
      [wotsChainCell core adrs i j] := by
  rcases j with _ | j
  · rw [childAdrs_wotsChainAdrs_setHashAddress_zero]
    rfl
  · rw [childAdrs_wotsChainAdrs_setHashAddress_succ]
    rfl

/-! ## Triples in the eager game -/

variable [SampleableType core.Y] [DecidableEq core.Y] [DecidableEq core.PkSeed]
  [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf] [SampleableType (Bytes vp.params.m)]

/-- Two programs over `labSpec core` related in the eager game of the canonical graph at
`pkSeed`, along the growth of the state: an equal-distribution triple of their simulations, with
the postcondition on `ob`. -/
abbrev LabTriple (pkSeed : core.PkSeed) {α : Type} (P : LabState core → Prop)
    (oa ob : OracleComp (labSpec core) α) (Q : α → LabState core → Prop) : Prop :=
  (slhGraph core pkSeed).eagerImpl.EqDistTriple (· ≤ ·) P oa ob Q

/-- Every program is related to itself, with any precondition and no postcondition. -/
theorem labTriple_refl (pkSeed : core.PkSeed) {α : Type} (P : LabState core → Prop)
    (oa : OracleComp (labSpec core) α) : LabTriple core pkSeed P oa oa fun _ _ ↦ True :=
  QueryImpl.EqDistTriple.refl_of_step
    (fun _ _ _ ↦ (slhGraph core pkSeed).le_of_mem_support_eagerImpl) oa

/-- **The node step.** At a ledger address `a`, from a state in which the cells of the structural
children of `a` hold `xs`, the honest tweakable hash `T(PK.seed, a, xs)` and the lab read of the
node at `a` are one draw of the node's label, which its cell then holds. -/
theorem tl_labTriple (hd : core.KeyDiscipline vp) (pkSeed : core.PkSeed) {a : Adrs}
    (ha : a ∈ constructionAddresses vp) (xs : List core.Y) :
    LabTriple core pkSeed
      (fun st ↦ List.Forall₂ (CellHolds core st) ((childAdrs vp a).map (childCell core)) xs)
      (PublicHash.tl core pkSeed a xs) (labNode core a)
      fun y st ↦ CellHolds core st (childCell core (.inr a)) y := by
  intro st hst
  let κ : NodeKey core := ⟨core.adrsToKey a, a, ha, rfl⟩
  have hch : (slhGraph core pkSeed).childVals st κ = some xs := by
    rw [CanonicalGraph.childVals_eq_some_iff,
      hd.slhGraph_ch_of_nodeKeyOf_eq_some pkSeed (nodeKeyOf_of_mem core ha)]
    exact List.forall₂_filterMap_of_forall₂ (List.forall₂_map_left_iff.1 hst)
  have hlab : (simulateQ (slhGraph core pkSeed).eagerImpl (labNode core a)).run st =
      (RelabelState.drawCell (.inr κ)).run st := by
    rw [labNode_of_mem core ha, CanonicalGraph.eagerImpl_readCell_run]
  have hhon : (simulateQ (slhGraph core pkSeed).eagerImpl
      (PublicHash.tl core pkSeed a xs : OracleComp (labSpec core) core.Y)).run st =
        (RelabelState.drawCell (.inr κ)).run st := by
    rw [PublicHash.tl, HasQuery.instOfMonadLift_query, simulateQ_liftM_query]
    refine (congrArg (StateT.run · st) (id_map _)).trans ?_
    refine ((slhGraph core pkSeed).relabelImpl_run_pt hch).trans ?_
    exact id_map _
  refine ⟨fun {_} ↦ by rw [hhon, hlab], fun z hz ↦ ?_⟩
  rw [hlab] at hz
  obtain ⟨hle, hc⟩ := RelabelState.le_and_cell_eq_of_mem_support_drawCell hz
  exact ⟨hle, _, childCell_inr core ha, hc⟩

/-- **A one-input step.** At a ledger address `a` with a single structural child, whose cell is
`c`, from a state in which `c` holds `x`, the honest `F(PK.seed, a, x)` and the lab `F` are one
draw of the node's label, which its cell then holds. -/
theorem f_labTriple (hd : core.KeyDiscipline vp) (pkSeed : core.PkSeed) {a : Adrs}
    (ha : a ∈ constructionAddresses vp) {c : Option (DeriveQuery core ⊕ NodeKey core)}
    (hch : (childAdrs vp a).map (childCell core) = [c]) (x : core.Y) :
    LabTriple core pkSeed (fun st ↦ CellHolds core st c x)
      (PublicHash.f core pkSeed a x) (labF core a x)
      fun y st ↦ CellHolds core st (childCell core (.inr a)) y :=
  (tl_labTriple core hd pkSeed ha [x]).mono (fun _ h ↦ hch ▸ .cons h .nil) fun _ _ h ↦ h

/-- **A two-input step.** At a ledger address `a` with two structural children, whose cells are
`c₁` and `c₂`, from a state in which they hold `l` and `r`, the honest `H(PK.seed, a, l, r)` and
the lab `H` are one draw of the node's label, which its cell then holds. -/
theorem h_labTriple (hd : core.KeyDiscipline vp) (pkSeed : core.PkSeed) {a : Adrs}
    (ha : a ∈ constructionAddresses vp) {c₁ c₂ : Option (DeriveQuery core ⊕ NodeKey core)}
    (hch : (childAdrs vp a).map (childCell core) = [c₁, c₂]) (l r : core.Y) :
    LabTriple core pkSeed (fun st ↦ CellHolds core st c₁ l ∧ CellHolds core st c₂ r)
      (PublicHash.h core pkSeed a l r) (labH core a l r)
      fun y st ↦ CellHolds core st (childCell core (.inr a)) y :=
  (tl_labTriple core hd pkSeed ha [l, r]).mono (fun _ h ↦ hch ▸ .cons h.1 (.cons h.2 .nil))
    fun _ _ h ↦ h

/-- **The secret read.** At a secret-key address the lab secret draws the derivation at its key,
which its cell then holds. -/
theorem labSecret_labTriple (pkSeed : core.PkSeed) {a : Adrs} (ha : a.IsSecretKey) :
    LabTriple core pkSeed (fun _ ↦ True) (labSecret core a) (labSecret core a)
      fun y st ↦ CellHolds core st (childCell core (.inl a)) y := by
  refine QueryImpl.EqDistTriple.of_support fun st _ z hz ↦ ?_
  rw [labSecret_of_isSecretKey core ha, CanonicalGraph.eagerImpl_readCell_run] at hz
  obtain ⟨hle, hc⟩ := RelabelState.le_and_cell_eq_of_mem_support_drawCell hz
  exact ⟨hle, _, childCell_inl core ha, hc⟩

/-! ## WOTS+ chains -/

/-- **Chain steps.** From a state in which chain cell `j` holds `x`, `s` honest `F` steps and `s`
lab steps of a WOTS+ chain of a reachable instance, with `j + s ≤ w - 1`, are related, and chain
cell `j + s` then holds the result. -/
theorem chainWith_labTriple (hd : core.KeyDiscipline vp) (pkSeed : core.PkSeed)
    (pos : LayerPosition vp) (i : Fin vp.params.len) (x : core.Y) (j : ℕ) :
    ∀ s, j + s ≤ vp.params.w - 1 →
      LabTriple core pkSeed
        (fun st ↦ CellHolds core st (wotsChainCell core (wotsInstanceAdrs pos) i j) x)
        (chainWith (PublicHash.f core pkSeed) (wotsChainAdrs (wotsInstanceAdrs pos) i) x j s)
        (chainWith (labF core) (wotsChainAdrs (wotsInstanceAdrs pos) i) x j s)
        fun y st ↦ CellHolds core st (wotsChainCell core (wotsInstanceAdrs pos) i (j + s)) y
  | 0, _ => QueryImpl.EqDistTriple.pure x fun _ h ↦ h
  | s + 1, hs => by
    simp only [chainWith]
    refine (chainWith_labTriple hd pkSeed pos i x j s (by omega)).bind fun y ↦ ?_
    exact f_labTriple core hd pkSeed
      (wotsChainAdrs_setHashAddress_mem_constructionAddresses pos i (t := j + s) (by omega))
      (map_childCell_childAdrs_wotsChainAdrs core _ i _) y

variable (G : CanonicalGraph (hashSpec core) (DeriveQuery core) (NodeKey core) core.Y)

/-- In the eager game the lab chain reads the secret and every hash step of the chain, through
the lab `F`, and returns the last value. -/
theorem simulateQ_eagerImpl_labChain (adrs : Adrs) (i : ℕ) :
    ∀ s, simulateQ G.eagerImpl (labChain core adrs i s) =
      simulateQ G.eagerImpl (do
        let x ← labSecret core (wotsSkAdrs adrs i)
        chainWith (labF core) (wotsChainAdrs adrs i) x 0 s)
  | 0 => by
    simp only [labChain, touchRead, touchUpTo, pure_bind, chainWith, bind_pure,
      labSecret_of_isSecretKey core (Adrs.isSecretKey_wotsSkAdrs adrs i),
      pathCell_zero core (Adrs.isSecretKey_wotsSkAdrs adrs i)]
  | s + 1 => by
    rw [labChain, G.simulateQ_eagerImpl_touchRead_succ, ← labChain,
      simulateQ_eagerImpl_labChain adrs i s]
    simp only [chainWith, simulateQ_bind, bind_assoc, Nat.zero_add]
    rfl

/-- **A chain from its secret.** For a chain of a reachable instance and `s ≤ w - 1`, the honest
chain of `s` steps from the secret is related to the lab chain, and chain cell `s` then holds the
result. -/
theorem labChain_labTriple (hd : core.KeyDiscipline vp) (pkSeed : core.PkSeed)
    (pos : LayerPosition vp) (i : Fin vp.params.len) {s : ℕ} (hs : s ≤ vp.params.w - 1) :
    LabTriple core pkSeed (fun _ ↦ True)
      (do
        let x ← labSecret core (wotsSkAdrs (wotsInstanceAdrs pos) i)
        chainWith (PublicHash.f core pkSeed) (wotsChainAdrs (wotsInstanceAdrs pos) i) x 0 s)
      (labChain core (wotsInstanceAdrs pos) i s)
      fun y st ↦ CellHolds core st (wotsChainCell core (wotsInstanceAdrs pos) i s) y := by
  refine QueryImpl.EqDistTriple.of_simulateQ_eq_right ?_
    (simulateQ_eagerImpl_labChain core _ _ _ s).symm
  refine (labSecret_labTriple core pkSeed (Adrs.isSecretKey_wotsSkAdrs _ _)).bind fun x ↦ ?_
  exact (chainWith_labTriple core hd pkSeed pos i x 0 s (by omega)).mono (fun _ h ↦ h)
    fun _ _ h ↦ by rwa [Nat.zero_add] at h

/-! ## FORS leaves -/

/-- In the eager game the lab FORS leaf reads the leaf's secret and then the leaf, through the lab
`F`. -/
theorem simulateQ_eagerImpl_labForsLeaf (adrs : Adrs) (t : ℕ) :
    simulateQ G.eagerImpl (labForsLeaf core adrs t) =
      simulateQ G.eagerImpl (do
        let x ← labSecret core (forsSkAdrs adrs t)
        labF core (forsNodeAdrs adrs 0 t) x) := by
  rw [labForsLeaf, G.simulateQ_eagerImpl_touchRead_succ]
  simp only [touchRead, touchUpTo, pure_bind, simulateQ_bind,
    labSecret_of_isSecretKey core (Adrs.isSecretKey_forsSkAdrs adrs t),
    pathCell_zero core (Adrs.isSecretKey_forsSkAdrs adrs t)]
  rfl

/-- **A FORS leaf.** For a leaf of tree `tree` at a reachable bottom position, the honest leaf from
its secret is related to the lab leaf, and the leaf's cell then holds the result. -/
theorem labForsLeaf_labTriple (hd : core.KeyDiscipline vp) (pkSeed : core.PkSeed)
    (pos : BottomPosition vp) (tree : Fin vp.params.k) {i : ℕ}
    (hi : i / 2 ^ vp.params.a = tree.val) :
    LabTriple core pkSeed (fun _ ↦ True)
      (forsLeafWithSecret core (PublicHash.f core pkSeed) (labSecret core) pos.forsAdrs i)
      (labForsLeaf core pos.forsAdrs i)
      fun y st ↦ CellHolds core st (childCell core (.inr (forsNodeAdrs pos.forsAdrs 0 i))) y := by
  refine QueryImpl.EqDistTriple.of_simulateQ_eq_right ?_
    (simulateQ_eagerImpl_labForsLeaf core _ _ _).symm
  refine (labSecret_labTriple core pkSeed (Adrs.isSecretKey_forsSkAdrs _ _)).bind fun x ↦ ?_
  exact f_labTriple core hd pkSeed (forsLeafAdrs_mem_constructionAddresses pos tree hi)
    (by rw [childAdrs_forsNodeAdrs_zero]; rfl) x

end SLHDSA.Security
