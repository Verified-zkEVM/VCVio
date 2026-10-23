/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ChargedProbe
public import HashSig.SLHDSA.SHAKE128s.Proof.LazyBridge
public import HashSig.SLHDSA.SHAKE128s.Proof.AddressBounds

/-!
# A cell a run cannot read may be drawn after it

`evalDist_redraw_coordinate` says that if altering one coordinate of the cell table leaves a
run's law alone, then the joint law of the run's result and that coordinate is the law of the
result together with an *independently* drawn cell: the coordinate may be redrawn.
`evalDist_uniformSample_bind_update` is what makes it short: a uniform table is a uniform table
with one coordinate overwritten by a fresh uniform value, so the overwriting value can be
substituted for the coordinate everywhere and then commuted past the run.

The file also holds the game's cache bookkeeping (`unionCache`, the programmed entries with
whatever the handler has drawn beside them) and the congruences saying that an honest FORS
signature reads only the cells it discloses.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.RedrawCell

open CanonicalGraph SensitiveQuery

/-- **A coordinate a run cannot read may be redrawn.** -/
theorem evalDist_redraw_coordinate {γ Aux : Type} (index : CanonicalGraph.Node)
    (auxiliary : ProbComp Aux) (run : Cells → Aux → ProbComp γ)
    (hcongr : ∀ (cells other : Cells) (aux : Aux),
      (∀ node, node ≠ index → cells node = other node) →
        𝒟[run cells aux] = 𝒟[run other aux]) :
    𝒟[do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let aux ← auxiliary
        let result ← run cells aux
        pure (result, cells index)] =
      𝒟[do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let aux ← auxiliary
        let result ← run cells aux
        let cell ← ($ᵗ Cell : ProbComp Cell)
        pure (result, cell)] := by
  classical
  have hupdate := evalDist_uniformSample_bind_update
    (D := CanonicalGraph.Node) (R := Cell) index
  calc 𝒟[do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let aux ← auxiliary
        let result ← run cells aux
        pure (result, cells index)]
      = 𝒟[(do
            let cell ← ($ᵗ Cell : ProbComp Cell)
            let cells ← ($ᵗ Cells : ProbComp Cells)
            pure (Function.update cells index cell)) >>= fun cells => do
          let aux ← auxiliary
          let result ← run cells aux
          pure (result, cells index)] :=
        (LazyBridge.evalDist_bind_congr_right hupdate _).symm
    _ = 𝒟[do
          let cell ← ($ᵗ Cell : ProbComp Cell)
          let cells ← ($ᵗ Cells : ProbComp Cells)
          let aux ← auxiliary
          let result ← run (Function.update cells index cell) aux
          pure (result, cell)] := by
        simp only [bind_assoc, pure_bind, Function.update_self]
    _ = 𝒟[do
          let cell ← ($ᵗ Cell : ProbComp Cell)
          let cells ← ($ᵗ Cells : ProbComp Cells)
          let aux ← auxiliary
          let result ← run cells aux
          pure (result, cell)] := by
        refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun cell => ?_
        refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun cells => ?_
        refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun aux => ?_
        refine LazyBridge.evalDist_bind_congr_right ?_ _
        exact hcongr _ _ aux fun node hnode => Function.update_of_ne hnode _ _
    _ = 𝒟[do
          let cells ← ($ᵗ Cells : ProbComp Cells)
          let cell ← ($ᵗ Cell : ProbComp Cell)
          let aux ← auxiliary
          let result ← run cells aux
          pure (result, cell)] :=
        OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
    _ = 𝒟[do
          let cells ← ($ᵗ Cells : ProbComp Cells)
          let aux ← auxiliary
          let cell ← ($ᵗ Cell : ProbComp Cell)
          let result ← run cells aux
          pure (result, cell)] := by
        refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun cells => ?_
        exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
    _ = _ := by
        refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun cells => ?_
        refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun aux => ?_
        exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _

open ChargedProbe

variable {Target : Type}

open OpenCache ChargedProbe

/-! ## The programmed cache read on demand

At total availability the handler serves exactly the entries the walk programmed, so at every
moment the game's cache is the programmed entries with whatever the handler has drawn beside
them. `unionCache` is that cache; the relation is an equation, not a coupling. -/

open scoped Classical in
/-- At total availability every node is open. -/
theorem openNodes_total :
    OpenCache.openNodes (fun _ => True) = CanonicalGraph.Programming.order := by
  simp [OpenCache.openNodes]

open scoped Classical in
/-- **At total availability the readable entries are the whole programmed cache** — the one the
walk leaves behind. -/
theorem openCache_total (publicSeed : Digest) (table : Cells × Padding) :
    openCache publicSeed (fun _ => True) table =
      CanonicalGraph.Programming.cacheFrom publicSeed table.1
        (CanonicalGraph.fullOutput table.1 table.2) CanonicalGraph.Programming.order ∅ := by
  rw [openCache, openNodes_total]

/-! ## The walk's own table

`WarmedGame.mem_support_graphWalk` hands the walk's cache as a programmed table over an
arbitrary output table; the handler wants a cells-and-padding pair. `Programming.splitTable` is
the bijection between the two, and the match is a reindexing along it. The secret seed is where
a mismatch would sit, and there is none: the bijection puts it in the table's own `secretSeed`
cell and leaves it there. -/

/-- **Every cells-and-padding pair is a seed and an output table.** -/
theorem splitTable_fullOutput (table : Cells × Padding) :
    CanonicalGraph.Programming.splitTable
        (table.1 CanonicalGraph.Node.secretSeed,
          CanonicalGraph.fullOutput table.1 table.2) = table := by
  refine Prod.ext (funext fun node => ?_) (funext fun parent => ?_)
  · cases node with
    | secretSeed => rfl
    | structural parent => exact CanonicalGraph.truncate_fullOutput _ _ _
  · exact BitVec.extractLsb'_append_eq_right

/-- The programmed entries, with whatever the handler has drawn beside them. -/
noncomputable def unionCache (publicSeed : Digest) (table : Cells × Padding)
    (cache : QueryCache HashSpec) : QueryCache HashSpec :=
  fun input =>
    match openCache publicSeed (fun _ => True) table input with
    | some answer => some answer
    | none => cache input

theorem unionCache_of_open (publicSeed : Digest) (table : Cells × Padding)
    (cache : QueryCache HashSpec) (input : Bytes) (answer : HashOutput)
    (hopen : openCache publicSeed (fun _ => True) table input = some answer) :
    unionCache publicSeed table cache input = some answer := by
  rw [unionCache, hopen]

/-- **The cells the union cache computes are the table's own.** The programmed entries answer
every canonical input, so replaying the graph through this cache returns the cells it was
programmed from — whatever else the handler has drawn beside them. -/
theorem replayCells_unionCache (publicSeed : Digest) (table : Cells × Padding)
    (cache : QueryCache HashSpec) :
    HonestProbes.replayCells (unionCache publicSeed table cache)
        (table.1 CanonicalGraph.Node.secretSeed) publicSeed = table.1 := by
  have hvalue := @CanonicalGraph.Programming.value_eq_of_cache_agreement
    (CacheReplay.replayQuery (unionCache publicSeed table cache)) publicSeed
    (table.1 CanonicalGraph.Node.secretSeed)
    (CanonicalGraph.fullOutput table.1 table.2)
    (fun input output hentry => by
      refine CacheReplay.hash_replayQuery (unionCache publicSeed table cache) input output ?_
      refine unionCache_of_open publicSeed table cache input output ?_
      rw [openCache_total]
      rw [show CanonicalGraph.Programming.cellsOfOutputs (table.1 CanonicalGraph.Node.secretSeed)
          (CanonicalGraph.fullOutput table.1 table.2) = table.1 from
        congrArg Prod.fst (splitTable_fullOutput table)] at hentry
      exact hentry)
  rw [HonestProbes.replayCells, hvalue,
    show CanonicalGraph.Programming.cellsOfOutputs (table.1 CanonicalGraph.Node.secretSeed)
        (CanonicalGraph.fullOutput table.1 table.2) = table.1 from
      congrArg Prod.fst (splitTable_fullOutput table)]

/-! ## What a signature reads, as a congruence

The statements here are congruences rather than a separate cell-reading signer: change the table
only away from the cells a signature discloses and the signature does not move. -/

/-- The nodes an honest FORS signature discloses: the secret at each selected leaf, and the
sibling at each level of its authentication path. -/
def ForsDiscloses (key : ForsKey) (indices : Fors.Indices) : CanonicalGraph.Node → Prop :=
  fun node =>
    (∃ tree, node = .structural (HonestProbes.forsSecretNode key indices tree)) ∨
      ∃ tree level, node = .structural (HonestProbes.forsAuthNode key indices tree level)

/-- Two FORS tree signatures agree when their fields do. -/
theorem forsTreeSignature_eq {left right : ForsTreeSignature}
    (hsecret : left.secret = right.secret)
    (hauth : left.authentication = right.authentication) : left = right := by
  cases left
  cases right
  simp_all

/-- **An honest FORS signature reads only the cells it discloses.** -/
theorem fors_sign_congr (publicSeed : Digest) (cache : QueryCache HashSpec)
    (left right : Cells × Padding) (key : ForsKey) (indices : Fors.Indices)
    (hagree : ∀ node, ForsDiscloses key indices node → left.1 node = right.1 node) :
    @Fors.sign Id _ (CacheReplay.replayQuery (unionCache publicSeed left cache)) indices
        (left.1 CanonicalGraph.Node.secretSeed) publicSeed key.address =
      @Fors.sign Id _ (CacheReplay.replayQuery (unionCache publicSeed right cache)) indices
        (right.1 CanonicalGraph.Node.secretSeed) publicSeed key.address := by
  funext tree
  refine forsTreeSignature_eq ?_ (funext fun level => ?_)
  · rw [HonestProbes.fors_sign_secret_cell, HonestProbes.fors_sign_secret_cell,
      replayCells_unionCache, replayCells_unionCache]
    exact hagree _ (Or.inl ⟨tree, rfl⟩)
  · rw [HonestProbes.fors_sign_authentication_cell, HonestProbes.fors_sign_authentication_cell,
      replayCells_unionCache, replayCells_unionCache]
    exact hagree _ (Or.inr ⟨tree, level, rfl⟩)

/-- Two XMSS signatures agree when their fields do. -/
theorem xmssSignature_eq {left right : XmssSignature} (hwots : left.wots = right.wots)
    (hauth : left.authentication = right.authentication) : left = right := by
  cases left
  cases right
  simp_all

/-- The cells the union cache computes, one node at a time. -/
theorem value_unionCache (publicSeed : Digest) (table : Cells × Padding)
    (cache : QueryCache HashSpec) (node : CanonicalGraph.Node) :
    @CanonicalGraph.value (CacheReplay.replayQuery (unionCache publicSeed table cache))
        (table.1 CanonicalGraph.Node.secretSeed) publicSeed node = table.1 node :=
  congrFun (replayCells_unionCache publicSeed table cache) node

/-- Two signatures built part by part agree when the parts do. Stated over six variables on
purpose: applying it is first-order, so nothing ever asks the unifier to walk into two large
terms that differ only inside a handler instance. -/
theorem signature_mk_eq {randomizerLeft randomizerRight : Digest}
    {forsLeft forsRight : ForsSignature}
    {hypertreeLeft hypertreeRight : HypertreeSignature}
    (hrandom : randomizerLeft = randomizerRight) (hfors : forsLeft = forsRight)
    (hhypertree : hypertreeLeft = hypertreeRight) :
    Signature.mk randomizerLeft forsLeft hypertreeLeft =
      Signature.mk randomizerRight forsRight hypertreeRight := by
  rw [hrandom, hfors, hhypertree]

end SlhDsaSecurity.RedrawCell
