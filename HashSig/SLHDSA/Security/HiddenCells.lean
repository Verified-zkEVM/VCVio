/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.LabScheme
public import HashSig.SLHDSA.Security.RomDescentSecret
public import VCVio.OracleComp.QueryTracking.RandomOracle.ReadSet
import all HashSig.SLHDSA.Security.NodeGraph
import HashSig.SLHDSA.Security.AddressKeys

/-!
# Hidden cells of the SLH-DSA graph

A relabelled state `st` over the SLH-DSA graph `slhGraph core pkSeed` draws cells: derivations,
among them the WOTS+ and FORS secrets, and node labels. Given a set `U` of `H_msg` digests, the
digests of the signatures issued so far, some of these cells are *hidden*: no signature on a
digest of `U` reveals them.

* **WOTS+ chains** (`HiddenChainStep`). Step `t` of chain `i` of the WOTS+ instance at a
  hypertree position `pos` is the value `t` hash steps above the chain's secret; its structural
  child is `chainChild pos i t`, the secret at `t = 0` and the hash step at hash address `t - 1`
  above. The step is hidden when `t < w - 1` and, if some digest of `U` uses `pos`
  (`UsedPosition`), `t` is below the step that the drawn honest message at `pos` selects on chain
  `i`. The honest message at `pos` is the label of the node at `msgAdrs pos` (`msgCell`); while it
  is undrawn, every step below the top of a used position is hidden. The top step `w - 1` is never
  hidden.
* **FORS secrets.** The secret of a FORS coordinate is hidden when no digest of `U` opens it
  (`OpenedCoord`).

`HiddenChild U st` is the set of hidden structural children and `hiddenCells U st` the set of
their cells. The digests of a transcript are its `SignedDigest`s: the `H_msg` digests, held in
the public cache, of the logged messages and their randomizers. `HiddenUndrawn pk log st` states
that no hidden cell of the signed digests of `log` is drawn in `st`.

* **Monotonicity** (`hiddenCells_anti`). More digests and a larger state hide fewer cells: using a
  position or opening a coordinate only reveals, and a drawn label never changes.
* **Down-closure** (`HiddenChainStep.of_le`). Below a hidden chain step every step is hidden. A
  public query draws the label of a node only when its children are drawn, and the only child of
  hash step `t` is step `t - 1`, so a public query never draws a hidden cell over a state where
  the hidden cells are undrawn (`hiddenUndrawn_of_mem_support_deferredImpl`).
* **Reading unhidden children** (`not_mem_hiddenCells_of_childCell_eq_some`). Under the key
  discipline distinct in-range structural children have distinct cells, so the cell of an
  in-range child that is not hidden is not a hidden cell. The tops of the chains and every node
  of another type (`not_hiddenChild_inr`), the chain steps at and above the selected step of a
  used position (`not_hiddenChild_chainChild`), and the opened FORS secrets
  (`not_hiddenChild_inl_forsSkAdrs`) are not hidden.
* **The forgery's replay.** Read off a cache with the `H_msg` entries of the state, the used
  leaves of `HashSig.SLHDSA.Security.RomDescentSecret` are used positions
  (`usedPosition_of_usedLeaf`), its unopened coordinates are not opened
  (`not_openedCoord_of_unopenedCoord`), and a chain value hidden at a larger state is a hidden
  chain step (`hiddenChainStep_of_le`), whose cell is a hidden cell
  (`mem_hiddenCells_of_hiddenChainStep`, `mem_hiddenCells_forsSkAdrs`).

## References

- NIST FIPS 205, Algorithms 6–8 (WOTS+), 15–17 (FORS), 19 (`H_msg` and the digest split)
-/

public section

namespace SLHDSA.Security

open OracleComp OracleSpec

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

/-! ## Signed digests, used positions and opened coordinates -/

/-- `d` is the `H_msg` digest, held in the public cache `C` at the public key `pk`, of a logged
message and its randomizer. -/
@[expose] def SignedDigest (pk : PublicKeyCore core)
    (log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp core))
    (C : (hashSpec core).QueryCache) (d : Bytes vp.params.m) : Prop :=
  ∃ e ∈ log, C (.inl (.hmsg e.2.randomness pk.pkSeed pk.pkRoot e.1)) = some d

variable {core}

/-- A larger log and a larger public cache sign every digest a smaller one signs. -/
theorem SignedDigest.mono {pk : PublicKeyCore core}
    {log log' : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp core)}
    {C C' : (hashSpec core).QueryCache} (hlog : ∀ e ∈ log, e ∈ log') (hC : C ≤ C')
    {d : Bytes vp.params.m} (h : SignedDigest core pk log C d) : SignedDigest core pk log' C' d :=
  let ⟨e, he, hd⟩ := h
  ⟨e, hlog e he, hC hd⟩

/-- Some digest of `U` places its hypertree position at the layer of `pos` at `pos`. -/
@[expose] def UsedPosition (U : Bytes vp.params.m → Prop) (pos : LayerPosition vp) : Prop :=
  ∃ d, U d ∧ LayerPosition.atLayer vp (splitDigest vp.params d) pos.layer = pos

/-- Some digest of `U` opens the FORS coordinate with instance address `adrs` and global leaf
index `t`. -/
@[expose] def OpenedCoord (U : Bytes vp.params.m → Prop) (adrs : Adrs) (t : ℕ) : Prop :=
  ∃ d, U d ∧ ∃ i : Fin vp.params.k, (splitDigest vp.params d).forsAdrs = adrs ∧
    forsSigLeafIndex vp.params (splitDigest vp.params d).md.toList i.val = t

/-- A position used by the digests of `U` is used by every larger set of digests. -/
theorem UsedPosition.mono {U U' : Bytes vp.params.m → Prop} (hU : ∀ d, U d → U' d)
    {pos : LayerPosition vp} (h : UsedPosition U pos) : UsedPosition U' pos :=
  let ⟨d, hd, hpos⟩ := h
  ⟨d, hU d hd, hpos⟩

/-- The position one layer above a used position is used. -/
theorem UsedPosition.next {U : Bytes vp.params.m → Prop} {pos : LayerPosition vp}
    (h : UsedPosition U pos) (hn : pos.layer.val + 1 < vp.params.d) :
    UsedPosition U (pos.next hn) := by
  obtain ⟨d, hd, hpos⟩ := h
  refine ⟨d, hd, ?_⟩
  rw [show (pos.next hn).layer = ⟨pos.layer.val + 1, hn⟩ from rfl,
    LayerPosition.atLayer_succ_eq_next]
  congr 1

/-- A coordinate opened by the digests of `U` is opened by every larger set of digests. -/
theorem OpenedCoord.mono {U U' : Bytes vp.params.m → Prop} (hU : ∀ d, U d → U' d) {adrs : Adrs}
    {t : ℕ} (h : OpenedCoord U adrs t) : OpenedCoord U' adrs t :=
  let ⟨d, hd, hi⟩ := h
  ⟨d, hU d hd, hi⟩

/-! ## Chain steps and the honest message -/

/-- The structural child of step `t` of WOTS+ chain `i` at `pos`: the chain's secret at `t = 0`,
and the hash step at hash address `t - 1` above. -/
@[expose] def chainChild (pos : LayerPosition vp) (i : ℕ) : ℕ → Adrs ⊕ Adrs
  | 0 => .inl (wotsSkAdrs (wotsInstanceAdrs pos) i)
  | t + 1 => .inr ((wotsChainAdrs (wotsInstanceAdrs pos) i).setHashAddress t)

variable (core) in
/-- The cells of the hash path of WOTS+ chain `i` at `pos` are the cells of its steps. -/
theorem pathCell_wotsInstanceAdrs (pos : LayerPosition vp) (i t : ℕ) :
    pathCell core (wotsSkAdrs (wotsInstanceAdrs pos) i)
      ((wotsChainAdrs (wotsInstanceAdrs pos) i).setHashAddress ·) t =
      childCell core (chainChild pos i t) := by
  cases t <;> rfl

/-- Every step of a WOTS+ chain at or below the top has a cell. -/
theorem isSome_childCell_chainChild (pos : LayerPosition vp) (i : Fin vp.params.len) {t : ℕ}
    (ht : t ≤ vp.params.w - 1) : (childCell core (chainChild pos i.val t)).isSome := by
  rcases t with _ | t
  · simp [chainChild, childCell_inl core (Adrs.isSecretKey_wotsSkAdrs _ _)]
  · simp [chainChild, childCell_inr core
      (wotsChainAdrs_setHashAddress_mem_constructionAddresses pos i (by omega : t < _))]

/-- Every step of a WOTS+ chain at or below the top is an in-range address. -/
theorem addressFacts_chainChild (hb : CanonicalAddressBounds vp.params) (pos : LayerPosition vp)
    (i : Fin vp.params.len) {t : ℕ} (ht : t ≤ vp.params.w - 1) :
    AddressFacts vp ((chainChild pos i.val t).elim id id) := by
  rcases t with _ | t
  · exact addressFacts_wotsSkAdrs hb pos i
  · exact addressFacts_wotsStepAdrs hb (pos, i) ⟨t, by omega⟩

/-- Steps of WOTS+ chains are equal only at one position, chain and step. -/
theorem eq_of_chainChild_eq {pos pos' : LayerPosition vp} {i i' t t' : ℕ}
    (h : chainChild pos i t = chainChild pos' i' t') : pos = pos' ∧ i = i' ∧ t = t' := by
  have key : ∀ {a a' : Adrs}, a.layer = a'.layer → a.tree = a'.tree → a.word1 = a'.word1 →
      ∀ (p p' : LayerPosition vp), a = wotsInstanceAdrs p → a' = wotsInstanceAdrs p' → p = p' := by
    rintro a a' hl ht hw p p' rfl rfl
    exact wotsInstanceAdrs_injective vp (Adrs.ext hl ht rfl hw rfl rfl)
  rcases t with _ | t <;> rcases t' with _ | t' <;>
    simp only [chainChild, reduceCtorEq, Sum.inl.injEq, Sum.inr.injEq] at h
  · rw [wotsSkAdrs_eq, wotsSkAdrs_eq] at h
    simp only [Adrs.mk.injEq] at h
    exact ⟨key h.1 h.2.1 h.2.2.2.1 pos pos' rfl rfl, h.2.2.2.2.1, rfl⟩
  · rw [wotsChainAdrs_setHashAddress_eq, wotsChainAdrs_setHashAddress_eq] at h
    simp only [Adrs.mk.injEq] at h
    exact ⟨key h.1 h.2.1 h.2.2.2.1 pos pos' rfl rfl, h.2.2.2.2.1, by rw [h.2.2.2.2.2]⟩

variable (core) in
/-- The cell of the honest message signed at `pos`: the label of the node at `msgAdrs pos`. -/
@[expose] def msgCell (pos : LayerPosition vp) : DeriveQuery core ⊕ NodeKey core :=
  .inr ⟨core.adrsToKey (msgAdrs pos), msgAdrs pos, msgAdrs_mem_constructionAddresses pos, rfl⟩

/-- The cell of the honest message at `pos` is the label of the node at any address equal to
`msgAdrs pos`. -/
theorem msgCell_eq_of_msgAdrs_eq {pos : LayerPosition vp} {a : Adrs} (h : msgAdrs pos = a)
    (ha : a ∈ constructionAddresses vp) :
    msgCell core pos = .inr ⟨core.adrsToKey a, a, ha, rfl⟩ := by
  subst h
  rfl

/-- At the layer-zero position of a digest, the honest message is at the FORS roots compression of
the digest's FORS instance. -/
theorem msgAdrs_initial (parts : DigestParts vp.params) :
    msgAdrs (LayerPosition.initial vp parts) = forsPkAdrs parts.forsAdrs := by
  simp only [msgAdrs, LayerPosition.initial_layer_val, ↓reduceIte]
  rfl

/-- One layer above a position, the honest message is at the root of the position's tree. -/
theorem msgAdrs_next (pos : LayerPosition vp) (hn : pos.layer.val + 1 < vp.params.d) :
    msgAdrs (pos.next hn) = xmssNodeAdrs pos.toAdrs vp.params.hp 0 := by
  simp only [msgAdrs, LayerPosition.next_layer_val, Nat.add_one_ne_zero, ↓reduceIte,
    childTreeAdrs_next]

/-! ## Hidden structural children -/

variable (core) in
/-- Step `t` of WOTS+ chain `i` at `pos` is hidden for the digests `U` at the state `st`: it is
below the top step `w - 1`, and if a digest of `U` uses `pos` and the honest message at `pos` is
drawn in `st`, it is below the step that message selects on chain `i`. -/
@[expose] def HiddenChainStep (U : Bytes vp.params.m → Prop)
    (st : RelabelState (hashSpec core) (DeriveQuery core) (NodeKey core) core.Y)
    (pos : LayerPosition vp) (i t : ℕ) : Prop :=
  t < vp.params.w - 1 ∧
    (UsedPosition U pos → ∀ m, st.2 (msgCell core pos) = some m → t < chainStepsCore core m i)

variable (core) in
/-- The hidden structural children for the digests `U` at the state `st`: the hidden steps of the
WOTS+ chains of every position, and the secrets of the FORS coordinates that no digest of `U`
opens. -/
@[expose] def HiddenChild (U : Bytes vp.params.m → Prop)
    (st : RelabelState (hashSpec core) (DeriveQuery core) (NodeKey core) core.Y)
    (b : Adrs ⊕ Adrs) : Prop :=
  (∃ (pos : LayerPosition vp) (i : Fin vp.params.len) (t : ℕ),
      b = chainChild pos i.val t ∧ HiddenChainStep core U st pos i.val t) ∨
    ∃ (bp : BottomPosition vp) (t : ℕ), t < vp.params.k * 2 ^ vp.params.a ∧
      b = .inl (forsSkAdrs bp.forsAdrs t) ∧ ¬OpenedCoord U bp.forsAdrs t

variable (core) in
/-- The cells of the hidden structural children. -/
@[expose] def hiddenCells (U : Bytes vp.params.m → Prop)
    (st : RelabelState (hashSpec core) (DeriveQuery core) (NodeKey core) core.Y) :
    Set (DeriveQuery core ⊕ NodeKey core) :=
  {c | ∃ b, HiddenChild core U st b ∧ childCell core b = some c}

variable (core) in
/-- **No hidden cell is drawn.** No cell hidden for the digests that the log `log` signs at the
public key `pk` in the public cache of `st` is drawn in `st`. -/
@[expose] def HiddenUndrawn (pk : PublicKeyCore core)
    (log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp core))
    (st : RelabelState (hashSpec core) (DeriveQuery core) (NodeKey core) core.Y) : Prop :=
  ∀ c ∈ hiddenCells core (SignedDigest core pk log st.1) st, st.2 c = none

variable {U U' : Bytes vp.params.m → Prop}
  {st st' : RelabelState (hashSpec core) (DeriveQuery core) (NodeKey core) core.Y}

/-- The cell of a hidden step of a WOTS+ chain is a hidden cell. -/
theorem mem_hiddenCells_of_hiddenChainStep {pos : LayerPosition vp} {i : Fin vp.params.len}
    {t : ℕ} (h : HiddenChainStep core U st pos i.val t) {c : DeriveQuery core ⊕ NodeKey core}
    (hc : childCell core (chainChild pos i.val t) = some c) : c ∈ hiddenCells core U st :=
  ⟨_, .inl ⟨pos, i, t, rfl, h⟩, hc⟩

/-- The cell of the secret of a FORS coordinate that no digest of `U` opens is a hidden cell. -/
theorem mem_hiddenCells_forsSkAdrs (bp : BottomPosition vp) {t : ℕ}
    (ht : t < vp.params.k * 2 ^ vp.params.a) (h : ¬OpenedCoord U bp.forsAdrs t)
    {c : DeriveQuery core ⊕ NodeKey core}
    (hc : childCell core (.inl (forsSkAdrs bp.forsAdrs t)) = some c) :
    c ∈ hiddenCells core U st :=
  ⟨_, .inr ⟨bp, t, ht, rfl, h⟩, hc⟩

/-- **Down-closure.** Below a hidden chain step, every step is hidden. -/
theorem HiddenChainStep.of_le {pos : LayerPosition vp} {i t t' : ℕ}
    (h : HiddenChainStep core U st pos i t) (ht : t' ≤ t) : HiddenChainStep core U st pos i t' :=
  ⟨by have := h.1; omega, fun hpos m hm ↦ by have := h.2 hpos m hm; omega⟩

/-- More digests and a larger state hide no more chain steps. -/
theorem HiddenChainStep.anti (hU : ∀ d, U d → U' d) (hle : st ≤ st') {pos : LayerPosition vp}
    {i t : ℕ} (h : HiddenChainStep core U' st' pos i t) : HiddenChainStep core U st pos i t :=
  ⟨h.1, fun hpos m hm ↦ h.2 (hpos.mono hU) m (hle.2 hm)⟩

/-- More digests and a larger state hide no more structural children. -/
theorem HiddenChild.anti (hU : ∀ d, U d → U' d) (hle : st ≤ st') {b : Adrs ⊕ Adrs}
    (h : HiddenChild core U' st' b) : HiddenChild core U st b := by
  rcases h with ⟨pos, i, t, rfl, h⟩ | ⟨bp, t, ht, rfl, h⟩
  · exact .inl ⟨pos, i, t, rfl, h.anti hU hle⟩
  · exact .inr ⟨bp, t, ht, rfl, fun ho ↦ h (ho.mono hU)⟩

/-- **Monotonicity.** More digests and a larger state hide no more cells. -/
theorem hiddenCells_anti (hU : ∀ d, U d → U' d) (hle : st ≤ st') :
    hiddenCells core U' st' ⊆ hiddenCells core U st :=
  fun _ ⟨b, hb, hc⟩ ↦ ⟨b, hb.anti hU hle, hc⟩

/-- A hidden structural child is an in-range address. -/
theorem addressFacts_of_hiddenChild (hb : CanonicalAddressBounds vp.params) {b : Adrs ⊕ Adrs}
    (h : HiddenChild core U st b) : AddressFacts vp (b.elim id id) := by
  rcases h with ⟨pos, i, t, rfl, h⟩ | ⟨bp, t, ht, rfl, -⟩
  · exact addressFacts_chainChild hb pos i (by have := h.1; omega)
  · exact addressFacts_forsSkAdrs hb bp ht

/-! ## Public steps -/

/-- **Public steps draw no hidden cell.** A sampling or public step of the deferred game over the
SLH-DSA graph, from a state whose hidden cells are undrawn, ends in a state whose hidden cells are
undrawn. A public step draws only the label of a node whose children are drawn, and the only child
of a hidden WOTS+ hash step is the hidden step below it. -/
theorem hiddenUndrawn_of_mem_support_deferredImpl [SampleableType core.Y] [DecidableEq core.Y]
    [SampleableType (Bytes vp.params.m)] [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey]
    [DecidableEq core.SkPrf] (hd : core.KeyDiscipline vp) (pkSeed : core.PkSeed)
    {pk : PublicKeyCore core}
    {log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp core)}
    {t : ℕ ⊕ (hashSpec core).Domain}
    {s : RelabelState (hashSpec core) (DeriveQuery core) (NodeKey core) core.Y ×
      List (DeriveQuery core ⊕ NodeKey core)} {z}
    (hs : HiddenUndrawn core pk log s.1)
    (hz : z ∈ support (((slhGraph core pkSeed).deferredImpl (.inl (.inl t))).run s)) :
    HiddenUndrawn core pk log z.2.1 := by
  intro c hc
  have hle := (slhGraph core pkSeed).le_of_mem_support_deferredImpl hz
  have hU : ∀ d, SignedDigest core pk log s.1.1 d → SignedDigest core pk log z.2.1.1 d :=
    fun _ h ↦ h.mono (fun _ h ↦ h) hle.1
  rcases (slhGraph core pkSeed).cell_eq_or_exists_childVals_of_mem_support_deferredImpl hz c with
    h | ⟨κ, vs, rfl, hκ⟩
  · rw [h]
    exact hs c (hiddenCells_anti hU hle hc)
  · exfalso
    obtain ⟨b, hb, hbc⟩ := hc
    rcases hb with ⟨pos, i, t, rfl, hstep⟩ | ⟨bp, t, -, rfl, -⟩
    · rcases t with _ | t
      · simp [chainChild, childCell] at hbc
      · have hmem := wotsChainAdrs_setHashAddress_mem_constructionAddresses pos i (t := t)
          (by have := hstep.1; omega)
        rw [chainChild, childCell_inr core hmem] at hbc
        obtain rfl := Sum.inr_injective (Option.some_injective _ hbc)
        have hch := slhGraph_ch_wotsChainAdrs_setHashAddress core hd pkSeed hmem
        rw [pathCell_wotsInstanceAdrs] at hch
        obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.1
          (isSome_childCell_chainChild (core := core) pos i (t := t) (by have := hstep.1; omega))
        have hpred : c' ∈ hiddenCells core (SignedDigest core pk log z.2.1.1) z.2.1 :=
          ⟨_, .inl ⟨pos, i, t, rfl, hstep.of_le (Nat.le_succ t)⟩, hc'⟩
        have hnone := hs c' (hiddenCells_anti hU hle hpred)
        rw [CanonicalGraph.childVals_eq_some_iff, hch, hc'] at hκ
        rcases hκ with _ | ⟨hv, -⟩
        rw [hnone] at hv
        exact absurd hv (by simp)
    · simp [childCell] at hbc

/-! ## Hidden cells of a forgery's replay

A forgery's replay is read off a cache `c` of the public hash whose `H_msg` entries are those of
the public cache `C` of a state. Its used leaves are then positions used by the signed digests,
its unopened coordinates are not opened by them, and a chain value it finds hidden at a larger
state, where the honest message is drawn, is a hidden chain step. -/

/-- A leaf a logged signature uses, read off a cache with the `H_msg` entries of `C`, is a
position used by the digests the log signs in `C`. -/
theorem usedPosition_of_usedLeaf {o : RomOutcome vp core} {c : PublicHash.Cache core}
    {C : (hashSpec core).QueryCache}
    (hc : ∀ r pk root msg, c (.hmsg r pk root msg) = C (.inl (.hmsg r pk root msg)))
    {j : Fin vp.params.d} {pos : LayerPosition vp} (h : UsedLeaf o c j pos) :
    UsedPosition (SignedDigest core o.pk o.log C) pos := by
  obtain ⟨e, he, d, hd, rfl⟩ := h
  refine ⟨d, ⟨e, he, (hc _ _ _ _).symm.trans hd⟩, ?_⟩
  congr 1
  exact Fin.ext (LayerPosition.atLayer_layer_val _ _ _)

/-- A FORS coordinate no logged signature opens, read off a cache with the `H_msg` entries of
`C`, is not opened by the digests the log signs in `C`. -/
theorem not_openedCoord_of_unopenedCoord {o : RomOutcome vp core} {c : PublicHash.Cache core}
    {C : (hashSpec core).QueryCache}
    (hc : ∀ r pk root msg, c (.hmsg r pk root msg) = C (.inl (.hmsg r pk root msg)))
    {adrs : Adrs} {t : ℕ} (h : UnopenedCoord o c adrs t) :
    ¬OpenedCoord (SignedDigest core o.pk o.log C) adrs t := by
  rintro ⟨d, ⟨e, he, hd⟩, i, hadrs, ht⟩
  exact h e he d ((hc _ _ _ _).trans hd) i ⟨hadrs, ht⟩

/-- A chain step below the top that, at a used position, lies below the step selected by the
honest message drawn at a larger state is hidden. -/
theorem hiddenChainStep_of_le (hle : st ≤ st') {pos : LayerPosition vp} {i t : ℕ}
    (ht : t < vp.params.w - 1)
    (h : UsedPosition U pos →
      ∃ m, st'.2 (msgCell core pos) = some m ∧ t < chainStepsCore core m i) :
    HiddenChainStep core U st pos i t :=
  ⟨ht, fun hpos m hm ↦ by
    obtain ⟨m', hm', hlt⟩ := h hpos
    obtain rfl : m = m' := Option.some_injective _ ((hle.2 hm).symm.trans hm')
    exact hlt⟩

/-! ## Distinct children have distinct cells -/

/-- Under key injectivity on the in-range addresses, two in-range structural children with the
same cell are equal. -/
theorem eq_of_childCell_eq_some (hinj : core.KeyInjective vp) {b b' : Adrs ⊕ Adrs}
    {c : DeriveQuery core ⊕ NodeKey core} (hc : childCell core b = some c)
    (hc' : childCell core b' = some c) (hb : AddressFacts vp (b.elim id id))
    (hb' : AddressFacts vp (b'.elim id id)) : b = b' := by
  rcases b with a | a <;> rcases b' with a' | a' <;>
    simp only [childCell, Option.map_eq_some_iff] at hc hc'
  · obtain ⟨k, hk, rfl⟩ := hc
    obtain ⟨k', hk', hkk⟩ := hc'
    obtain rfl : k' = k := Sum.inl_injective (Sum.inl_injective hkk)
    rw [prfKeyOf_eq_some_iff] at hk hk'
    exact congrArg Sum.inl (hinj hb hb' (hk.2.trans hk'.2.symm))
  · obtain ⟨_, -, rfl⟩ := hc
    obtain ⟨_, -, h⟩ := hc'
    simp at h
  · obtain ⟨_, -, rfl⟩ := hc
    obtain ⟨_, -, h⟩ := hc'
    simp at h
  · obtain ⟨k, hk, rfl⟩ := hc
    obtain ⟨k', hk', hkk⟩ := hc'
    obtain rfl : k' = k := Sum.inr_injective hkk
    rw [nodeKeyOf_eq_some_iff] at hk hk'
    exact congrArg Sum.inr (hinj hb hb' (hk.2.trans hk'.2.symm))

/-- **Reading unhidden children.** Under the key discipline, the cell of an in-range structural
child that is not hidden is not a hidden cell. -/
theorem not_mem_hiddenCells_of_childCell_eq_some (hd : core.KeyDiscipline vp) {b : Adrs ⊕ Adrs}
    {c : DeriveQuery core ⊕ NodeKey core} (hc : childCell core b = some c)
    (hb : AddressFacts vp (b.elim id id)) (h : ¬HiddenChild core U st b) :
    c ∉ hiddenCells core U st := by
  rintro ⟨b', hb', hc'⟩
  obtain rfl := eq_of_childCell_eq_some hd.keyInjective hc' hc
    (addressFacts_of_hiddenChild hd.canonicalAddressBounds hb') hb
  exact h hb'

/-- The cell of a node child is the label of a ledger address, which is in range. -/
theorem addressFacts_of_childCell_inr_eq_some (hb : CanonicalAddressBounds vp.params) {a : Adrs}
    {c : DeriveQuery core ⊕ NodeKey core} (hc : childCell core (.inr a) = some c) :
    AddressFacts vp a := by
  simp only [childCell, Option.map_eq_some_iff] at hc
  obtain ⟨κ, hκ, -⟩ := hc
  exact addressFacts_of_mem_constructionAddresses hb ((nodeKeyOf_eq_some_iff core).1 hκ).1

/-- A derivation that is not a secret, such as a randomizer, is not a hidden cell. -/
theorem inl_inr_not_mem_hiddenCells (x : core.Y × List Byte) :
    (.inl (.inr x) : DeriveQuery core ⊕ NodeKey core) ∉ hiddenCells core U st := by
  rintro ⟨b, -, hb⟩
  rcases b with a | a <;> simp [childCell] at hb

/-! ## Children that are not hidden -/

/-- A node child that is not a WOTS+ hash step, or that is the top hash step of its chain, is not
hidden. -/
theorem not_hiddenChild_inr {a : Adrs} (h : a.type ≠ 0 ∨ a.word3 = vp.params.w - 2) :
    ¬HiddenChild core U st (.inr a) := by
  rintro (⟨pos, i, t, hb, ht, -⟩ | ⟨bp, t, -, hb, -⟩)
  · rcases t with _ | t
    · simp [chainChild] at hb
    · simp only [chainChild, Sum.inr.injEq] at hb
      subst hb
      rw [wotsChainAdrs_setHashAddress_eq] at h
      simp only [ne_eq, not_true_eq_false, false_or] at h
      omega
  · simp at hb

/-- At a position used by `U`, whose honest message `m` is drawn, the steps of a chain at and above
the step `m` selects are not hidden. -/
theorem not_hiddenChild_chainChild {pos : LayerPosition vp} (hpos : UsedPosition U pos) {m : core.Y}
    (hm : st.2 (msgCell core pos) = some m) {i t : ℕ} (ht : chainStepsCore core m i ≤ t) :
    ¬HiddenChild core U st (chainChild pos i t) := by
  rintro (⟨pos', i', t', hb, -, h⟩ | ⟨bp, t', -, hb, -⟩)
  · obtain ⟨rfl, rfl, rfl⟩ := eq_of_chainChild_eq hb
    have := h hpos m hm
    omega
  · rcases t with _ | t
    · simp only [chainChild, Sum.inl.injEq] at hb
      rw [wotsSkAdrs_eq, forsSkAdrs_eq] at hb
      simp at hb
    · simp [chainChild] at hb

/-- The FORS secret that a digest of `U` opens is not hidden. -/
theorem not_hiddenChild_inl_forsSkAdrs {d : Bytes vp.params.m} (hd : U d) (i : Fin vp.params.k) :
    ¬HiddenChild core U st (.inl (forsSkAdrs (splitDigest vp.params d).forsAdrs
      (forsSigLeafIndex vp.params (splitDigest vp.params d).md.toList i.val))) := by
  rintro (⟨pos, i', t, hb, -⟩ | ⟨bp, t, -, hb, h⟩)
  · rcases t with _ | t
    · simp only [chainChild, Sum.inl.injEq] at hb
      rw [wotsSkAdrs_eq, forsSkAdrs_eq] at hb
      simp at hb
    · simp [chainChild] at hb
  · simp only [Sum.inl.injEq] at hb
    rw [forsSkAdrs_eq, forsSkAdrs_eq] at hb
    simp only [Adrs.mk.injEq, true_and] at hb
    obtain ⟨hl, ht, hw, hidx⟩ := hb
    have hadrs : bp.forsAdrs = (splitDigest vp.params d).forsAdrs :=
      Adrs.ext hl.symm ht.symm rfl hw.symm rfl rfl
    rw [hadrs, ← hidx] at h
    exact h ⟨d, hd, i, rfl, rfl⟩

/-- The global leaf index of an opened FORS coordinate is below `k * 2 ^ a`. -/
theorem forsSigLeafIndex_lt (md : List Byte) (i : Fin vp.params.k) :
    forsSigLeafIndex vp.params md i.val < vp.params.k * 2 ^ vp.params.a := by
  have h := forsIdx_lt vp.params md i.val
  have hi : i.val + 1 ≤ vp.params.k := i.isLt
  calc forsSigLeafIndex vp.params md i.val = i.val * 2 ^ vp.params.a + forsIdx vp.params md i.val
        := forsSigLeafIndex_eq _ _ _
    _ < (i.val + 1) * 2 ^ vp.params.a := by rw [Nat.add_mul, one_mul]; omega
    _ ≤ _ := Nat.mul_le_mul_right _ hi

end SLHDSA.Security
