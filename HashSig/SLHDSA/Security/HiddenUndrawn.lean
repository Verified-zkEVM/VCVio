/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.LabReadSet
import HashSig.SLHDSA.Security.AddressKeys
import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Option
import VCVio.OracleComp.QueryTracking.RandomOracle.Settled

/-!
# No hidden cell is drawn in the deferred lab experiment

On every run of the lab experiment `labExperiment core adv pkSeed` in the deferred game over the
SLH-DSA graph `slhGraph core pkSeed`, before the end fill, no cell is drawn that is hidden for the
digests the transcript's log signs: no WOTS+ chain step below the one the honest message selects
at a used position, no chain step below the top at an unused position, and no unopened FORS
secret. The transcript's public key carries the graph's public seed `pkSeed`
(`hiddenUndrawn_of_mem_support_deferredImpl_labExperiment`).

The invariant `HiddenUndrawn pk log st` is carried through the three stages of the experiment by
`SignatureAlg.holds_of_mem_support_run_unforgeableTranscriptExperiment`.

* **Key generation** reads no hidden cell at all (`readsUnhidden_labXmssNode`), so from the empty
  state it draws none.
* **The forger and verification** make only sampling and public queries, and a public query draws
  only the label of a node whose children are drawn (`hiddenUndrawn_of_mem_support_deferredImpl`).
* **Signing** a message `M` with randomizer `R` adds the digest `d` of `H_msg(R, PK.seed, PK.root,
  M)` to the signed digests. It reads the secrets `d` opens, the FORS nodes, and, at each layer,
  WOTS+ chain steps at and above the ones the layer's message selects. That message is the drawn
  label of the honest message's node at the layer's position. At layer `0` it is the FORS public
  key (`cell_eq_of_mem_support_forsPkFromSigWith`), and above it the root recovered at the layer
  below (`cell_eq_of_mem_support_xmssPkFromSigWith`). Every cell signing draws is therefore
  visible for the signed digests with `d` added (`hiddenKept_of_mem_support_labSignFromPosition`).

The same experiment leaves the cell of the top-layer root, `rootNode core`, holding `PK.root`
(`cell_rootNode_of_mem_support_deferredImpl_labExperiment`): key generation reads that cell and
returns it, and no later step changes a drawn cell. Under the key discipline the root is no node's
child (`inr_rootNode_not_mem_ch`).

## References

- NIST FIPS 205, Algorithms 18–20 (internal key generation, signing and verification)
-/

public section

namespace SLHDSA.Security

open OracleComp OracleSpec SignatureAlg

variable {vp : ValidatedParams} {core : CorePrimitives vp.params}

variable (core) in
/-- The state `st'` leaves every cell hidden for the digests `U` at `st'` as it is in `st`. -/
@[expose] def HiddenKept (U : Bytes vp.params.m → Prop)
    (st st' : RelabelState (hashSpec core) (DeriveQuery core) (NodeKey core) core.Y) : Prop :=
  ∀ c ∈ hiddenCells core U st', st'.2 c = st.2 c

/-- Keeping the hidden cells composes along a growing state. -/
theorem HiddenKept.trans {U : Bytes vp.params.m → Prop}
    {st st₁ st₂ : RelabelState (hashSpec core) (DeriveQuery core) (NodeKey core) core.Y}
    (h₁ : HiddenKept core U st st₁) (h₂ : HiddenKept core U st₁ st₂) (hle : st₁ ≤ st₂) :
    HiddenKept core U st st₂ :=
  fun c hc ↦ (h₂ c hc).trans (h₁ c (hiddenCells_anti (fun _ h ↦ h) hle hc))

/-! ## The root is no node's child -/

variable (vp) in
/-- The address of the top-layer root, node `(h', 0)` of the XMSS tree at layer `d - 1`. -/
abbrev rootAdrs : Adrs :=
  xmssNodeAdrs (GeneralHypertree.layerAdrs (vp.params.d - 1) 0) vp.params.hp 0

/-- The top-layer root is an address of the union ledger. -/
theorem rootAdrs_mem_constructionAddresses : rootAdrs vp ∈ constructionAddresses vp := by
  rw [rootAdrs, ← LayerTreeCoord.top_toAdrs_layerAdrs]
  exact xmssNodeAdrs_mem_constructionAddresses _ vp.valid.hp_pos le_rfl (by simp)

variable (core) in
/-- The node of the top-layer root. -/
def rootNode : NodeKey core :=
  ⟨core.adrsToKey (rootAdrs vp), rootAdrs vp, rootAdrs_mem_constructionAddresses, rfl⟩

/-- The top-layer root is no node child of an address of the union ledger: the node children of a
ledger address are `WOTS_HASH`, `WOTS_PK` or `FORS_TREE` addresses, or XMSS nodes below height
`h'`. -/
theorem inr_rootAdrs_not_mem_childAdrs {a : Adrs} (ha : a ∈ constructionAddresses vp) :
    .inr (rootAdrs vp) ∉ childAdrs vp a := by
  intro hb
  have hroot : rootAdrs vp = ⟨vp.params.d - 1, 0, 2, 0, vp.params.hp, 0⟩ := rfl
  rcases (mem_constructionAddresses_iff a).1 ha with h | h | h | h | h | h
  · obtain ⟨_, -, rfl⟩ := List.mem_map.1 h
    simp [childAdrs_forsNodeAdrs_zero] at hb
  · obtain ⟨⟨⟨pos, tree⟩, z, j⟩, hmem, rfl⟩ := List.mem_map.1 h
    rw [childAdrs_forsNodeAdrs vp (mem_perfectInternalCoords.1 (List.mem_product.1 hmem).2).1]
      at hb
    simp [hroot, forsNodeAdrs_eq] at hb
  · obtain ⟨_, -, rfl⟩ := List.mem_map.1 h
    simp [childAdrs_forsPkAdrs, hroot, forsNodeAdrs_eq] at hb
  · obtain ⟨⟨_, ⟨t, _⟩⟩, -, rfl⟩ := List.mem_map.1 h
    simp only [wotsStepAdrs] at hb
    rcases t with _ | t
    · simp [childAdrs_wotsChainAdrs_setHashAddress_zero] at hb
    · rw [childAdrs_wotsChainAdrs_setHashAddress_succ] at hb
      simp [hroot, wotsChainAdrs_setHashAddress_eq] at hb
  · obtain ⟨_, -, rfl⟩ := List.mem_map.1 h
    simp [childAdrs_wotsPkAdrs, hroot, wotsChainAdrs_setHashAddress_eq] at hb
  · obtain ⟨⟨_, z, j⟩, hmem, rfl⟩ := List.mem_map.1 h
    obtain ⟨hz, hzh, -⟩ := mem_perfectInternalCoords.1 (List.mem_product.1 hmem).2
    rcases (by omega : z = 1 ∨ 1 < z) with rfl | hz1
    · simp [childAdrs_xmssNodeAdrs_one, hroot, wotsPkAdrs_eq] at hb
    · rw [childAdrs_xmssNodeAdrs vp hz1] at hb
      simp only [hroot, xmssNodeAdrs_eq, List.mem_cons, Sum.inr.injEq, Adrs.mk.injEq,
        List.not_mem_nil, or_false] at hb
      omega

/-- **The root is no node's child**, under the key discipline. -/
theorem inr_rootNode_not_mem_ch (hd : core.KeyDiscipline vp) (pkSeed : core.PkSeed)
    (κ : NodeKey core) :
    (.inr (rootNode core) : DeriveQuery core ⊕ NodeKey core) ∉ (slhGraph core pkSeed).ch κ := by
  intro h
  rw [slhGraph_ch, List.mem_filterMap] at h
  obtain ⟨(b | b), hb, hcb⟩ := h
  · obtain ⟨_, -, -, h⟩ := (childCell_inl_eq_some_iff core).1 hcb
    cases h
  · obtain ⟨_, hmem, hkey, h⟩ := (childCell_inr_eq_some_iff core).1 hcb
    cases h
    obtain rfl := hd.keyInjective
      (addressFacts_of_mem_constructionAddresses hd.canonicalAddressBounds hmem)
      (addressFacts_of_mem_constructionAddresses hd.canonicalAddressBounds
        rootAdrs_mem_constructionAddresses) hkey
    exact inr_rootAdrs_not_mem_childAdrs (nodeAdrs_mem_constructionAddresses core κ) hb

/-! ## The queries of the forger and of verification -/

variable (core) in
/-- The sampling and public queries of the lab specification. -/
@[expose] def IsAmbientLabQuery : (labSpec core).Domain → Prop
  | .inl (.inl _) => True
  | _ => False

/-- Verification in the lab makes only sampling and public queries. -/
theorem allQueriesSatisfy_labScheme_verify [SampleableType core.Y] [DecidableEq core.Y]
    {pkSeed : core.PkSeed} (optRand : PublicKeyCore core → ProbComp core.Y)
    (pk : PublicKeyCore core) (msg : List Byte) (sig : GeneralScheme.SignatureCore vp core) :
    AllQueriesSatisfy ((labScheme core optRand pkSeed).verify pk msg sig)
      (IsAmbientLabQuery core) :=
  GeneralScheme.verifyInternalM_pred (AllQueriesSatisfy · (IsAmbientLabQuery core))
    (fun _ ↦ allQueriesSatisfy_pure _ _) (fun _ _ ↦ allQueriesSatisfy_bind) core msg sig pk
    (fun _ _ _ ↦ (allQueriesSatisfy_query_iff _ _).2 trivial)
    ((allQueriesSatisfy_query_iff _ _).2 trivial)

/-- The lab forger makes only sampling and public queries, besides its signing queries. -/
theorem allQueriesSatisfy_labAdversary_main [SampleableType core.Y] [DecidableEq core.Y]
    [SampleableType core.SkSeed] [SampleableType core.SkPrf] {pkSeed : core.PkSeed}
    {e : core.SkSeed ≃ core.Y}
    {optRand : PublicKeyCore core → ProbComp core.Y} {pkSeedDist : ProbComp core.PkSeed}
    (adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist)) (pk : PublicKeyCore core) :
    AllQueriesSatisfy ((labAdversary core adv pkSeed).main pk)
      (Sum.elim (IsAmbientLabQuery core) fun _ ↦ True) := by
  rw [labAdversary, deriveAdversary, UnforgeableAdversary.mapOracles_mapOracles]
  exact allQueriesSatisfy_mapOracles _ adv (fun _ ↦ by
    simp only [QueryImpl.apply_compose, OracleSpec.withDerivationsLift]
    exact (allQueriesSatisfy_query_iff _ _).2 trivial) pk

variable [SampleableType core.Y] [DecidableEq core.Y] [SampleableType (Bytes vp.params.m)]
  [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf]
  (pkSeed : core.PkSeed)

/-- A run of a lab program that reads no hidden cell at its final state keeps the hidden cells. -/
theorem hiddenKept_of_readsUnhidden {U : Bytes vp.params.m → Prop} {α : Type}
    {oa : OracleComp (labSpec core) α}
    {s : RelabelState (hashSpec core) (DeriveQuery core) (NodeKey core) core.Y ×
      List (DeriveQuery core ⊕ NodeKey core)} {z}
    (hz : z ∈ support ((simulateQ (slhGraph core pkSeed).deferredImpl oa).run s))
    (h : ReadsUnhidden core pkSeed U z.2.1 oa) : HiddenKept core U s.1 z.2.1 :=
  fun _ hc ↦ (slhGraph core pkSeed).cell_eq_of_mem_support_simulateQ_deferredImpl h hz
    fun h' ↦ h' hc

/-! ## The messages signed at each layer -/

/-- After FORS public-key recovery at the lab callbacks, the recovered public key is the drawn
label of the FORS roots compression. -/
theorem cell_eq_of_mem_support_forsPkFromSigWith (sig : ForsSigCore vp.params core)
    (md : List Byte) {adrs : Adrs} {c : DeriveQuery core ⊕ NodeKey core}
    (hc : childCell core (.inr (forsPkAdrs adrs)) = some c)
    {s : RelabelState (hashSpec core) (DeriveQuery core) (NodeKey core) core.Y ×
      List (DeriveQuery core ⊕ NodeKey core)} {z}
    (hz : z ∈ support ((simulateQ (slhGraph core pkSeed).deferredImpl
      (forsPkFromSigWith core (labF core) (labH core) (labTl core) sig md adrs)).run s)) :
    z.2.1.2 c = some z.1 := by
  simp only [forsPkFromSigWith, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨w, -, hz⟩ := hz
  rw [labTl, labNode, hc] at hz
  exact (slhGraph core pkSeed).cell_eq_of_mem_support_simulateQ_deferredImpl_readCell hz

/-- After XMSS root recovery at the lab callbacks from a leaf of the tree at `adrs`, the recovered
root is the drawn label of the tree's root. -/
theorem cell_eq_of_mem_support_xmssPkFromSigWith {idx : ℕ} (hidx : idx < 2 ^ vp.params.hp)
    (sig : XmssSig vp.params core) (msg : core.Y) {adrs : Adrs}
    {c : DeriveQuery core ⊕ NodeKey core}
    (hc : childCell core (.inr (xmssNodeAdrs adrs vp.params.hp 0)) = some c)
    {s : RelabelState (hashSpec core) (DeriveQuery core) (NodeKey core) core.Y ×
      List (DeriveQuery core ⊕ NodeKey core)} {z}
    (hz : z ∈ support ((simulateQ (slhGraph core pkSeed).deferredImpl
      (xmssPkFromSigWith core (labF core) (labTl core) (labH core) idx sig msg adrs)).run s)) :
    z.2.1.2 c = some z.1 := by
  simp only [xmssPkFromSigWith, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨w, -, hz⟩ := hz
  refine PerfectMerkleTree.climbM_pred_of_last (fun oa ↦ ∀ s (z : core.Y × _),
      z ∈ support ((simulateQ (slhGraph core pkSeed).deferredImpl oa).run s) → z.2.1.2 c = some z.1)
    (fun _ _ h s z hz ↦ ?_) _ idx _ (by simpa using vp.valid.hp_pos.ne')
    (fun _ _ s z hz ↦ ?_) _ _ hz
  · simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨w, -, hz⟩ := hz
    exact h _ _ _ hz
  · rw [Vector.length_toList, Nat.div_eq_of_lt hidx, xmssNodeHashWith, labH, labNode, hc] at hz
    exact (slhGraph core pkSeed).cell_eq_of_mem_support_simulateQ_deferredImpl_readCell hz

/-! ## Hypertree signing -/

/-- **Hypertree signing keeps the hidden cells.** Signing `msg` from a position used by `U`, whose
honest message `msg` is drawn, upward over `layers` layers in the lab, reads at each layer only
cells visible for `U`: the message signed at the next layer is the recovered root, which is the
drawn honest message there. -/
theorem hiddenKept_of_mem_support_labSignFromPosition (hd : core.KeyDiscipline vp)
    {U : Bytes vp.params.m → Prop} (recoverFinal : Bool) :
    ∀ (layers : ℕ) (pos : LayerPosition vp) (h : pos.layer.val + layers = vp.params.d)
      (msg : core.Y)
      {s : RelabelState (hashSpec core) (DeriveQuery core) (NodeKey core) core.Y ×
        List (DeriveQuery core ⊕ NodeKey core)} {z},
      UsedPosition U pos → s.1.2 (msgCell core pos) = some msg →
      z ∈ support ((simulateQ (slhGraph core pkSeed).deferredImpl
        (labSignFromPosition core recoverFinal pos layers h msg)).run s) →
      HiddenKept core U s.1 z.2.1
  | 0, pos, h, msg, s, z, _, _, hz => by
      simp only [labSignFromPosition, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      exact fun _ _ ↦ rfl
  | 1, pos, h, msg, s, z, hpos, hmsg, hz => by
      rw [labSignFromPosition, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨w, hw, hz⟩ := hz
      have hle := (slhGraph core pkSeed).le_of_mem_support_simulateQ_deferredImpl _ hw
      have h₁ := hiddenKept_of_readsUnhidden pkSeed hw
        (readsUnhidden_labXmssSign pkSeed hpos (hle.2 hmsg) hd)
      cases recoverFinal
      · simp only [Bool.false_eq_true, ↓reduceIte, simulateQ_pure, StateT.run_pure,
          support_pure, Set.mem_singleton_iff] at hz
        subst hz
        exact h₁
      · simp only [↓reduceIte, simulateQ_bind, StateT.run_bind, mem_support_bind_iff,
          simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        obtain ⟨w', hw', rfl⟩ := hz
        have hle' := (slhGraph core pkSeed).le_of_mem_support_simulateQ_deferredImpl _ hw'
        change HiddenKept core U s.1 w'.2.1
        exact h₁.trans (hiddenKept_of_readsUnhidden pkSeed hw'
          (readsUnhidden_xmssPkFromSigWith pkSeed hpos (hle'.2 (hle.2 hmsg)) hd _)) hle'
  | layers + 2, pos, h, msg, s, z, hpos, hmsg, hz => by
      rw [labSignFromPosition] at hz
      simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff, simulateQ_pure,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨w₁, hw₁, w₂, hw₂, w₃, hw₃, rfl⟩ := hz
      have hle₁ := (slhGraph core pkSeed).le_of_mem_support_simulateQ_deferredImpl _ hw₁
      have hle₂ := (slhGraph core pkSeed).le_of_mem_support_simulateQ_deferredImpl _ hw₂
      have hle₃ := (slhGraph core pkSeed).le_of_mem_support_simulateQ_deferredImpl _ hw₃
      have hn : pos.layer.val + 1 < vp.params.d := by omega
      have hnext : w₂.2.1.2 (msgCell core (pos.next hn)) = some w₂.1 :=
        cell_eq_of_mem_support_xmssPkFromSigWith pkSeed pos.leaf.isLt _ _
          (by rw [← msgAdrs_next pos hn]; exact childCell_msgAdrs _) hw₂
      have h₁ := hiddenKept_of_readsUnhidden pkSeed hw₁
        (readsUnhidden_labXmssSign pkSeed hpos (hle₁.2 hmsg) hd)
      have h₂ := hiddenKept_of_readsUnhidden pkSeed hw₂
        (readsUnhidden_xmssPkFromSigWith pkSeed hpos (hle₂.2 (hle₁.2 hmsg)) hd _)
      have h₃ := hiddenKept_of_mem_support_labSignFromPosition hd false (layers + 1)
        (pos.next hn) _ w₂.1 (hpos.next hn) hnext hw₃
      change HiddenKept core U s.1 w₃.2.1
      exact (h₁.trans h₂ hle₂).trans h₃ hle₃

/-! ## Signing -/

/-- The `H_msg` query leaves its digest in the public cache. -/
theorem fst_apply_hmsg_of_mem_support_deferredImpl (r : core.Y) (pk : core.PkSeed)
    (root : core.Y) (msg : List Byte)
    {s : RelabelState (hashSpec core) (DeriveQuery core) (NodeKey core) core.Y ×
      List (DeriveQuery core ⊕ NodeKey core)} {z}
    (hz : z ∈ support ((simulateQ (slhGraph core pkSeed).deferredImpl
      (PublicHash.hmsg core r pk root msg : OracleComp (labSpec core) _)).run s)) :
    z.2.1.1 (.inl (.hmsg r pk root msg)) = some z.1 := by
  rw [show (PublicHash.hmsg core r pk root msg : OracleComp (labSpec core) _) =
      liftM ((labSpec core).query (.inl (.inl (.inr (.inl (.hmsg r pk root msg)))))) from rfl,
    simulateQ_spec_query] at hz
  exact (slhGraph core pkSeed).fst_apply_of_mem_support_deferredImpl_pub (by simp) hz

/-- **Signing keeps the hidden cells undrawn.** A run of lab signing on `msg`, at a key pair whose
secret key is its public key at the public seed `pkSeed`, from a state whose hidden cells are
undrawn for the log `log`, ends in a state whose hidden cells are undrawn for `log` followed by
the new entry. -/
theorem hiddenUndrawn_of_mem_support_labScheme_sign (hd : core.KeyDiscipline vp)
    (optRand : PublicKeyCore core → ProbComp core.Y) {pk : PublicKeyCore core}
    (hpk : pk.pkSeed = pkSeed)
    {log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp core)} (msg : List Byte)
    {s : RelabelState (hashSpec core) (DeriveQuery core) (NodeKey core) core.Y ×
      List (DeriveQuery core ⊕ NodeKey core)} {z}
    (hs : HiddenUndrawn core pk log s.1)
    (hz : z ∈ support ((simulateQ (slhGraph core pkSeed).deferredImpl
      ((labScheme core optRand pkSeed).sign pk pk msg)).run s)) :
    HiddenUndrawn core pk (log ++ [⟨msg, z.1⟩]) z.2.1 := by
  simp only [labScheme, labSignInternal, simulateQ_bind, StateT.run_bind, mem_support_bind_iff,
    simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨w₀, hw₀, w₁, hw₁, w₂, hw₂, w₃, hw₃, w₄, hw₄, rfl⟩ := hz
  have hle₀ := (slhGraph core pkSeed).le_of_mem_support_simulateQ_deferredImpl _ hw₀
  have hle₁ := (slhGraph core pkSeed).le_of_mem_support_simulateQ_deferredImpl _ hw₁
  have hle₂ := (slhGraph core pkSeed).le_of_mem_support_simulateQ_deferredImpl _ hw₂
  have hle₃ := (slhGraph core pkSeed).le_of_mem_support_simulateQ_deferredImpl _ hw₃
  have hle₄ := (slhGraph core pkSeed).le_of_mem_support_simulateQ_deferredImpl _ hw₄
  obtain ⟨U, hU⟩ : ∃ U, U = SignedDigest core pk (log ++ [⟨msg, ⟨w₀.1, w₂.1, w₄.1⟩⟩]) w₄.2.1.1 :=
    ⟨_, rfl⟩
  have hdig : U w₁.1 := by
    rw [hU]
    refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
    rw [hpk]
    exact hle₄.1 (hle₃.1 (hle₂.1
      (fst_apply_hmsg_of_mem_support_deferredImpl pkSeed _ _ _ _ hw₁)))
  have hinit : w₃.2.1.2 (msgCell core (LayerPosition.initial vp (splitDigest vp.params w₁.1))) =
      some w₃.1 := cell_eq_of_mem_support_forsPkFromSigWith pkSeed _ _
        (by rw [← msgAdrs_initial]; exact childCell_msgAdrs _) hw₃
  have huse : UsedPosition U (LayerPosition.initial vp (splitDigest vp.params w₁.1)) :=
    ⟨w₁.1, hdig, LayerPosition.atLayer_zero_eq_initial _ _⟩
  have h₀ := hiddenKept_of_readsUnhidden (U := U) pkSeed hw₀
    (readsUnhidden_randomizer pkSeed _ _)
  have h₁ := hiddenKept_of_readsUnhidden (U := U) pkSeed hw₁ (readsUnhidden_hmsg pkSeed _ _ _ _)
  have h₂ := hiddenKept_of_readsUnhidden (U := U) pkSeed hw₂
    (readsUnhidden_labForsSign pkSeed hd hdig)
  have h₃ := hiddenKept_of_readsUnhidden (U := U) pkSeed hw₃
    (readsUnhidden_forsPkFromSigWith pkSeed hd _ _ _)
  have h₄ := hiddenKept_of_mem_support_labSignFromPosition pkSeed hd _ _ _ _ _ huse hinit hw₄
  have hkept : HiddenKept core U s.1 w₄.2.1 :=
    (((h₀.trans h₁ hle₁).trans h₂ hle₂).trans h₃ hle₃).trans h₄ hle₄
  intro c hc
  rw [← hU] at hc
  have hle : s.1 ≤ w₄.2.1 := hle₀.trans (hle₁.trans (hle₂.trans (hle₃.trans hle₄)))
  rw [hkept c hc]
  refine hs c (hiddenCells_anti (fun _ h ↦ ?_) hle hc)
  rw [hU]
  exact h.mono (fun e he ↦ List.mem_append_left _ he) hle.1

/-! ## The experiment -/

/-- **No hidden cell is drawn before the end fill.** On every run of the lab experiment in
the deferred game over the SLH-DSA graph at the public seed `pkSeed`, from the empty state, the
transcript's public key has public seed `pkSeed`, and the final state draws no cell that is hidden
for the digests the transcript's log signs at that key: no WOTS+ chain step below the one the
drawn honest message selects at a used position, no chain step below the top at an unused one,
and no FORS secret that no signed digest opens. -/
theorem hiddenUndrawn_of_mem_support_deferredImpl_labExperiment [SampleableType core.SkSeed]
    [SampleableType core.SkPrf] (hd : core.KeyDiscipline vp) {e : core.SkSeed ≃ core.Y}
    {optRand : PublicKeyCore core → ProbComp core.Y} {pkSeedDist : ProbComp core.PkSeed}
    (adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist)) {z}
    (hz : z ∈ support ((simulateQ (slhGraph core pkSeed).deferredImpl
      (labExperiment core adv pkSeed)).run ((∅, ∅), []))) :
    z.1.pk.pkSeed = pkSeed ∧ HiddenUndrawn core z.1.pk z.1.log z.2.1 := by
  refine (holds_of_mem_support_run_unforgeableTranscriptExperiment
    (slhGraph core pkSeed).deferredImpl
    (I := fun pk sk log s ↦ sk = pk ∧ pk.pkSeed = pkSeed ∧ HiddenUndrawn core pk log s.1)
    (allowed := IsAmbientLabQuery core) ?_ ?_ ?_ ?_ (labAdversary core adv pkSeed)
    (allQueriesSatisfy_labAdversary_main adv) hz).2
  · intro w hw
    simp only [labScheme, simulateQ_bind, StateT.run_bind, mem_support_bind_iff, simulateQ_pure,
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    refine ⟨rfl, rfl, fun c hc ↦ ?_⟩
    exact (hiddenKept_of_readsUnhidden pkSeed hw' (readsUnhidden_labXmssNode pkSeed hd _ _ _) c
      hc).trans rfl
  · rintro ((t | _) | _) ht pk sk log s ⟨hsk, hpk, hs⟩ w hw
    · exact ⟨hsk, hpk, hiddenUndrawn_of_mem_support_deferredImpl hd pkSeed hs hw⟩
    · exact ht.elim
    · exact ht.elim
  · rintro pk sk msg log s ⟨rfl, hpk, hs⟩ w hw
    exact ⟨rfl, hpk, hiddenUndrawn_of_mem_support_labScheme_sign pkSeed hd _ hpk msg hs hw⟩
  · rintro pk sk log msg sig s hI w hw
    refine AllQueriesSatisfy.holds_of_mem_support_run_simulateQ
      (allQueriesSatisfy_labScheme_verify optRand pk msg sig)
      (fun s ↦ sk = pk ∧ pk.pkSeed = pkSeed ∧ HiddenUndrawn core pk log s.1) ?_ hI hw
    rintro ((t | _) | _) ht s' ⟨hsk, hpk, hs⟩ w' hw'
    · exact ⟨hsk, hpk, hiddenUndrawn_of_mem_support_deferredImpl hd pkSeed hs hw'⟩
    · exact ht.elim
    · exact ht.elim

/-! ## The root cell -/

/-- A lab XMSS node above the leaves leaves its own cell drawn at its value. -/
theorem cell_of_mem_support_labXmssNode {pkSeed : core.PkSeed} (base : Adrs) (z t : ℕ)
    (hmem : xmssNodeAdrs base (z + 1) t ∈ constructionAddresses vp)
    {s : LabState core × List (DeriveQuery core ⊕ NodeKey core)} {w}
    (hw : w ∈ support ((simulateQ (slhGraph core pkSeed).deferredImpl
      (labXmssNode core base (z + 1) t)).run s)) :
    w.2.1.2 (.inr ⟨_, _, hmem, rfl⟩) = some w.1 := by
  simp only [labXmssNode, PerfectMerkleTree.merkleRootM, xmssNodeHashWith, labH,
    labNode_of_mem core hmem, readCell, simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
    at hw
  obtain ⟨_, -, _, -, hw⟩ := hw
  rw [simulateQ_HasQuery_query, CanonicalGraph.deferredImpl_run_read, support_map] at hw
  obtain ⟨y, hy, rfl⟩ := hw
  exact (RelabelState.le_and_cell_eq_of_mem_support_drawCell hy).2

/-- **The root cell holds `PK.root`** at the end of every deferred run of the lab experiment. -/
theorem cell_rootNode_of_mem_support_deferredImpl_labExperiment [SampleableType core.SkSeed]
    [SampleableType core.SkPrf] {pkSeed : core.PkSeed}
    {e : core.SkSeed ≃ core.Y} {optRand : PublicKeyCore core → ProbComp core.Y}
    {pkSeedDist : ProbComp core.PkSeed}
    (adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist)) {z}
    (hz : z ∈ support ((simulateQ (slhGraph core pkSeed).deferredImpl
      (labExperiment core adv pkSeed)).run ((∅, ∅), []))) :
    z.2.1.2 (.inr (rootNode core)) = some z.1.pk.pkRoot := by
  have hmono : ∀ {α : Type} (oa : OracleComp (labSpec core) α) (pk : PublicKeyCore core) s,
      s.1.2 (.inr (rootNode core)) = some pk.pkRoot →
        ∀ w ∈ support ((simulateQ (slhGraph core pkSeed).deferredImpl oa).run s),
          w.2.1.2 (.inr (rootNode core)) = some pk.pkRoot :=
    fun oa _ s h w hw ↦ ((slhGraph core pkSeed).le_of_mem_support_simulateQ_deferredImpl oa hw).2 h
  refine holds_of_mem_support_run_unforgeableTranscriptExperiment
    (slhGraph core pkSeed).deferredImpl
    (I := fun pk _ _ s ↦ s.1.2 (.inr (rootNode core)) = some pk.pkRoot)
    (allowed := IsAmbientLabQuery core) ?_ ?_ ?_ ?_ (labAdversary core adv pkSeed)
    (allQueriesSatisfy_labAdversary_main adv) hz
  · intro w hw
    simp only [labScheme, simulateQ_bind, StateT.run_bind, mem_support_bind_iff, simulateQ_pure,
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    obtain ⟨hp', hhp⟩ : ∃ hp', vp.params.hp = hp' + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos vp.valid.hp_pos).symm⟩
    have hmem : xmssNodeAdrs (GeneralHypertree.layerAdrs (vp.params.d - 1) 0) (hp' + 1) 0 ∈
        constructionAddresses vp := hhp ▸ rootAdrs_mem_constructionAddresses
    have hκ : rootNode core = ⟨_, _, hmem, rfl⟩ := Subtype.ext (by simp [rootNode, rootAdrs, hhp])
    rw [labKeygen, hhp] at hw'
    rw [hκ]
    exact cell_of_mem_support_labXmssNode _ _ _ hmem hw'
  · intro t _ pk _ _ s h w hw
    exact ((slhGraph core pkSeed).le_of_mem_support_deferredImpl hw).2 h
  · intro pk _ msg _ s h w hw
    exact hmono _ pk s h w hw
  · intro pk _ _ msg sig s h w hw
    exact hmono _ pk s h w hw

end SLHDSA.Security
