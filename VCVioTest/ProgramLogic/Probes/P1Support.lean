module

public import VCVio
public meta import VCVio.ProgramLogic.Tactics
public import Mathlib.Util.CountHeartbeats

-- A probe: its proofs are measurements, not library code, so Mathlib's style set is off.
set_option linter.mathlibStandardSet false

/-!
# Probe P1: core-first support invariant for the Merkle batch verifier

Re-proves `batchProofEvaluatesInCache_of_mem_support_getPutativeBatchRootM`
(`VCVio/CryptoFoundations/MerkleTree/BatchExtractability.lean`) through a necessary-reading core
triple in weakest-precondition form, `⦃ fun c => ∀ r c', c ≤ c' → Inv c' r → post r c' ⦄`, whose
`c ≤ c'` is the monotone frame of the caching oracle. `original` is the library proof copied
verbatim; `batchRoot_wp` / `coreFirst` is the core-first proof with a per-query spec only;
`batchRoot_wp2` adds structural `simulateQ` specs (candidate library additions).
-/

public section

namespace VCVioTest.ProgramLogic.Probes.P1Support

open OracleSpec OracleComp BinaryTree InductiveMerkleTree MerkleTreeBatchExtractability
open OracleComp.ProgramLogic Std.WP

universe u

variable {Query Y : Type} {Address : Type u}

/-! ## The original proof, copied verbatim -/

#count_heartbeats in
theorem original
    [DecidableEq Query]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address)
    {selector : LeafData Bool s} (values : SelectedValues Y selector)
    (proof : BatchProof Y selector) (root : Y)
    (cache₀ cache₁ : (Query →ₒ Y).QueryCache)
    (hmem : (root, cache₁) ∈ support
      ((simulateQ (Query →ₒ Y).cachingOracle
        (getPutativeBatchRootM model addressKey values proof)).run cache₀)) :
    BatchProofEvaluatesInCache model addressKey cache₁ values proof root := by
  induction proof generalizing root cache₀ cache₁ with
  | leaf =>
      simp only [getPutativeBatchRootM,
        AddressedMerkleTree.getPutativeBatchRootAddressedM, simulateQ_pure,
        StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hmem
      exact congrArg Prod.fst hmem
  | internalBoth leftProof rightProof ihLeft ihRight =>
      simp only [getPutativeBatchRootM,
        AddressedMerkleTree.getPutativeBatchRootAddressedM,
        simulateQ_bind, StateT.run_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨leftRoot, cacheLeft⟩, hleft, hmem⟩ := hmem
      obtain ⟨⟨rightRoot, cacheRight⟩, hright, hhash⟩ := hmem
      have hentry : cache₁
          (model.mkQuery (addressKey .ofInternal) (leftRoot, rightRoot)) = some root :=
        OracleComp.cachingOracle_query_caches
          (model.mkQuery (addressKey .ofInternal) (leftRoot, rightRoot))
          cacheRight root cache₁ (by
            simpa only [HasQuery.instOfMonadLift_query,
              cachingOracle.simulateQ_query] using hhash)
      have hleftMono : cacheLeft ≤ cache₁ :=
        (simulateQ_cachingOracle_cache_le
          (getPutativeBatchRootM model
            (fun position => addressKey (.ofRight position)) values.2 rightProof)
          cacheLeft (rightRoot, cacheRight) hright).trans
          (simulateQ_cachingOracle_cache_le
            (liftM ((Query →ₒ Y).query
              (model.mkQuery (addressKey .ofInternal) (leftRoot, rightRoot))))
            cacheRight (root, cache₁) hhash)
      have hrightMono : cacheRight ≤ cache₁ :=
        simulateQ_cachingOracle_cache_le
          (liftM ((Query →ₒ Y).query
            (model.mkQuery (addressKey .ofInternal) (leftRoot, rightRoot))))
          cacheRight (root, cache₁) hhash
      exact ⟨leftRoot, rightRoot,
        batchProofEvaluatesInCache_mono model
          (fun position => addressKey (.ofLeft position)) hleftMono values.1 leftProof leftRoot
          (ihLeft (fun position => addressKey (.ofLeft position)) values.1 leftRoot
            cache₀ cacheLeft hleft),
        batchProofEvaluatesInCache_mono model
          (fun position => addressKey (.ofRight position)) hrightMono values.2 rightProof rightRoot
          (ihRight (fun position => addressKey (.ofRight position)) values.2 rightRoot
            cacheLeft cacheRight hright),
        hentry⟩
  | pruneRight hright rightRoot leftProof ih =>
      simp only [getPutativeBatchRootM,
        AddressedMerkleTree.getPutativeBatchRootAddressedM,
        simulateQ_bind, StateT.run_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨leftRoot, cacheLeft⟩, hleft, hhash⟩ := hmem
      have hentry : cache₁
          (model.mkQuery (addressKey .ofInternal) (leftRoot, rightRoot)) = some root :=
        OracleComp.cachingOracle_query_caches
          (model.mkQuery (addressKey .ofInternal) (leftRoot, rightRoot))
          cacheLeft root cache₁ (by
            simpa only [HasQuery.instOfMonadLift_query,
              cachingOracle.simulateQ_query] using hhash)
      have hmono : cacheLeft ≤ cache₁ :=
        simulateQ_cachingOracle_cache_le
          (liftM ((Query →ₒ Y).query
            (model.mkQuery (addressKey .ofInternal) (leftRoot, rightRoot))))
          cacheLeft (root, cache₁) hhash
      exact ⟨leftRoot,
        batchProofEvaluatesInCache_mono model
          (fun position => addressKey (.ofLeft position)) hmono values.1 leftProof leftRoot
          (ih (fun position => addressKey (.ofLeft position)) values.1 leftRoot
            cache₀ cacheLeft hleft),
        hentry⟩
  | pruneLeft hleft leftRoot rightProof ih =>
      simp only [getPutativeBatchRootM,
        AddressedMerkleTree.getPutativeBatchRootAddressedM,
        simulateQ_bind, StateT.run_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨rightRoot, cacheRight⟩, hright, hhash⟩ := hmem
      have hentry : cache₁
          (model.mkQuery (addressKey .ofInternal) (leftRoot, rightRoot)) = some root :=
        OracleComp.cachingOracle_query_caches
          (model.mkQuery (addressKey .ofInternal) (leftRoot, rightRoot))
          cacheRight root cache₁ (by
            simpa only [HasQuery.instOfMonadLift_query,
              cachingOracle.simulateQ_query] using hhash)
      have hmono : cacheRight ≤ cache₁ :=
        simulateQ_cachingOracle_cache_le
          (liftM ((Query →ₒ Y).query
            (model.mkQuery (addressKey .ofInternal) (leftRoot, rightRoot))))
          cacheRight (root, cache₁) hhash
      exact ⟨rightRoot,
        batchProofEvaluatesInCache_mono model
          (fun position => addressKey (.ofRight position)) hmono values.2 rightProof rightRoot
          (ih (fun position => addressKey (.ofRight position)) values.2 rightRoot
            cache₀ cacheRight hright),
        hentry⟩

/-! ## Core-first proof -/

open scoped OracleComp.Necessary

set_option experimental.vcgen true

section CoreFirst

variable [DecidableEq Query]

#count_heartbeats in
/-- WP-form per-query spec: the cache grows and records the answer. -/
@[spec high]
theorem cachingOracle_wp (t : Query) (post : Y → (Query →ₒ Y).QueryCache → Prop) :
    ⦃ fun c => ∀ v c', c ≤ c' → c' t = some v → post v c' ⦄
      ((Query →ₒ Y).cachingOracle t :
        StateT (Query →ₒ Y).QueryCache (OracleComp (Query →ₒ Y)) Y)
    ⦃ post ⦄ := by
  rw [cachingOracle.apply_eq]
  vcgen with finish

#count_heartbeats in
theorem batchRoot_wp (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {s : Skeleton} (addressKey : SkeletonInternalIndex s → Address)
    {selector : LeafData Bool s} (values : SelectedValues Y selector)
    (proof : BatchProof Y selector) (post : Y → (Query →ₒ Y).QueryCache → Prop) :
    ⦃ fun c => ∀ r c', c ≤ c' →
        BatchProofEvaluatesInCache model addressKey c' values proof r → post r c' ⦄
      (simulateQ (Query →ₒ Y).cachingOracle
        (AddressedMerkleTree.getPutativeBatchRootAddressedM
          (fun p l r => liftM ((Query →ₒ Y).query (model.mkQuery (addressKey p) (l, r))))
          values proof) :
        StateT (Query →ₒ Y).QueryCache (OracleComp (Query →ₒ Y)) Y)
    ⦃ post ⦄ := by
  induction proof generalizing post with
  | leaf =>
    simp only [AddressedMerkleTree.getPutativeBatchRootAddressedM, simulateQ_pure]
    vcgen
    grind [BatchProofEvaluatesInCache]
  | internalBoth leftProof rightProof ihLeft ihRight =>
    simp only [AddressedMerkleTree.getPutativeBatchRootAddressedM,
      simulateQ_bind, cachingOracle.simulateQ_query]
    vcgen [ihLeft, ihRight]
    grind [batchProofEvaluatesInCache_mono, BatchProofEvaluatesInCache]
  | pruneRight _ _ _ ih =>
    simp only [AddressedMerkleTree.getPutativeBatchRootAddressedM,
      simulateQ_bind, cachingOracle.simulateQ_query]
    vcgen [ih]
    grind [batchProofEvaluatesInCache_mono, BatchProofEvaluatesInCache]
  | pruneLeft _ _ _ ih =>
    simp only [AddressedMerkleTree.getPutativeBatchRootAddressedM,
      simulateQ_bind, cachingOracle.simulateQ_query]
    vcgen [ih]
    grind [batchProofEvaluatesInCache_mono, BatchProofEvaluatesInCache]

#count_heartbeats in
theorem coreFirst
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address)
    {selector : LeafData Bool s} (values : SelectedValues Y selector)
    (proof : BatchProof Y selector) (root : Y)
    (cache₀ cache₁ : (Query →ₒ Y).QueryCache)
    (hmem : (root, cache₁) ∈ support
      ((simulateQ (Query →ₒ Y).cachingOracle
        (getPutativeBatchRootM model addressKey values proof)).run cache₀)) :
    BatchProofEvaluatesInCache model addressKey cache₁ values proof root :=
  (triple_stateT_iff_forall_support _ _ _ _).mp
    (batchRoot_wp model addressKey values proof
      fun r c => BatchProofEvaluatesInCache model addressKey c values proof r)
    cache₀ (fun _ _ _ h => h) root cache₁ hmem

end CoreFirst

/-! ## Variant: generic `simulateQ` structural specs (candidate library additions) -/

section SimulateQSpecs

universe w w'

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {m : Type → Type} [Monad m]
  {Pred : Type w} {EPred : Type w'} [Assertion Pred] [Assertion EPred]
  [WPMonad m Pred EPred] {α β : Type}

#count_heartbeats in
/-- `simulateQ` of a bind is the bind of the simulations (WP form). -/
@[spec]
theorem Spec.simulateQ_bind (h : QueryImpl spec m) (x : OracleComp spec α)
    (f : α → OracleComp spec β) (post : β → Pred) (epost : EPred) :
    Triple (simulateQ h (x >>= f))
      (wp (simulateQ h x >>= fun a => simulateQ h (f a)) post epost) post epost :=
  ⟨by rw [_root_.simulateQ_bind]⟩

#count_heartbeats in
/-- `simulateQ` of `pure` is `pure` (WP form). -/
@[spec]
theorem Spec.simulateQ_pure (h : QueryImpl spec m) (a : α) (post : α → Pred) (epost : EPred) :
    Triple (simulateQ h (pure a : OracleComp spec α)) (post a) post epost :=
  Triple.pure a Lean.Order.PartialOrder.rel_refl

#count_heartbeats in
open scoped OracleComp.Necessary in
/-- `simulateQ` of a lifted query runs the handler (WP form, `StateT` over `OracleComp`). -/
@[spec high]
theorem Spec.simulateQ_query_stateT {σ : Type} (h : QueryImpl spec (StateT σ (OracleComp spec)))
    (t : spec.Domain) (post : spec.Range t → σ → Prop) :
    ⦃ wp (h t) post Lean.Order.bot ⦄
      (simulateQ h (liftM (OracleSpec.query t) : OracleComp spec (spec.Range t)) :
        StateT σ (OracleComp spec) (spec.Range t)) ⦃ post ⦄ :=
  ⟨by rw [simulateQ_spec_query]; exact Lean.Order.PartialOrder.rel_refl⟩

end SimulateQSpecs

section CoreFirst2

variable [DecidableEq Query]

#count_heartbeats in
theorem batchRoot_wp2 (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {s : Skeleton} (addressKey : SkeletonInternalIndex s → Address)
    {selector : LeafData Bool s} (values : SelectedValues Y selector)
    (proof : BatchProof Y selector) (post : Y → (Query →ₒ Y).QueryCache → Prop) :
    ⦃ fun c => ∀ r c', c ≤ c' →
        BatchProofEvaluatesInCache model addressKey c' values proof r → post r c' ⦄
      (simulateQ (Query →ₒ Y).cachingOracle
        (AddressedMerkleTree.getPutativeBatchRootAddressedM
          (fun p l r => liftM ((Query →ₒ Y).query (model.mkQuery (addressKey p) (l, r))))
          values proof) :
        StateT (Query →ₒ Y).QueryCache (OracleComp (Query →ₒ Y)) Y)
    ⦃ post ⦄ := by
  induction proof generalizing post with
  | leaf =>
    simp only [AddressedMerkleTree.getPutativeBatchRootAddressedM]
    vcgen
    grind [BatchProofEvaluatesInCache]
  | internalBoth _ _ ihLeft ihRight =>
    simp only [AddressedMerkleTree.getPutativeBatchRootAddressedM]
    vcgen [ihLeft, ihRight]
    grind [batchProofEvaluatesInCache_mono, BatchProofEvaluatesInCache]
  | pruneRight _ _ _ ih | pruneLeft _ _ _ ih =>
    simp only [AddressedMerkleTree.getPutativeBatchRootAddressedM]
    vcgen [ih]
    grind [batchProofEvaluatesInCache_mono, BatchProofEvaluatesInCache]

#count_heartbeats in
theorem verifyOpening_original [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address) (root : Y)
    (opening : InductiveMerkleTree.BatchOpening Y s)
    (cache₀ cache₁ : (Query →ₒ Y).QueryCache)
    (hmem : (true, cache₁) ∈ support
      ((simulateQ (Query →ₒ Y).cachingOracle
        (verifyOpening model addressKey root opening)).run cache₀)) :
    BatchProofEvaluatesInCache model addressKey cache₁ opening.values opening.proof root := by
  unfold verifyOpening AddressedMerkleTree.verifyBatchProofAddressedM at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨putativeRoot, cacheMid⟩, hroot, hfinal⟩ := hmem
  simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff,
    Prod.mk.injEq] at hfinal
  obtain ⟨haccepted, rfl⟩ := hfinal
  have hputative : putativeRoot = root := by
    simpa only [beq_iff_eq] using haccepted.symm
  subst root
  exact batchProofEvaluatesInCache_of_mem_support_getPutativeBatchRootM model addressKey
    opening.values opening.proof putativeRoot cache₀ cache₁ hroot

#count_heartbeats in
/-- Downstream reuse: the verifier corollary (original proof: 11 lines). -/
theorem verifyOpening_coreFirst [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y) {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address) (root : Y)
    (opening : InductiveMerkleTree.BatchOpening Y s)
    (cache₀ cache₁ : (Query →ₒ Y).QueryCache)
    (hmem : (true, cache₁) ∈ support
      ((simulateQ (Query →ₒ Y).cachingOracle
        (verifyOpening model addressKey root opening)).run cache₀)) :
    BatchProofEvaluatesInCache model addressKey cache₁ opening.values opening.proof root := by
  refine (triple_stateT_iff_forall_support _ (fun _ => True)
    (fun b c => b = true → BatchProofEvaluatesInCache model addressKey c opening.values
      opening.proof root) Lean.Order.bot).mp ?_ cache₀ trivial true cache₁ hmem rfl
  simp only [verifyOpening, AddressedMerkleTree.verifyBatchProofAddressedM]
  vcgen [batchRoot_wp2]
  grind

/-- Candidate library addition: the monotone frame of a whole caching simulation, in WP form.
As a low-priority spec it is the fallback for opaque sub-programs (adversaries): any
upward-closed cache invariant survives them. -/
@[spec low]
theorem simulateQ_cachingOracle_wp {α : Type} (oa : OracleComp (Query →ₒ Y) α)
    (post : α → (Query →ₒ Y).QueryCache → Prop) :
    ⦃ fun c => ∀ a c', c ≤ c' → post a c' ⦄
      (simulateQ (Query →ₒ Y).cachingOracle oa :
        StateT (Query →ₒ Y).QueryCache (OracleComp (Query →ₒ Y)) α) ⦃ post ⦄ :=
  (triple_stateT_iff_forall_support _ _ _ _).mpr fun c h a c' hmem =>
    h a c' (simulateQ_cachingOracle_cache_le oa c (a, c') hmem)

/-- The frame in use: an opaque run followed by a query keeps an upward-closed invariant.
(Stated with `P c ∧ True`: the eta-reduced precondition `fun c => P c`, i.e. `P`, makes core
`vcgen` fail with "failed to apply `Lean.Order.le_of_forall_le`", and VCVio's route then
silently hands the goal to its own pipeline, which returns a raw `MonadAttach.CanReturn` VC.) -/
example {α : Type} (oa : OracleComp (Query →ₒ Y) α) (t : Query)
    (P : (Query →ₒ Y).QueryCache → Prop) (hP : ∀ c c', c ≤ c' → P c → P c') :
    ⦃ fun c => P c ∧ True ⦄
      (simulateQ (Query →ₒ Y).cachingOracle (oa >>= fun _ => liftM ((Query →ₒ Y).query t)) :
        StateT (Query →ₒ Y).QueryCache (OracleComp (Query →ₒ Y)) Y)
    ⦃ fun v c => P c ∧ c t = some v ⦄ := by
  vcgen
  grind

end CoreFirst2

end VCVioTest.ProgramLogic.Probes.P1Support
