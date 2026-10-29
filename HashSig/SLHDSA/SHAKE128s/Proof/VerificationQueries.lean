/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.Experiment
public import HashSig.SLHDSA.SHAKE128s.Proof.Checksum
public import HashSig.SLHDSA.SHAKE128s.Generic.ExactQueryCount
public import VCVio.OracleComp.QueryTracking.QueryBound.Exact.Sequence
public import VCVio.OracleComp.QueryTracking.QueryBound.Exact.Cost
public import VCVio.OracleComp.SimSemantics.StateT.Basic

/-!
# Oracle-call accounting for the SLH-DSA verifier

Exact and bounded hash-call counts for the concrete SLH-DSA verifier. `ExactQueryCount` facts are
derived for the hash, chain, WOTS and FORS verifiers; `Bounds` packages lower and upper bounds on
the cost of every reachable trace under every oracle implementation, and `verify_bounds` shows
that verification makes between 569 and 3824 hash calls. `Bounds.simulated` transfers those
bounds through any stateful implementation, such as a cached random oracle.
-/

public section

open OracleComp OracleSpec
open scoped BigOperators

namespace SLHDSA.SHAKE128s.VerificationQueries

open Generic (ExactQueryCount)

variable {ι : Type} {spec : OracleSpec ι} {α β : Type}

/-- Exact query counts add along a bind whose continuation has a uniform exact count. -/
theorem exact_bind {computation : OracleComp spec α} {count : Nat}
    (h : ExactQueryCount computation count) (next : α → OracleComp spec β)
    (nextCount : Nat) (hnext : ∀ value, ExactQueryCount (next value) nextCount) :
    ExactQueryCount (computation >>= next) (count + nextCount) := by
  exact OracleComp.QueryBound.ExactQueryCount.bind h next nextCount hnext

/-- Mapping over a computation preserves its exact query count. -/
theorem exact_map {computation : OracleComp spec α} {count : Nat}
    (h : ExactQueryCount computation count) (f : α → β) :
    ExactQueryCount (f <$> computation) count := by
  exact OracleComp.QueryBound.ExactQueryCount.map h f

/-- One hash call makes exactly one query. -/
theorem hash_exact (input : Bytes) :
    ExactQueryCount (Hashing.hash input : OracleComp HashSpec HashOutput) 1 := by
  exact .query input (fun output => pure output) 0 (fun output => .pure output)

/-- A truncated hash call makes exactly one query. -/
theorem shortHash_exact (input : Bytes) :
    ExactQueryCount (Hashing.shortHash input : OracleComp HashSpec Digest) 1 := by
  simpa [Hashing.shortHash, map_eq_bind_pure_comp] using
    exact_map (hash_exact input) Hashing.truncate

/-- A tweakable hash call makes exactly one query. -/
theorem tweakable_exact (seed : Digest) (address : Address) (payload : Bytes) :
    ExactQueryCount (Hashing.tweakable seed address payload : OracleComp HashSpec Digest) 1 :=
  shortHash_exact _

/-- Advancing a WOTS chain by `steps` makes exactly `steps` queries. -/
theorem chain_exact (publicSeed : Digest) (address : Address) (start steps : Nat)
    (value : Digest) :
    ExactQueryCount (Wots.chain publicSeed address start steps value : OracleComp HashSpec Digest)
      steps := by
  induction steps generalizing start value with
  | zero => exact .pure value
  | succ steps ih =>
    rw [Wots.chain]
    simpa only [Nat.add_comm] using
      exact_bind (tweakable_exact _ _ _) _ steps (fun next => ih (start + 1) next)

/-- Finite oracle sequencing has the function-valued finite traversal's execution order. -/
private theorem sequenceFin_eq_fin_mOfFn {ι : Type} {spec : OracleSpec ι} {α : Type}
    (size : Nat) (f : Fin size → OracleComp spec α) :
    SLHDSA.SHAKE128s.sequenceFin size f = Fin.mOfFn size f := by
  induction size with
  | zero => rfl
  | succ size ih =>
    simp only [SLHDSA.SHAKE128s.sequenceFin, Fin.mOfFn_succ, ih]
    rfl

/-- Sequencing a family of computations adds their exact query counts. -/
theorem sequenceFin_exact {size : Nat} (f : Fin size → OracleComp HashSpec α)
    (count : Fin size → Nat) (hcount : ∀ i, ExactQueryCount (f i) (count i)) :
    ExactQueryCount (sequenceFin size f) (∑ i, count i) := by
  rw [sequenceFin_eq_fin_mOfFn]
  exact OracleComp.QueryBound.ExactQueryCount.fin_mOfFn f count hcount

/-- A monadic fold whose step makes `count` queries makes `length * count` queries. -/
theorem foldlM_exact (items : List α) (f : β → α → OracleComp HashSpec β)
    (count : Nat) (hcount : ∀ value item, ExactQueryCount (f value item) count) (initial : β) :
    ExactQueryCount (items.foldlM f initial) (items.length * count) := by
  exact OracleComp.QueryBound.ExactQueryCount.foldlM items f count hcount initial

/-- The remaining chain steps over the encoded message are the verifier's chain-call count. -/
theorem encoded_chain_steps (message : Digest) :
    (∑ i : Fin chains, (w - 1 - (Checksum.encode message i).val)) =
      Checksum.chainVerificationCalls (Checksum.messageDigit message) := by
  change (∑ i : Fin (messageDigits + checksumDigits), _) = _
  rw [Fin.sum_univ_add]
  rfl

/-- WOTS public-key recovery makes its chain calls plus one compression call. -/
theorem wots_exact (signature : WotsSignature) (message publicSeed : Digest)
    (address : Address) :
    ExactQueryCount
      (Wots.publicKeyFromSignature signature message publicSeed address :
        OracleComp HashSpec Digest)
      (Checksum.chainVerificationCalls (Checksum.messageDigit message) + 1) := by
  unfold Wots.publicKeyFromSignature
  rw [← encoded_chain_steps message]
  exact exact_bind (sequenceFin_exact _ _ (fun i => chain_exact _ _ _ _ _)) _ 1
    (fun _ => tweakable_exact _ _ _)

/-- FORS public-key recovery makes exactly 183 hash calls. -/
theorem fors_exact (signature : ForsSignature) (indices : Fors.Indices)
    (publicSeed : Digest) (address : Address) :
    ExactQueryCount
      (Fors.publicKeyFromSignature signature indices publicSeed address :
        OracleComp HashSpec Digest)
      183 := by
  unfold Fors.publicKeyFromSignature
  have hroots : ∀ i : Fin forsTrees, ExactQueryCount
      (do
        let index := i.val * 2 ^ forsHeight + (indices i).val
        let leaf ← Hashing.tweakable publicSeed (Fors.nodeAddress address 0 index)
          (bytesBE n (signature i).secret)
        (List.finRange forsHeight).foldlM (fun value j => do
          let payload := if (indices i).val / 2 ^ j.val % 2 = 0 then
            bytesBE n value ++ bytesBE n ((signature i).authentication j)
            else bytesBE n ((signature i).authentication j) ++ bytesBE n value
          Hashing.tweakable publicSeed
            (Fors.nodeAddress address (j.val + 1) (index / 2 ^ (j.val + 1))) payload) leaf :
          OracleComp HashSpec Digest) (1 + forsHeight) := by
    intro i
    refine exact_bind (tweakable_exact _ _ _) _ forsHeight (fun leaf => ?_)
    simpa only [List.length_finRange, Nat.mul_one] using
      foldlM_exact (List.finRange forsHeight) _ 1 (fun _ _ => tweakable_exact _ _ _) leaf
  have h : (∑ _ : Fin forsTrees, (1 + forsHeight)) + 1 = 183 := by
    norm_num [forsTrees, forsHeight]
  rw [← h]
  exact exact_bind (sequenceFin_exact _ (fun _ => 1 + forsHeight) hroots) _ 1
    (fun _ => tweakable_exact _ _ _)

/-! ### Support elimination under `LawfulMonadAttach`

The runtime monads below carry only `LawfulMonadAttach`, whose elimination rules suffice for
pathwise cost bounds. -/

section LawfulAttach

variable {m : Type → Type} [Monad m] [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m]

/-- Stateful simulation only shrinks the support of the free computation. -/
private theorem fst_mem_support_of_mem_support_simulateQ_run {σ γ : Type}
    (impl : QueryImpl HashSpec (StateT σ m)) (oa : OracleComp HashSpec γ) (s : σ)
    (p : γ × σ) (hp : p ∈ support ((simulateQ impl oa).run s)) : p.1 ∈ support oa := by
  induction oa using OracleComp.inductionOn generalizing s p with
  | pure x =>
    rw [simulateQ_pure, StateT.run_pure] at hp
    rw [← LawfulMonadAttach.eq_of_canReturn_pure hp]
    simp
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at hp
    obtain ⟨q, -, hq⟩ := LawfulMonadAttach.canReturn_bind_imp' hp
    have := ih q.1 q.2 p hq
    simp only [support_bind, Set.mem_iUnion, exists_prop]
    exact ⟨q.1, mem_support_query t q.1, this⟩

end LawfulAttach

/-- Exact syntactic call counts remain exact for every runtime, including a cached shared oracle. -/
theorem exact_cost {m : Type → Type} [Monad m] [LawfulMonad m]
    [MonadAttach m] [LawfulMonadAttach m]
    (impl : QueryImpl HashSpec m) {computation : OracleComp HashSpec α} {count : Nat}
    (hexact : ExactQueryCount computation count) :
    AddWriterT.QueryCostExactly (simulateQ impl.withUnitCost computation) count := by
  exact OracleComp.QueryBound.ExactQueryCount.queryCostExactly impl hexact

/-- Every reachable trace has the given bounds, under every possible oracle implementation. -/
@[expose, irreducible]
def Bounds (computation : OracleComp HashSpec α) (lower upper : Nat) : Prop :=
  ∀ (m : Type → Type) [Monad m] [LawfulMonad m]
    [MonadAttach m] [LawfulMonadAttach m] (impl : QueryImpl HashSpec m),
    AddWriterT.QueryBoundedBelowBy (simulateQ impl.withUnitCost computation) lower ∧
      AddWriterT.QueryBoundedAboveBy (simulateQ impl.withUnitCost computation) upper

/-- An exact query count lies within any enclosing bounds. -/
theorem Bounds.of_exact {computation : OracleComp HashSpec α} {count lower upper : Nat}
    (hexact : ExactQueryCount computation count) (hlower : lower ≤ count) (hupper : count ≤ upper) :
    Bounds computation lower upper := by
  unfold Bounds
  intro m _ _ _ _ impl
  have h := exact_cost impl hexact
  exact ⟨AddWriterT.queryBoundedBelowBy_mono h.toBelow hlower,
    AddWriterT.queryBoundedAboveBy_mono h.toAbove hupper⟩

/-- Bounds add along a bind. -/
theorem Bounds.bind {computation : OracleComp HashSpec α} {next : α → OracleComp HashSpec β}
    {lower upper nextLower nextUpper : Nat} (h : Bounds computation lower upper)
    (hnext : ∀ value, Bounds (next value) nextLower nextUpper) :
    Bounds (computation >>= next) (lower + nextLower) (upper + nextUpper) := by
  unfold Bounds at h hnext ⊢
  intro m _ _ _ _ impl
  rw [simulateQ_bind]
  exact ⟨AddWriterT.LawfulAttach.queryBoundedBelowBy_bind
      (h m impl).1 (fun value => (hnext value m impl).1),
    AddWriterT.LawfulAttach.queryBoundedAboveBy_bind
      (h m impl).2 (fun value => (hnext value m impl).2)⟩

/-- Mapping over a computation preserves its bounds. -/
theorem Bounds.map {computation : OracleComp HashSpec α} {lower upper : Nat}
    (h : Bounds computation lower upper) (f : α → β) :
    Bounds (f <$> computation) lower upper := by
  simpa [map_eq_bind_pure_comp] using
    h.bind (fun value => Bounds.of_exact (.pure (f value)) le_rfl le_rfl)

/-- XMSS root recovery makes between 55 and 520 hash calls. -/
theorem merkle_bounds (index : Fin (2 ^ subtreeHeight)) (signature : XmssSignature)
    (message publicSeed : Digest) (address : Address) :
    Bounds (Merkle.publicKeyFromSignature index signature message publicSeed address) 55 520 := by
  have hwork := Checksum.chainVerificationCalls_bounds (Checksum.messageDigit message)
  unfold Merkle.publicKeyFromSignature
  have hwots := Bounds.of_exact
    (wots_exact signature.wots message publicSeed (Merkle.wotsAddress address index.val))
    (show 46 ≤ _ by omega) (show _ ≤ 511 by omega)
  change Bounds _ (46 + 9) (511 + 9)
  exact hwots.bind (fun leaf => Bounds.of_exact
    (by
      simpa only [List.length_finRange, Nat.mul_one, subtreeHeight] using
        foldlM_exact (List.finRange subtreeHeight) _ 1 (fun _ _ => tweakable_exact _ _ _) leaf)
    le_rfl le_rfl)

/-- Hypertree root recovery over `remaining` layers makes between `remaining * 55` and
`remaining * 520` hash calls. -/
theorem hypertree_root_bounds (publicSeed : Digest) (remaining : Nat)
    (signatures : Fin remaining → XmssSignature) (layer tree : Nat) (leaf : Hypertree.LeafIndex)
    (message : Digest) :
    Bounds (Hypertree.rootFromSignature publicSeed remaining signatures layer tree leaf message)
      (remaining * 55) (remaining * 520) := by
  induction remaining generalizing layer tree leaf message with
  | zero => exact Bounds.of_exact (.pure message) le_rfl le_rfl
  | succ remaining ih =>
    rw [Hypertree.rootFromSignature]
    simpa only [Nat.add_mul, Nat.one_mul, Nat.add_comm] using
      (merkle_bounds leaf (signatures 0) message publicSeed (Hypertree.address layer tree)).bind
        (fun root => ih (fun i => signatures i.succ) (layer + 1)
          (tree / 2 ^ subtreeHeight) (Hypertree.nextLeaf tree) root)

/-- Internal verification makes between 569 and 3824 hash calls. -/
theorem verifyInternal_bounds (pk : PublicKey) (message : Bytes) (signature : Signature) :
    Bounds (Scheme.verifyInternal pk message signature) 569 3824 := by
  have hh : Bounds
      (Hashing.messageDigest signature.randomizer pk message : OracleComp HashSpec HashOutput)
      1 1 := Bounds.of_exact (hash_exact (Hashing.messageInput signature.randomizer pk message))
        le_rfl le_rfl
  have htail (digest : HashOutput) : Bounds
      (do
        let forsKey ← Fors.publicKeyFromSignature signature.fors (MessageDigest.forsIndices digest)
          pk.seed (Scheme.forsAddress digest)
        Hypertree.verify forsKey signature.hypertree pk
          (MessageDigest.treeIndex digest) (MessageDigest.leafIndex digest).toFin)
      (183 + 385) (183 + 3640) := by
    have hf := Bounds.of_exact
      (fors_exact signature.fors (MessageDigest.forsIndices digest) pk.seed
        (Scheme.forsAddress digest))
      le_rfl le_rfl
    refine hf.bind (fun forsKey => ?_)
    unfold Hypertree.verify
    simpa [map_eq_bind_pure_comp, layers] using
      (hypertree_root_bounds pk.seed layers signature.hypertree 0
        (MessageDigest.treeIndex digest).toNat (MessageDigest.leafIndex digest).toFin forsKey).map
        (fun root => root == pk.root)
  exact hh.bind htail

/-- Verifying a well-framed, parsable request makes between 569 and 3824 hash calls. -/
theorem verify_bounds (pk : PublicKey) (request : Message) (wire : Bytes)
    (message : Bytes) (signature : Signature)
    (hframe : request.frame = some message) (hparse : Signature.fromBytes? wire = some signature) :
    Bounds (Scheme.verify pk request wire) 569 3824 := by
  simpa only [Scheme.verify, hframe, hparse] using verifyInternal_bounds pk message signature

/-- Instrument the free computation before interpreting its hash calls. -/
@[expose]
def counted (computation : OracleComp HashSpec α) : OracleComp HashSpec (α × Multiplicative Nat) :=
  (simulateQ (QueryImpl.ofLift HashSpec (OracleComp HashSpec)).withUnitCost computation).run

/-- The bounds survive any stateful implementation and any initial state, including a random-oracle
cache. Instrumentation precedes the implementation, so repeated inputs still count once per call. -/
theorem Bounds.simulated {m : Type → Type} [Monad m] [LawfulMonad m]
    [MonadAttach m] [LawfulMonadAttach m]
    {σ : Type} {computation : OracleComp HashSpec α} {lower upper : Nat}
    (h : Bounds computation lower upper) (impl : QueryImpl HashSpec (StateT σ m)) (initial : σ)
    (result : α × Multiplicative Nat)
    (hresult : result ∈ support ((simulateQ impl (counted computation)).run' initial)) :
    lower ≤ Multiplicative.toAdd result.2 ∧ Multiplicative.toAdd result.2 ≤ upper := by
  have hfree : result ∈ support (counted computation) := by
    rw [StateT.run'_eq] at hresult
    obtain ⟨p, hp, rfl⟩ := LawfulMonadAttach.canReturn_map_imp' hresult
    exact fst_mem_support_of_mem_support_simulateQ_run impl _ initial p hp
  unfold Bounds at h
  have hb := h (OracleComp HashSpec) (QueryImpl.ofLift HashSpec (OracleComp HashSpec))
  exact ⟨hb.1 result hfree, hb.2 result hfree⟩

end SLHDSA.SHAKE128s.VerificationQueries
