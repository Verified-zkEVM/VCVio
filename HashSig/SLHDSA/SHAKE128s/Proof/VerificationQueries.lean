/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.Experiment
public import HashSig.SLHDSA.SHAKE128s.Proof.Checksum
public import HashSig.SLHDSA.SHAKE128s.Generic.ExactQueryCount
public import VCVio.OracleComp.SimSemantics.StateT.Basic

/-! Oracle-call accounting for the concrete SLH-DSA verifier. -/

@[expose] public section

open OracleComp OracleSpec
open scoped BigOperators

set_option maxRecDepth 2000

namespace SlhDsaSecurity.VerificationQueries

open Xmss.Generic (ExactQueryCount)

variable {ι : Type} {spec : OracleSpec ι} {α β : Type}

/-- The generic XMSS lemma carries an unused `Code` instance; this version does not. -/
theorem exact_bind {computation : OracleComp spec α} {count : Nat}
    (h : ExactQueryCount computation count) (next : α → OracleComp spec β)
    (nextCount : Nat) (hnext : ∀ value, ExactQueryCount (next value) nextCount) :
    ExactQueryCount (computation >>= next) (count + nextCount) := by
  induction h with
  | pure value => simpa using hnext value
  | query input rest restCount hrest ih =>
    rw [bind_assoc]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ExactQueryCount.query input (fun output => rest output >>= next)
        (restCount + nextCount) ih

theorem exact_map {computation : OracleComp spec α} {count : Nat}
    (h : ExactQueryCount computation count) (f : α → β) :
    ExactQueryCount (f <$> computation) count := by
  simpa [map_eq_bind_pure_comp] using
    exact_bind h (fun value => pure (f value)) 0 (fun value => .pure (f value))

theorem hash_exact (input : Bytes) :
    ExactQueryCount (Hashing.hash input : OracleComp HashSpec HashOutput) 1 := by
  exact .query input (fun output => pure output) 0 (fun output => .pure output)

theorem shortHash_exact (input : Bytes) :
    ExactQueryCount (Hashing.shortHash input : OracleComp HashSpec Digest) 1 := by
  simpa [Hashing.shortHash, map_eq_bind_pure_comp] using
    exact_map (hash_exact input) Hashing.truncate

theorem tweakable_exact (seed : Digest) (address : Address) (payload : Bytes) :
    ExactQueryCount (Hashing.tweakable seed address payload : OracleComp HashSpec Digest) 1 :=
  shortHash_exact _

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

theorem sequenceFin_exact {size : Nat} (f : Fin size → OracleComp HashSpec α)
    (count : Fin size → Nat) (hcount : ∀ i, ExactQueryCount (f i) (count i)) :
    ExactQueryCount (sequenceFin size f) (∑ i, count i) := by
  induction size with
  | zero => exact .pure Fin.elim0
  | succ size ih =>
    rw [sequenceFin, Fin.sum_univ_succ]
    exact exact_bind (hcount 0) _ (∑ i : Fin size, count i.succ) (fun first => by
      simpa only [map_eq_bind_pure_comp, Function.comp_def] using
        exact_map (ih (fun i => f i.succ) (fun i => count i.succ) (fun i => hcount i.succ))
          (fun rest => (Fin.cases first rest : Fin (size + 1) → α)))

theorem foldlM_exact (items : List α) (f : β → α → OracleComp HashSpec β)
    (count : Nat) (hcount : ∀ value item, ExactQueryCount (f value item) count) (initial : β) :
    ExactQueryCount (items.foldlM f initial) (items.length * count) := by
  induction items generalizing initial with
  | nil => simpa using ExactQueryCount.pure initial
  | cons item items ih =>
    simpa only [List.foldlM_cons, List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm] using
      exact_bind (hcount initial item) _ (items.length * count) (fun value => ih value)

theorem encoded_chain_steps (message : Digest) :
    (∑ i : Fin chains, (w - 1 - (Checksum.encode message i).val)) =
      Checksum.chainVerificationCalls (Checksum.messageDigit message) := by
  change (∑ i : Fin (messageDigits + checksumDigits), _) = _
  rw [Fin.sum_univ_add]
  rfl

theorem wots_exact (signature : WotsSignature) (message publicSeed : Digest)
    (address : Address) :
    ExactQueryCount
      (Wots.publicKeyFromSignature signature message publicSeed address : OracleComp HashSpec Digest)
      (Checksum.chainVerificationCalls (Checksum.messageDigit message) + 1) := by
  unfold Wots.publicKeyFromSignature
  rw [← encoded_chain_steps message]
  exact exact_bind (sequenceFin_exact _ _ (fun i => chain_exact _ _ _ _ _)) _ 1
    (fun _ => tweakable_exact _ _ _)

theorem fors_exact (signature : ForsSignature) (indices : Fors.Indices)
    (publicSeed : Digest) (address : Address) :
    ExactQueryCount
      (Fors.publicKeyFromSignature signature indices publicSeed address : OracleComp HashSpec Digest)
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

private theorem mem_support_run_bind {γ δ : Type} {oa : AddWriterT ℕ m γ}
    {f : γ → AddWriterT ℕ m δ} {z : δ × Multiplicative ℕ} (hz : z ∈ support (oa >>= f).run) :
    ∃ x ∈ support oa.run, ∃ y ∈ support (f x.1).run, z = (y.1, x.2 * y.2) := by
  rw [WriterT.run_bind] at hz
  obtain ⟨⟨a, wa⟩, hx, hy⟩ := LawfulMonadAttach.canReturn_bind_imp' hz
  obtain ⟨⟨b, wb⟩, hb, hzb⟩ := LawfulMonadAttach.canReturn_map_imp' hy
  exact ⟨(a, wa), hx, (b, wb), hb, hzb.symm⟩

private theorem queryBoundedAboveBy_bind' {γ δ : Type} {oa : AddWriterT ℕ m γ}
    {f : γ → AddWriterT ℕ m δ} {n₁ n₂ : ℕ} (h₁ : AddWriterT.QueryBoundedAboveBy oa n₁)
    (h₂ : ∀ a, AddWriterT.QueryBoundedAboveBy (f a) n₂) :
    AddWriterT.QueryBoundedAboveBy (oa >>= f) (n₁ + n₂) := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_support_run_bind hz
  simpa using Nat.add_le_add (h₁ x hx) (h₂ x.1 y hy)

private theorem queryBoundedBelowBy_bind' {γ δ : Type} {oa : AddWriterT ℕ m γ}
    {f : γ → AddWriterT ℕ m δ} {n₁ n₂ : ℕ} (h₁ : AddWriterT.QueryBoundedBelowBy oa n₁)
    (h₂ : ∀ a, AddWriterT.QueryBoundedBelowBy (f a) n₂) :
    AddWriterT.QueryBoundedBelowBy (oa >>= f) (n₁ + n₂) := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_support_run_bind hz
  simpa using Nat.add_le_add (h₁ x hx) (h₂ x.1 y hy)

private theorem queryCostExactly_bind' {γ δ : Type} {oa : AddWriterT ℕ m γ}
    {f : γ → AddWriterT ℕ m δ} {n₁ n₂ : ℕ} (h₁ : AddWriterT.QueryCostExactly oa n₁)
    (h₂ : ∀ a, AddWriterT.QueryCostExactly (f a) n₂) :
    AddWriterT.QueryCostExactly (oa >>= f) (n₁ + n₂) :=
  ⟨queryBoundedAboveBy_bind' h₁.toAbove (fun a => (h₂ a).toAbove),
    queryBoundedBelowBy_bind' h₁.toBelow (fun a => (h₂ a).toBelow)⟩

private theorem queryCostExactly_pure' {γ : Type} (x : γ) :
    AddWriterT.QueryCostExactly (pure x : AddWriterT ℕ m γ) 0 := by
  have h : ∀ z ∈ support (pure x : AddWriterT ℕ m γ).run, Multiplicative.toAdd z.2 = 0 := by
    intro z hz
    rw [WriterT.run_pure] at hz
    rw [← LawfulMonadAttach.eq_of_canReturn_pure hz]
    rfl
  exact ⟨fun z hz => (h z hz).le, fun z hz => (h z hz).ge⟩

private theorem queryCostExactly_addTell' (w : ℕ) :
    AddWriterT.QueryCostExactly (AddWriterT.addTell (M := m) w) w := by
  have h : ∀ z ∈ support (AddWriterT.addTell (M := m) w).run, Multiplicative.toAdd z.2 = w := by
    intro z hz
    rw [AddWriterT.run_addTell] at hz
    rw [← LawfulMonadAttach.eq_of_canReturn_pure hz]
    rfl
  exact ⟨fun z hz => (h z hz).le, fun z hz => (h z hz).ge⟩

private theorem queryCostExactly_monadLift' {γ : Type} (x : m γ) :
    AddWriterT.QueryCostExactly (monadLift x : AddWriterT ℕ m γ) 0 := by
  have h : ∀ z ∈ support (monadLift x : AddWriterT ℕ m γ).run, Multiplicative.toAdd z.2 = 0 := by
    intro z hz
    rw [WriterT.run_monadLift] at hz
    obtain ⟨a, -, rfl⟩ := LawfulMonadAttach.canReturn_map_imp' hz
    rfl
  exact ⟨fun z hz => (h z hz).le, fun z hz => (h z hz).ge⟩

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
  induction hexact with
  | pure value => simpa using queryCostExactly_pure' (m := m) value
  | query input next count hnext ih =>
    rw [simulateQ_bind, simulateQ_spec_query]
    have hquery : AddWriterT.QueryCostExactly (impl.withUnitCost input) 1 := by
      rw [QueryImpl.withUnitCost_apply]
      simpa only [Nat.add_zero] using queryCostExactly_bind'
        (queryCostExactly_addTell' (m := m) 1)
        (fun _ => queryCostExactly_monadLift' (impl input))
    simpa only [Nat.add_comm] using
      queryCostExactly_bind' hquery ih

/-- Every reachable trace has the given bounds, under every possible oracle implementation. -/
@[irreducible] def Bounds (computation : OracleComp HashSpec α) (lower upper : Nat) : Prop :=
  ∀ (m : Type → Type) [Monad m] [LawfulMonad m]
    [MonadAttach m] [LawfulMonadAttach m] (impl : QueryImpl HashSpec m),
    AddWriterT.QueryBoundedBelowBy (simulateQ impl.withUnitCost computation) lower ∧
      AddWriterT.QueryBoundedAboveBy (simulateQ impl.withUnitCost computation) upper

theorem Bounds.of_exact {computation : OracleComp HashSpec α} {count lower upper : Nat}
    (hexact : ExactQueryCount computation count) (hlower : lower ≤ count) (hupper : count ≤ upper) :
    Bounds computation lower upper := by
  unfold Bounds
  intro m _ _ _ _ impl
  have h := exact_cost impl hexact
  exact ⟨AddWriterT.queryBoundedBelowBy_mono h.toBelow hlower,
    AddWriterT.queryBoundedAboveBy_mono h.toAbove hupper⟩

theorem Bounds.bind {computation : OracleComp HashSpec α} {next : α → OracleComp HashSpec β}
    {lower upper nextLower nextUpper : Nat} (h : Bounds computation lower upper)
    (hnext : ∀ value, Bounds (next value) nextLower nextUpper) :
    Bounds (computation >>= next) (lower + nextLower) (upper + nextUpper) := by
  unfold Bounds at h hnext ⊢
  intro m _ _ _ _ impl
  rw [simulateQ_bind]
  exact ⟨queryBoundedBelowBy_bind' (h m impl).1 (fun value => (hnext value m impl).1),
    queryBoundedAboveBy_bind' (h m impl).2 (fun value => (hnext value m impl).2)⟩

theorem Bounds.map {computation : OracleComp HashSpec α} {lower upper : Nat}
    (h : Bounds computation lower upper) (f : α → β) :
    Bounds (f <$> computation) lower upper := by
  simpa [map_eq_bind_pure_comp] using
    h.bind (fun value => Bounds.of_exact (.pure (f value)) le_rfl le_rfl)

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
      (fors_exact signature.fors (MessageDigest.forsIndices digest) pk.seed (Scheme.forsAddress digest))
      le_rfl le_rfl
    refine hf.bind (fun forsKey => ?_)
    unfold Hypertree.verify
    simpa [map_eq_bind_pure_comp, layers] using
      (hypertree_root_bounds pk.seed layers signature.hypertree 0
        (MessageDigest.treeIndex digest).toNat (MessageDigest.leafIndex digest).toFin forsKey).map
        (fun root => root == pk.root)
  exact hh.bind htail

theorem verify_bounds (pk : PublicKey) (request : Message) (wire : Bytes)
    (message : Bytes) (signature : Signature)
    (hframe : request.frame = some message) (hparse : Signature.fromBytes? wire = some signature) :
    Bounds (Scheme.verify pk request wire) 569 3824 := by
  simpa only [Scheme.verify, hframe, hparse] using verifyInternal_bounds pk message signature

/-- Instrument the free computation before interpreting its hash calls. -/
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

end SlhDsaSecurity.VerificationQueries
