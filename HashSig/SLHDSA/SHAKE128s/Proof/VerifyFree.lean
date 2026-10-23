/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.GraphStakes
public import HashSig.SLHDSA.SHAKE128s.Proof.Target127
public import HashSig.SLHDSA.SHAKE128s.Proof.VerificationBudget

/-!
# The verifier's free queries

A hash input is *free* at a public seed when no sensitive node of the canonical graph is located
at it and it is prefixed by that seed. Every compression the verifier performs whose payload is
not a single 16-byte cell is free at `pk.seed`: `GraphStakes.locate` reads only single-cell
payloads back, and every tweakable input begins with the seed. Along every path, the verifier of a
parsed signature makes at least

* `168` FORS authentication-path compressions (`14` trees, `12` levels, payload `32` bytes),
* `1` FORS root compression (payload `14 · 16` bytes),
* `7` WOTS public-key compressions (payload `35 · 16` bytes),
* `63` Merkle node compressions (`7` layers, `9` levels, payload `32` bytes),

so at least `239` free queries. The bound is handler independent (`FreeBounds`), and survives any
stateful implementation (`FreeBounds.simulated`), in particular the game's random oracle in the
`OracleWorld` (`verify_free_rom`).
-/

@[expose] public section

open OracleComp OracleSpec
open scoped BigOperators

set_option maxRecDepth 2000

namespace SlhDsaSecurity.VerifyFree

variable {α β : Type}

open VerificationQueries

/-- An input is **free** at a public seed: it locates no sensitive node, and it is prefixed by
the seed. -/
def Free (publicSeed : Digest) (input : Bytes) : Prop :=
  (GraphStakes.stakes publicSeed).locate input = none ∧ Target127.SeedPrefixed publicSeed input

open scoped Classical in
/-- One unit for each free query. -/
noncomputable def freeCost (publicSeed : Digest) (input : Bytes) : Nat :=
  if Free publicSeed input then 1 else 0

theorem freeCost_of_free {publicSeed : Digest} {input : Bytes} (h : Free publicSeed input) :
    freeCost publicSeed input = 1 := by
  classical
  unfold freeCost
  exact ite_eq_left h

/-- **A tweakable input whose payload is not one cell is free.** -/
theorem free_tweakableInput (publicSeed : Digest) (address : Address) (payload : Bytes)
    (hlength : payload.length ≠ n) :
    Free publicSeed (Hashing.tweakableInput publicSeed address payload) := by
  classical
  refine ⟨?_, ⟨address.toBytes ++ payload, by simp [Hashing.tweakableInput, List.append_assoc]⟩⟩
  change GraphStakes.locate publicSeed _ = none
  unfold GraphStakes.locate
  rw [dite_eq_right]
  rintro ⟨node, cell, hinput⟩
  have hpayload := (Hashing.tweakableInput_injective hinput).2.2
  apply hlength
  rw [← hpayload, length_bytesBE]

/-- A two-cell payload, in either order. -/
theorem length_pair (first second : Digest) : (bytesBE n first ++ bytesBE n second).length ≠ n := by
  rw [List.length_append, length_bytesBE, length_bytesBE]
  simp [n]

/-! ## Handler-independent lower bounds on free queries -/

/-- Lower bounds compose along `bind` using only the elimination rules of a lawful attachment. -/
private theorem queryBoundedBelowBy_bind_of_lawful {m : Type → Type} [Monad m] [LawfulMonad m]
    [MonadAttach m] [LawfulMonadAttach m] {oa : AddWriterT ℕ m α} {f : α → AddWriterT ℕ m β}
    {n₁ n₂ : ℕ} (h₁ : AddWriterT.QueryBoundedBelowBy oa n₁)
    (h₂ : ∀ a, AddWriterT.QueryBoundedBelowBy (f a) n₂) :
    AddWriterT.QueryBoundedBelowBy (oa >>= f) (n₁ + n₂) := by
  intro z hz
  rw [WriterT.run_bind] at hz
  obtain ⟨⟨a, wa⟩, haw, hz⟩ := LawfulMonadAttach.canReturn_bind_imp' hz
  obtain ⟨⟨b, wb⟩, hbw, rfl⟩ := LawfulMonadAttach.canReturn_map_imp' hz
  simpa using add_le_add (h₁ (a, wa) haw) (h₂ a (b, wb) hbw)

/-- One instrumented query carries its own cost, using only a lawful attachment. -/
private theorem queryBoundedBelowBy_withAddCost_of_lawful {m : Type → Type} [Monad m]
    [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m] (impl : QueryImpl HashSpec m)
    (cost : Bytes → ℕ) (input : Bytes) :
    AddWriterT.QueryBoundedBelowBy (impl.withAddCost cost input) (cost input) := by
  intro z hz
  have hrun : (impl.withAddCost cost input).run =
      (fun a => (a, Multiplicative.ofAdd (cost input))) <$> impl input := by
    simp [QueryImpl.withAddCost_apply, AddWriterT.addTell, WriterT.run_bind]
  rw [hrun] at hz
  obtain ⟨a, -, rfl⟩ := LawfulMonadAttach.canReturn_map_imp' hz
  exact le_refl _

/-- Every reachable trace makes at least `lower` free queries, under every oracle implementation. -/
@[irreducible] def FreeBounds (publicSeed : Digest) (computation : OracleComp HashSpec α)
    (lower : Nat) : Prop :=
  ∀ (m : Type → Type) [Monad m] [LawfulMonad m]
    [MonadAttach m] [LawfulMonadAttach m] (impl : QueryImpl HashSpec m),
    AddWriterT.QueryBoundedBelowBy
      (simulateQ (impl.withAddCost (freeCost publicSeed)) computation) lower

variable {publicSeed : Digest}

theorem FreeBounds.zero (computation : OracleComp HashSpec α) :
    FreeBounds publicSeed computation 0 := by
  unfold FreeBounds
  intro m _ _ _ _ impl result _
  exact Nat.zero_le _

theorem FreeBounds.pure (value : α) :
    FreeBounds publicSeed (pure value : OracleComp HashSpec α) 0 :=
  FreeBounds.zero _

theorem FreeBounds.bind {computation : OracleComp HashSpec α} {next : α → OracleComp HashSpec β}
    {lower nextLower : Nat} (h : FreeBounds publicSeed computation lower)
    (hnext : ∀ value, FreeBounds publicSeed (next value) nextLower) :
    FreeBounds publicSeed (computation >>= next) (lower + nextLower) := by
  unfold FreeBounds at h hnext ⊢
  intro m _ _ _ _ impl
  rw [simulateQ_bind]
  exact queryBoundedBelowBy_bind_of_lawful (h m impl) (fun value => hnext value m impl)

theorem FreeBounds.map {computation : OracleComp HashSpec α} {lower : Nat}
    (h : FreeBounds publicSeed computation lower) (f : α → β) :
    FreeBounds publicSeed (f <$> computation) lower := by
  simpa [map_eq_bind_pure_comp] using
    h.bind (fun value => FreeBounds.pure (publicSeed := publicSeed) (f value))

theorem FreeBounds.query_bind (input : Bytes) {next : HashOutput → OracleComp HashSpec α}
    {lower : Nat} (hnext : ∀ output, FreeBounds publicSeed (next output) lower) :
    FreeBounds publicSeed (liftM (HashSpec.query input) >>= next)
      (freeCost publicSeed input + lower) := by
  unfold FreeBounds at hnext ⊢
  intro m _ _ _ _ impl
  rw [simulateQ_bind, simulateQ_spec_query]
  exact queryBoundedBelowBy_bind_of_lawful
    (queryBoundedBelowBy_withAddCost_of_lawful impl (freeCost publicSeed) input)
    (fun output => hnext output m impl)

theorem tweakable_free (address : Address) (payload : Bytes) (hlength : payload.length ≠ n) :
    FreeBounds publicSeed
      (Hashing.tweakable publicSeed address payload : OracleComp HashSpec Digest) 1 := by
  have h := FreeBounds.query_bind (publicSeed := publicSeed)
    (Hashing.tweakableInput publicSeed address payload)
    (next := fun output => (Pure.pure (Hashing.truncate output) : OracleComp HashSpec Digest))
    (fun output => FreeBounds.pure _)
  rw [freeCost_of_free (free_tweakableInput publicSeed address payload hlength)] at h
  exact h

theorem sequenceFin_free {size : Nat} (f : Fin size → OracleComp HashSpec α)
    (lower : Fin size → Nat) (hlower : ∀ i, FreeBounds publicSeed (f i) (lower i)) :
    FreeBounds publicSeed (sequenceFin size f) (∑ i, lower i) := by
  induction size with
  | zero => exact FreeBounds.pure Fin.elim0
  | succ size ih =>
    rw [sequenceFin, Fin.sum_univ_succ]
    exact (hlower 0).bind (fun first => by
      simpa only [map_eq_bind_pure_comp, Function.comp_def] using
        (ih (fun i => f i.succ) (fun i => lower i.succ) (fun i => hlower i.succ)).map
          (fun rest => (Fin.cases first rest : Fin (size + 1) → α)))

theorem foldlM_free (items : List α) (f : β → α → OracleComp HashSpec β)
    (lower : Nat) (hlower : ∀ value item, FreeBounds publicSeed (f value item) lower)
    (initial : β) :
    FreeBounds publicSeed (items.foldlM f initial) (items.length * lower) := by
  induction items generalizing initial with
  | nil => simpa using FreeBounds.pure (publicSeed := publicSeed) initial
  | cons item items ih =>
    simpa only [List.foldlM_cons, List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm] using
      (hlower initial item).bind (fun value => ih value)

/-! ## The verifier's components -/

/-- FORS: `14 · 12` authentication-path compressions and the root compression. -/
theorem fors_free (signature : ForsSignature) (indices : Fors.Indices) (address : Address) :
    FreeBounds publicSeed
      (Fors.publicKeyFromSignature signature indices publicSeed address :
        OracleComp HashSpec Digest) 169 := by
  unfold Fors.publicKeyFromSignature
  have hroots : ∀ i : Fin forsTrees, FreeBounds publicSeed
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
          OracleComp HashSpec Digest) (0 + forsHeight) := by
    intro i
    refine (FreeBounds.zero _).bind (fun leaf => ?_)
    simpa only [List.length_finRange, Nat.mul_one] using
      foldlM_free (List.finRange forsHeight) _ 1 (fun value j => tweakable_free _ _ (by
        split_ifs <;> exact length_pair _ _)) leaf
  have h : (∑ _ : Fin forsTrees, (0 + forsHeight)) + 1 = 169 := by
    norm_num [forsTrees, forsHeight]
  rw [← h]
  exact (sequenceFin_free _ (fun _ => 0 + forsHeight) hroots).bind (fun roots =>
    tweakable_free _ _ (by rw [digestArrayBytes_length]; norm_num [forsTrees, n]))

/-- WOTS: the public-key compression. -/
theorem wots_free (signature : WotsSignature) (message : Digest) (address : Address) :
    FreeBounds publicSeed
      (Wots.publicKeyFromSignature signature message publicSeed address :
        OracleComp HashSpec Digest) 1 := by
  unfold Wots.publicKeyFromSignature
  simpa only [Nat.zero_add] using (FreeBounds.zero _).bind (fun endpoints =>
    tweakable_free (publicSeed := publicSeed) _ (digestArrayBytes endpoints) (by
      rw [digestArrayBytes_length]
      norm_num [chains, messageDigits, checksumDigits, winternitzBits, n]))

/-- One XMSS layer: the WOTS compression and nine node compressions. -/
theorem merkle_free (index : Fin (2 ^ subtreeHeight)) (signature : XmssSignature)
    (message : Digest) (address : Address) :
    FreeBounds publicSeed
      (Merkle.publicKeyFromSignature index signature message publicSeed address :
        OracleComp HashSpec Digest) 10 := by
  unfold Merkle.publicKeyFromSignature
  change FreeBounds publicSeed _ (1 + subtreeHeight)
  exact (wots_free signature.wots message _).bind (fun leaf => by
    simpa only [List.length_finRange, Nat.mul_one] using
      foldlM_free (List.finRange subtreeHeight) _ 1 (fun value j => tweakable_free _ _ (by
        split_ifs <;> exact length_pair _ _)) leaf)

theorem hypertree_root_free (remaining : Nat)
    (signatures : Fin remaining → XmssSignature) (layer tree : Nat) (leaf : Hypertree.LeafIndex)
    (message : Digest) :
    FreeBounds publicSeed
      (Hypertree.rootFromSignature publicSeed remaining signatures layer tree leaf message :
        OracleComp HashSpec Digest) (remaining * 10) := by
  induction remaining generalizing layer tree leaf message with
  | zero => exact FreeBounds.pure message
  | succ remaining ih =>
    rw [Hypertree.rootFromSignature]
    simpa only [Nat.add_mul, Nat.one_mul, Nat.add_comm] using
      (merkle_free leaf (signatures 0) message (Hypertree.address layer tree)).bind
        (fun root => ih (fun i => signatures i.succ) (layer + 1)
          (tree / 2 ^ subtreeHeight) (Hypertree.nextLeaf tree) root)

theorem verifyInternal_free (pk : PublicKey) (message : Bytes) (signature : Signature) :
    FreeBounds pk.seed (Scheme.verifyInternal pk message signature : OracleComp HashSpec Bool)
      239 := by
  have htail (digest : HashOutput) : FreeBounds pk.seed
      (do
        let forsKey ← Fors.publicKeyFromSignature signature.fors (MessageDigest.forsIndices digest)
          pk.seed (Scheme.forsAddress digest)
        Hypertree.verify forsKey signature.hypertree pk
          (MessageDigest.treeIndex digest) (MessageDigest.leafIndex digest).toFin :
        OracleComp HashSpec Bool)
      (169 + 70) := by
    refine (fors_free signature.fors (MessageDigest.forsIndices digest)
      (Scheme.forsAddress digest)).bind (fun forsKey => ?_)
    unfold Hypertree.verify
    simpa [map_eq_bind_pure_comp, layers] using
      (hypertree_root_free (publicSeed := pk.seed) layers signature.hypertree 0
        (MessageDigest.treeIndex digest).toNat (MessageDigest.leafIndex digest).toFin forsKey).map
        (fun root => root == pk.root)
  unfold Scheme.verifyInternal
  simpa only [Nat.zero_add] using (FreeBounds.zero _).bind htail

/-- **Every path of the verifier on a parsed signature makes at least `239` free queries.** -/
theorem verify_free (pk : PublicKey) (request : Message) (wire : Bytes)
    (message : Bytes) (signature : Signature)
    (hframe : request.frame = some message) (hparse : Signature.fromBytes? wire = some signature) :
    FreeBounds pk.seed (Scheme.verify pk request wire : OracleComp HashSpec Bool) 239 := by
  simpa only [Scheme.verify, hframe, hparse] using verifyInternal_free pk message signature

/-! ## Transfer to stateful implementations -/

/-- Instrument the free computation with the free-query cost before interpreting it. -/
noncomputable def freeCounted (publicSeed : Digest) (computation : OracleComp HashSpec α) :
    OracleComp HashSpec (α × Multiplicative Nat) :=
  (simulateQ ((QueryImpl.ofLift HashSpec (OracleComp HashSpec)).withAddCost (freeCost publicSeed))
    computation).run

/-- Simulation through a stateful implementation can only shrink the support, using only the
elimination rules of a lawful attachment on the base monad. -/
private theorem mem_support_of_mem_support_simulateQ_run {ι : Type} {spec : OracleSpec ι}
    {m : Type → Type} [Monad m] [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m]
    {σ γ : Type} (impl : QueryImpl spec (StateT σ m)) (oa : OracleComp spec γ) (s : σ)
    {z : γ × σ} (hz : MonadAttach.CanReturn ((simulateQ impl oa).run s) z) :
    z.1 ∈ support oa := by
  induction oa using OracleComp.inductionOn generalizing s z with
  | pure y =>
    simp only [simulateQ_pure, StateT.run_pure] at hz
    have := LawfulMonadAttach.eq_of_canReturn_pure hz
    simp [← this]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at hz
    obtain ⟨⟨u, s'⟩, -, hrest⟩ := LawfulMonadAttach.canReturn_bind_imp' hz
    exact (mem_support_bind_iff _ _ _).2 ⟨u, mem_support_query t u, ih u s' hrest⟩

private theorem mem_support_of_mem_support_simulateQ_run' {ι : Type} {spec : OracleSpec ι}
    {m : Type → Type} [Monad m] [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m]
    {σ γ : Type} (impl : QueryImpl spec (StateT σ m)) (oa : OracleComp spec γ) (s : σ) {x : γ}
    (hx : x ∈ support ((simulateQ impl oa).run' s)) : x ∈ support oa := by
  rw [StateT.run'_eq] at hx
  obtain ⟨z, hz, rfl⟩ := LawfulMonadAttach.canReturn_map_imp' hx
  exact mem_support_of_mem_support_simulateQ_run impl oa s hz

/-- The bound survives any stateful implementation and any initial state, including a
random-oracle cache: instrumentation precedes the implementation. -/
theorem FreeBounds.simulated {m : Type → Type} [Monad m] [LawfulMonad m]
    [MonadAttach m] [LawfulMonadAttach m]
    {σ : Type} {computation : OracleComp HashSpec α} {lower : Nat}
    (h : FreeBounds publicSeed computation lower) (impl : QueryImpl HashSpec (StateT σ m))
    (initial : σ) (result : α × Multiplicative Nat)
    (hresult : result ∈ support ((simulateQ impl (freeCounted publicSeed computation)).run' initial)) :
    lower ≤ Multiplicative.toAdd result.2 := by
  have hfree := mem_support_of_mem_support_simulateQ_run' impl
    (freeCounted publicSeed computation) initial hresult
  unfold FreeBounds at h
  exact h (OracleComp HashSpec) (QueryImpl.ofLift HashSpec (OracleComp HashSpec)) result hfree

/-! ## The `OracleWorld` verifier under the game's random oracle -/

theorem freeCounted_pure (value : α) :
    freeCounted publicSeed (pure value : OracleComp HashSpec α) =
      pure (value, Multiplicative.ofAdd 0) := rfl

theorem freeCounted_query_bind (input : HashSpec.Domain)
    (next : HashSpec.Range input → OracleComp HashSpec α) :
    freeCounted publicSeed (liftM (HashSpec.query input) >>= next) = (do
      let output ← liftM (HashSpec.query input)
      let result ← freeCounted publicSeed (next output)
      return (result.1, Multiplicative.ofAdd
        (freeCost publicSeed input + Multiplicative.toAdd result.2))) := by
  simp [freeCounted, simulateQ_bind, QueryImpl.withAddCost, QueryImpl.withCost, WriterT.run_bind,
    bind_assoc, map_eq_bind_pure_comp]

end SlhDsaSecurity.VerifyFree
