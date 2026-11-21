/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.GrowthBudget

/-!
# A lower bound on the hash calls made by SHAKE-128s key generation

Every supported run of internal key generation makes at least 18,432 hash calls from any
initial random-oracle cache. Each of the 512 leaves of the top Merkle tree derives 35 WOTS+
secret values and compresses the endpoints. This gives a lower bound of 36 calls per leaf.

`count_keygen_ge` counts key generation's own calls. The security game's
`Game.adversaryWork` counts signing attempts, direct adversary hashes and final verification.
Key-generation hashes are excluded from that budget.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.HonestGrowth

open Security

/-- A single query is charged its own cost. -/
theorem count_query (queried : OracleWorld.Domain) (cache : QueryCache HashSpec)
    (result : (OracleWorld.Range queried × Nat) × QueryCache HashSpec)
    (hmem : result ∈ support ((simulateQ KeygenUniform.rom (countAllHashes
      (liftM (OracleWorld.query queried) :
        OracleComp OracleWorld (OracleWorld.Range queried)))).run cache)) :
    result.1.2 = hashCost queried := by
  rw [GrowthBudget.countAllHashes_query, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    mem_support_bind_iff] at hmem
  obtain ⟨step, -, hpure⟩ := hmem
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hpure
  rw [hpure]

/-- A tweakable call is charged one unit. -/
theorem one_le_count_tweakable (publicSeed : Digest) (address : Address) (payload : Bytes)
    (cache : QueryCache HashSpec) (result : (Digest × Nat) × QueryCache HashSpec)
    (hmem : result ∈ support ((simulateQ KeygenUniform.rom (countAllHashes
      (Hashing.tweakable (m := OracleComp OracleWorld) publicSeed address payload))).run cache)) :
    1 ≤ result.1.2 := by
  rw [show (Hashing.tweakable (m := OracleComp OracleWorld) publicSeed address payload) =
      Hashing.truncate <$> (Hashing.hash (m := OracleComp OracleWorld)
        (Hashing.tweakableInput publicSeed address payload)) from by
      simp [Hashing.tweakable, Hashing.shortHash, map_eq_bind_pure_comp],
    AdversaryQueries.countAllHashes_map, simulateQ_map, StateT.run_map, support_map] at hmem
  obtain ⟨inner, hinner, heq⟩ := hmem
  have hcount := count_query (Sum.inr (Hashing.tweakableInput publicSeed address payload)) cache
    inner hinner
  rw [show result.1.2 = inner.1.2 from by rw [← heq], hcount]
  exact Nat.le_refl 1

end SLHDSA.SHAKE128s.HonestGrowth

namespace SLHDSA.SHAKE128s.KeygenCost

variable {α : Type}

open Security

/-- **A `sequenceFin` whose every entry costs at least `k` costs at least `size · k`.** -/
theorem count_sequenceFin_ge {α : Type} (k : Nat) :
    ∀ (size : Nat) (f : Fin size → OracleComp OracleWorld α),
      (∀ i (cache : QueryCache HashSpec) (result : (α × Nat) × QueryCache HashSpec),
        result ∈ support ((simulateQ KeygenUniform.rom (countAllHashes (f i))).run cache) →
          k ≤ result.1.2) →
      ∀ (cache : QueryCache HashSpec) (result : ((Fin size → α) × Nat) × QueryCache HashSpec),
        result ∈ support ((simulateQ KeygenUniform.rom
          (countAllHashes (sequenceFin size f))).run cache) → size * k ≤ result.1.2 := by
  intro size
  induction size with
  | zero => intro _ _ _ _ _; simp
  | succ size ih =>
    intro f hf cache result hmem
    rw [sequenceFin] at hmem
    obtain ⟨first, middleCache, firstCount, restCount, hfirst, hrest, hsplit⟩ :=
      AdversaryQueries.mem_support_counted_bind_count _ _ cache result hmem
    obtain ⟨rest, lastCache, restCount', lastCount, hrest', hlast, hsplit'⟩ :=
      AdversaryQueries.mem_support_counted_bind_count _ _ middleCache _ hrest
    rw [GrowthBudget.countAllHashes_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hlast
    have hlastZero : lastCount = 0 := congrArg (fun z => z.1.2) hlast
    have h1 := hf 0 cache _ hfirst
    have h2 := ih (fun i => f i.succ) (fun i => hf i.succ) middleCache _ hrest'
    simp only at hsplit hsplit' h1 h2
    rw [Nat.succ_mul]
    omega

/-- **A WOTS public key costs at least thirty-six calls.** -/
theorem count_wotsPublicKey_ge (secretSeed publicSeed : Digest) (address : Address)
    (cache : QueryCache HashSpec) (result : (Digest × Nat) × QueryCache HashSpec)
    (hmem : result ∈ support ((simulateQ KeygenUniform.rom (countAllHashes
      (Wots.publicKey (m := OracleComp OracleWorld) secretSeed publicSeed address))).run
        cache)) :
    chains + 1 ≤ result.1.2 := by
  rw [Wots.publicKey_eq] at hmem
  obtain ⟨endpoints, middleCache, first, second, hfirst, hsecond, hsplit⟩ :=
    AdversaryQueries.mem_support_counted_bind_count _ _ cache result hmem
  have hone : (1 : Nat) ≤ second := HonestGrowth.one_le_count_tweakable publicSeed _ _
    middleCache ⟨⟨result.1.1, second⟩, result.2⟩ hsecond
  have hchains : chains * 1 ≤ first := by
    refine count_sequenceFin_ge 1 chains _ (fun i cache' result' hmem' => ?_) cache _ hfirst
    obtain ⟨secret, cache'', c1, c2, hderive, -, hsplit''⟩ :=
      AdversaryQueries.mem_support_counted_bind_count _ _ cache' result' hmem'
    have := HonestGrowth.one_le_count_tweakable publicSeed _ _ cache' ⟨⟨secret, c1⟩, cache''⟩
      hderive
    simp only at hsplit'' this
    omega
  omega

/-- **A Merkle subtree of height `h` costs at least `36 · 2 ^ h` calls.** -/
theorem count_merkleNode_ge (secretSeed publicSeed : Digest) (address : Address) :
    ∀ (height index : Nat) (cache : QueryCache HashSpec)
      (result : (Digest × Nat) × QueryCache HashSpec),
      result ∈ support ((simulateQ KeygenUniform.rom (countAllHashes
        (SLHDSA.SHAKE128s.Merkle.node (m := OracleComp OracleWorld) secretSeed publicSeed address
          height index))).run cache) →
        (chains + 1) * 2 ^ height ≤ result.1.2 := by
  intro height
  induction height with
  | zero =>
    intro index cache result hmem
    rw [SLHDSA.SHAKE128s.Merkle.node] at hmem
    simpa using count_wotsPublicKey_ge secretSeed publicSeed _ cache result hmem
  | succ height ih =>
    intro index cache result hmem
    rw [SLHDSA.SHAKE128s.Merkle.node] at hmem
    obtain ⟨left, leftCache, leftCount, restCount, hleft, hrest, hsplit⟩ :=
      AdversaryQueries.mem_support_counted_bind_count _ _ cache result hmem
    obtain ⟨right, rightCache, rightCount, lastCount, hright, hlast, hsplit'⟩ :=
      AdversaryQueries.mem_support_counted_bind_count _ _ leftCache _ hrest
    have hleftCount := ih (2 * index) cache ⟨⟨left, leftCount⟩, leftCache⟩ hleft
    have hrightCount := ih (2 * index + 1) leftCache ⟨⟨right, rightCount⟩, rightCache⟩ hright
    simp only at hsplit' hleftCount hrightCount
    rw [pow_succ, ← mul_assoc, mul_two]
    omega

attribute [local irreducible] SLHDSA.SHAKE128s.Merkle.node

/-- **Key generation costs at least `36 · 2 ^ subtreeHeight` calls.** -/
theorem count_keygen_ge (secretSeed prfSeed publicSeed : Digest)
    (cache : QueryCache HashSpec)
    (result : ((SecretKey × PublicKey) × Nat) × QueryCache HashSpec)
    (hmem : result ∈ support ((simulateQ KeygenUniform.rom (countAllHashes
      (Scheme.keygenInternal secretSeed prfSeed publicSeed))).run cache)) :
    (chains + 1) * 2 ^ subtreeHeight ≤ result.1.2 := by
  rw [Scheme.keygenInternal] at hmem
  obtain ⟨root, middleCache, first, second, hfirst, -, hsplit⟩ :=
    AdversaryQueries.mem_support_counted_bind_count _ _ cache result hmem
  have hnode := count_merkleNode_ge secretSeed publicSeed
    (SLHDSA.SHAKE128s.Hypertree.address (layers - 1) 0) subtreeHeight 0 cache
    ⟨⟨root, first⟩, middleCache⟩ hfirst
  simp only at hnode
  omega

end SLHDSA.SHAKE128s.KeygenCost
