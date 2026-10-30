/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.VerifierNaturality
public import HashSig.SLHDSA.SHAKE128s.Proof.XmssAuthentication

/-!
# Naturality of key generation and signing

Key generation and signing preserve their ordered queries under oracle simulation: for a
`QueryImpl` that answers every hash query by the ambient `query`, simulating each signing
component (WOTS, XMSS, FORS, the hypertree, `Scheme.keygenInternal`, `Scheme.signInternal` and
`Scheme.sign`) gives the same computation run directly in the target monad.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.Correctness.Naturality

open VerifierNaturality

variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable (impl : QueryImpl HashSpec m) [HasQuery HashSpec m]
variable (himpl : ∀ input, impl input = (query (spec := HashSpec) input : m HashOutput))
include himpl

/-- Simulating secret derivation is derivation in the target monad. -/
theorem derive_simulate (publicSeed secretSeed : Digest) (address : Address) :
    simulateQ impl (Hashing.derive publicSeed secretSeed address) =
      (Hashing.derive publicSeed secretSeed address : m Digest) := by
  exact tweakable_simulate impl himpl _ _ _

/-- Simulating the randomizer computation is the randomizer in the target monad. -/
theorem randomizer_simulate (prf seed : Digest) (message : Bytes) :
    simulateQ impl (Hashing.randomizer prf seed message) =
      (Hashing.randomizer prf seed message : m Digest) := by
  simp only [Hashing.randomizer, Hashing.shortHash, simulateQ_bind, simulateQ_pure,
    hash_simulate impl himpl]

/-- Simulating WOTS public-key generation is that generation in the target monad. -/
theorem wots_publicKey_simulate (secretSeed publicSeed : Digest) (address : Address) :
    simulateQ impl (Wots.publicKey secretSeed publicSeed address) =
      (Wots.publicKey secretSeed publicSeed address : m Digest) := by
  simp only [Wots.publicKey_eq, simulateQ_bind, sequenceFin_simulate,
    derive_simulate impl himpl, chain_simulate impl himpl, tweakable_simulate impl himpl]

/-- Simulating WOTS signing is WOTS signing in the target monad. -/
theorem wots_sign_simulate (message secretSeed publicSeed : Digest) (address : Address) :
    simulateQ impl (Wots.sign message secretSeed publicSeed address) =
      (Wots.sign message secretSeed publicSeed address : m WotsSignature) := by
  simp only [Wots.sign_eq, sequenceFin_simulate, simulateQ_bind,
    derive_simulate impl himpl, chain_simulate impl himpl]

/-- Simulating an XMSS node computation is that computation in the target monad. -/
theorem merkle_node_simulate (secretSeed publicSeed : Digest) (address : Address)
    (height index : Nat) :
    simulateQ impl (Merkle.node secretSeed publicSeed address height index) =
      (Merkle.node secretSeed publicSeed address height index : m Digest) := by
  unfold Merkle.node
  apply PerfectMerkleTree.merkleRootM_natural (simulateQ' impl)
  · intro t
    exact wots_publicKey_simulate impl himpl _ _ _
  · intro z t left right
    exact tweakable_simulate impl himpl _ _ _

/-- Simulating an XMSS path maps its effectful WOTS+ leaves and parent hashes. -/
theorem merkle_authenticationPath_simulate (secretSeed publicSeed : Digest) (address : Address)
    (height index : Nat) :
    simulateQ impl (Merkle.authenticationPath secretSeed publicSeed address height index) =
      (Merkle.authenticationPath secretSeed publicSeed address height index :
        m (Vector Digest height)) := by
  unfold Merkle.authenticationPath
  apply PerfectMerkleTree.intrinsicAuthPathM_natural (simulateQ' impl)
  · intro t
    exact wots_publicKey_simulate impl himpl _ _ _
  · intro z t left right
    exact tweakable_simulate impl himpl _ _ _

/-- Simulating XMSS signing is XMSS signing in the target monad. -/
theorem merkle_sign_simulate (message secretSeed publicSeed : Digest) (address : Address)
    (index : Fin (2 ^ subtreeHeight)) :
    simulateQ impl (Merkle.sign message secretSeed publicSeed address index) =
      (Merkle.sign message secretSeed publicSeed address index : m XmssSignature) := by
  simp only [Merkle.sign, simulateQ_bind, simulateQ_pure,
    merkle_authenticationPath_simulate impl himpl, wots_sign_simulate impl himpl]

/-- Simulating FORS secret derivation is that derivation in the target monad. -/
theorem fors_secret_simulate (secretSeed publicSeed : Digest) (address : Address)
    (index : Nat) :
    simulateQ impl (Fors.secret secretSeed publicSeed address index) =
      (Fors.secret secretSeed publicSeed address index : m Digest) := by
  exact derive_simulate impl himpl _ _ _

/-- Simulating a FORS node computation is that computation in the target monad. -/
theorem fors_node_simulate (secretSeed publicSeed : Digest) (address : Address)
    (height index : Nat) :
    simulateQ impl (Fors.node secretSeed publicSeed address height index) =
      (Fors.node secretSeed publicSeed address height index : m Digest) := by
  unfold Fors.node
  apply PerfectMerkleTree.merkleRootM_natural (simulateQ' impl)
  · intro leafIndex
    simp only [simulateQ_bind, fors_secret_simulate impl himpl,
      tweakable_simulate impl himpl]
  · intro z t left right
    exact tweakable_simulate impl himpl _ _ _

/-- Simulating a FORS authentication path maps its primitive leaf and node hashes. -/
theorem fors_authenticationPath_simulate (secretSeed publicSeed : Digest) (address : Address)
    (height index : Nat) :
    simulateQ impl (Fors.authenticationPath secretSeed publicSeed address height index) =
      (Fors.authenticationPath secretSeed publicSeed address height index :
        m (Vector Digest height)) := by
  unfold Fors.authenticationPath
  apply PerfectMerkleTree.intrinsicAuthPathM_natural (simulateQ' impl)
  · intro leafIndex
    exact fors_node_simulate impl himpl _ _ _ 0 leafIndex
  · intro z t left right
    exact tweakable_simulate impl himpl _ _ _

/-- Simulating FORS signing is FORS signing in the target monad. -/
theorem fors_sign_simulate (indices : Fors.Indices) (secretSeed publicSeed : Digest)
    (address : Address) :
    simulateQ impl (Fors.sign indices secretSeed publicSeed address) =
      (Fors.sign indices secretSeed publicSeed address : m ForsSignature) := by
  simp only [Fors.sign, sequenceFin_simulate, simulateQ_bind, simulateQ_pure,
    fors_secret_simulate impl himpl, fors_authenticationPath_simulate impl himpl]

/-- Simulating hypertree signing over `remaining` layers is that signing in the target monad. -/
theorem hypertree_signLayers_simulate (secretSeed publicSeed : Digest)
    (remaining layer tree : Nat) (leaf : Hypertree.LeafIndex) (message : Digest) :
    simulateQ impl (Hypertree.signLayers secretSeed publicSeed remaining layer tree leaf message) =
      (Hypertree.signLayers secretSeed publicSeed remaining layer tree leaf message :
        m (Fin remaining → XmssSignature)) := by
  induction remaining generalizing layer tree leaf message with
  | zero => rfl
  | succ remaining ih =>
      cases remaining with
      | zero =>
          simp only [Hypertree.signLayers, simulateQ_bind, simulateQ_pure,
            merkle_sign_simulate impl himpl]
      | succ remaining =>
          conv_lhs => rw [Hypertree.signLayers]
          conv_rhs => rw [Hypertree.signLayers]
          simp only [simulateQ_bind, simulateQ_pure,
            merkle_sign_simulate impl himpl, merkle_simulate impl himpl, ih]

/-- Simulating hypertree signing is hypertree signing in the target monad. -/
theorem hypertree_sign_simulate (message secretSeed publicSeed : Digest)
    (tree : Hypertree.TreeIndex) (leaf : Hypertree.LeafIndex) :
    simulateQ impl (Hypertree.sign message secretSeed publicSeed tree leaf) =
      (Hypertree.sign message secretSeed publicSeed tree leaf : m HypertreeSignature) := by
  exact hypertree_signLayers_simulate impl himpl _ _ _ _ _ _ _

/-- Simulating internal key generation is key generation in the target monad. -/
theorem keygenInternal_simulate (secretSeed prfSeed publicSeed : Digest) :
    simulateQ impl (Scheme.keygenInternal secretSeed prfSeed publicSeed) =
      (Scheme.keygenInternal secretSeed prfSeed publicSeed : m (SecretKey × PublicKey)) := by
  simp only [Scheme.keygenInternal, simulateQ_bind, simulateQ_pure,
    merkle_node_simulate impl himpl]

/-- Simulating internal signing is internal signing in the target monad. -/
theorem signInternal_simulate (sk : SecretKey) (message : Bytes) :
    simulateQ impl (Scheme.signInternal sk message) =
      (Scheme.signInternal sk message : m Signature) := by
  simp only [Scheme.signInternal, Hashing.messageDigest, simulateQ_bind, simulateQ_pure,
    randomizer_simulate impl himpl, hash_simulate impl himpl, fors_sign_simulate impl himpl,
    fors_simulate impl himpl, hypertree_sign_simulate impl himpl]

/-- Simulating the signing oracle's computation is signing in the target monad. -/
theorem sign_simulate (sk : SecretKey) (request : Message) :
    simulateQ impl (Scheme.sign sk request) = (Scheme.sign sk request : m (Option Bytes)) := by
  unfold Scheme.sign
  cases request.frame with
  | none => simp only [simulateQ_pure]
  | some message => simp only [simulateQ_bind, simulateQ_pure, signInternal_simulate impl himpl]

end SLHDSA.SHAKE128s.Correctness.Naturality
