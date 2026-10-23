/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.Experiment

/-! The hash-only verifier and its instantiations use the same ordered oracle calls. -/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.VerifierNaturality

variable {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type}
variable (impl : QueryImpl HashSpec m)

theorem sequenceFin_simulate {size : Nat} (f : Fin size → OracleComp HashSpec α) :
    simulateQ impl (sequenceFin size f) =
      sequenceFin size (fun i => simulateQ impl (f i)) := by
  induction size with
  | zero => rfl
  | succ size ih =>
    simp only [sequenceFin, simulateQ_bind, simulateQ_pure]
    congr 1
    funext first
    rw [ih]

theorem foldlM_simulate (items : List α) (f : β → α → OracleComp HashSpec β) (initial : β) :
    simulateQ impl (items.foldlM f initial) =
      items.foldlM (fun value item => simulateQ impl (f value item)) initial := by
  induction items generalizing initial with
  | nil => rfl
  | cons item items ih => simp only [List.foldlM_cons, simulateQ_bind, ih]

variable [HasQuery HashSpec m]
variable (himpl : ∀ input, impl input = (query (spec := HashSpec) input : m HashOutput))
include himpl

theorem hash_simulate (input : Bytes) :
    simulateQ impl (Hashing.hash input) = (Hashing.hash input : m HashOutput) := by
  change simulateQ impl (liftM (HashSpec.query input)) = query (spec := HashSpec) input
  rw [simulateQ_spec_query, himpl]

theorem tweakable_simulate (seed : Digest) (address : Address) (payload : Bytes) :
    simulateQ impl (Hashing.tweakable seed address payload) =
      (Hashing.tweakable seed address payload : m Digest) := by
  simp only [Hashing.tweakable, Hashing.shortHash, simulateQ_bind,
    hash_simulate impl himpl, simulateQ_pure]

theorem chain_simulate (seed : Digest) (address : Address) (start steps : Nat) (value : Digest) :
    simulateQ impl (Wots.chain seed address start steps value) =
      (Wots.chain seed address start steps value : m Digest) := by
  induction steps generalizing start value with
  | zero => rfl
  | succ steps ih =>
    simp only [Wots.chain, simulateQ_bind, tweakable_simulate impl himpl, ih]

theorem wots_simulate (signature : WotsSignature) (message publicSeed : Digest) (address : Address) :
    simulateQ impl (Wots.publicKeyFromSignature signature message publicSeed address) =
      (Wots.publicKeyFromSignature signature message publicSeed address : m Digest) := by
  simp only [Wots.publicKeyFromSignature, simulateQ_bind, sequenceFin_simulate,
    chain_simulate impl himpl, tweakable_simulate impl himpl]

theorem merkle_simulate (index : Fin (2 ^ subtreeHeight)) (signature : XmssSignature)
    (message publicSeed : Digest) (address : Address) :
    simulateQ impl (Merkle.publicKeyFromSignature index signature message publicSeed address) =
      (Merkle.publicKeyFromSignature index signature message publicSeed address : m Digest) := by
  simp only [Merkle.publicKeyFromSignature, simulateQ_bind, wots_simulate impl himpl,
    foldlM_simulate, tweakable_simulate impl himpl]

theorem fors_simulate (signature : ForsSignature) (indices : Fors.Indices)
    (publicSeed : Digest) (address : Address) :
    simulateQ impl (Fors.publicKeyFromSignature signature indices publicSeed address) =
      (Fors.publicKeyFromSignature signature indices publicSeed address : m Digest) := by
  simp only [Fors.publicKeyFromSignature, simulateQ_bind, sequenceFin_simulate,
    foldlM_simulate, tweakable_simulate impl himpl]

theorem hypertree_root_simulate (publicSeed : Digest) (remaining : Nat)
    (signatures : Fin remaining → XmssSignature) (layer tree : Nat) (leaf : Hypertree.LeafIndex)
    (message : Digest) :
    simulateQ impl
        (Hypertree.rootFromSignature publicSeed remaining signatures layer tree leaf message) =
      (Hypertree.rootFromSignature publicSeed remaining signatures layer tree leaf message : m Digest) := by
  induction remaining generalizing layer tree leaf message with
  | zero => rfl
  | succ remaining ih =>
    simp only [Hypertree.rootFromSignature, simulateQ_bind, merkle_simulate impl himpl, ih]

theorem hypertree_simulate (message : Digest) (signature : HypertreeSignature) (pk : PublicKey)
    (tree : Hypertree.TreeIndex) (leaf : Hypertree.LeafIndex) :
    simulateQ impl (Hypertree.verify message signature pk tree leaf) =
      (Hypertree.verify message signature pk tree leaf : m Bool) := by
  simp only [Hypertree.verify, simulateQ_bind, hypertree_root_simulate impl himpl, simulateQ_pure]

theorem verifyInternal_simulate (pk : PublicKey) (message : Bytes) (signature : Signature) :
    simulateQ impl (Scheme.verifyInternal pk message signature) =
      (Scheme.verifyInternal pk message signature : m Bool) := by
  simp only [Scheme.verifyInternal, Hashing.messageDigest, simulateQ_bind, hash_simulate impl himpl,
    fors_simulate impl himpl, hypertree_simulate impl himpl]

theorem verify_simulate (pk : PublicKey) (request : Message) (signature : Bytes) :
    simulateQ impl (Scheme.verify pk request signature) =
      (Scheme.verify pk request signature : m Bool) := by
  unfold Scheme.verify
  cases request.frame with
  | none => rfl
  | some message =>
    cases Signature.fromBytes? signature with
    | none => rfl
    | some parsed => exact verifyInternal_simulate impl himpl pk message parsed

end SlhDsaSecurity.VerifierNaturality
