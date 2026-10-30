/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.Extraction.Hypertree
public import HashSig.SLHDSA.SHAKE128s.Proof.Extraction.WotsPreimage
public import HashSig.SLHDSA.SHAKE128s.Proof.Correctness.Merkle

/-!
# Chaining the structural extraction across all hypertree layers

A forged hypertree signature recovering the honest top root either contains a concrete
structural fault at some layer — a layer collision, or a WOTS signature on a message
differing from the honest input at that layer (which yields a chain preimage witness) — or the
bottom layer's incoming message equals the honest input threaded through every layer
(`rootFromSignature_fault_or_signed`). Threaded to the full hypertree, the fault-free branch
forces the recovered FORS public key to equal the honest one, and the whole signature to be the
one the honest signer writes (`verify_fault_or_fors_signed`), handing the FORS coverage argument
its input. No collision or one-wayness is assumed; every fault is a concrete witness whose ROM
probability is charged elsewhere in the proof.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.Extraction.HypertreeChain

variable [HasQuery HashSpec Id]

/-- The honest root of the subtree at `(layer, tree)` under the genuine seeds. -/
@[expose] def honestNode (secretSeed publicSeed : Digest) (layer tree : Nat) : Digest :=
  SLHDSA.SHAKE128s.Merkle.node (m := Id) secretSeed publicSeed
    (SLHDSA.SHAKE128s.Hypertree.address layer tree) subtreeHeight 0

/-- The honest top root reached by folding the given segment upward. The recovered root of
each honest layer is independent of its incoming message, so the fold ignores its input
past the bottom layer. -/
@[expose] def honestFold (secretSeed publicSeed : Digest) :
    (remaining layer tree : Nat) → Digest → Digest
  | 0, _, _, input => input
  | remaining + 1, layer, tree, _ =>
    honestFold secretSeed publicSeed remaining (layer + 1) (tree / 2 ^ subtreeHeight)
      (honestNode secretSeed publicSeed layer tree)

/-- A concrete structural fault somewhere in the segment: either a layer collision, or a
layer whose WOTS signature is the honest signature of a message differing from the honest
input threaded into that layer. The second case is a WOTS one-wayness witness. -/
@[expose] def HypertreeFault (secretSeed publicSeed : Digest) :
    (remaining : Nat) → (Fin remaining → XmssSignature) → (layer tree : Nat) →
      SLHDSA.SHAKE128s.Hypertree.LeafIndex → (message expectedInput : Digest) → Prop
  | 0, _, _, _, _, _, _ => False
  | remaining + 1, signatures, layer, tree, leaf, message, expectedInput =>
    Extraction.Hypertree.LayerCollision secretSeed publicSeed message layer tree leaf
        (signatures 0) ∨
    ((signatures 0).wots = SLHDSA.SHAKE128s.Wots.sign (m := Id) message secretSeed publicSeed
        (Extraction.Hypertree.wotsAddress layer tree leaf) ∧ message ≠ expectedInput) ∨
    HypertreeFault secretSeed publicSeed remaining (fun i => signatures i.succ) (layer + 1)
      (tree / 2 ^ subtreeHeight) (SLHDSA.SHAKE128s.Hypertree.nextLeaf tree)
      (SLHDSA.SHAKE128s.Merkle.publicKeyFromSignature (m := Id) leaf (signatures 0) message
        publicSeed (SLHDSA.SHAKE128s.Hypertree.address layer tree))
      (honestNode secretSeed publicSeed layer tree)

/-! ## The layers the honest signer writes

The fault-free branch of the chain below establishes more than an equation about the bottom
message: at each layer it has the forged signature's WOTS part equal to the honest signature of
that layer's message *and* its authentication path equal to the honest siblings. Together those
are the layer signature `Merkle.sign` produces, so the whole segment is the array
`Hypertree.signLayers` writes. Keeping that rather than projecting it away is what identifies a
forgery whose layers are all canonical with the signature the signer issued. -/

/-- One layer peeled off the honest signer's loop, uniformly in how many are left. -/
theorem signLayers_succ (secretSeed publicSeed : Digest) (remaining layer tree : Nat)
    (leaf : SLHDSA.SHAKE128s.Hypertree.LeafIndex) (message : Digest) :
    SLHDSA.SHAKE128s.Hypertree.signLayers (m := Id) secretSeed publicSeed (remaining + 1) layer
        tree leaf message =
      Fin.cases (SLHDSA.SHAKE128s.Merkle.sign (m := Id) message secretSeed publicSeed
          (SLHDSA.SHAKE128s.Hypertree.address layer tree) leaf)
        (SLHDSA.SHAKE128s.Hypertree.signLayers (m := Id) secretSeed publicSeed remaining (layer + 1)
          (tree / 2 ^ subtreeHeight) (SLHDSA.SHAKE128s.Hypertree.nextLeaf tree)
          (SLHDSA.SHAKE128s.Merkle.publicKeyFromSignature (m := Id) leaf
            (SLHDSA.SHAKE128s.Merkle.sign (m := Id) message secretSeed publicSeed
              (SLHDSA.SHAKE128s.Hypertree.address layer tree) leaf)
            message publicSeed (SLHDSA.SHAKE128s.Hypertree.address layer tree))) := by
  cases remaining <;> rfl

/-- **A canonical WOTS part and canonical siblings are the honest layer signature.** -/
theorem xmss_eq_sign (secretSeed publicSeed message : Digest) (layer tree : Nat)
    (leaf : SLHDSA.SHAKE128s.Hypertree.LeafIndex) (xsig : XmssSignature)
    (hwots : xsig.wots = SLHDSA.SHAKE128s.Wots.sign (m := Id) message secretSeed publicSeed
      (Extraction.Hypertree.wotsAddress layer tree leaf))
    (hauth : ∀ j, xsig.authentication j = SLHDSA.SHAKE128s.Merkle.node (m := Id) secretSeed
      publicSeed (SLHDSA.SHAKE128s.Hypertree.address layer tree) j.val
        (Nat.xor (leaf.val / 2 ^ j.val) 1)) :
    xsig = SLHDSA.SHAKE128s.Merkle.sign (m := Id) message secretSeed publicSeed
      (SLHDSA.SHAKE128s.Hypertree.address layer tree) leaf := by
  have hsign : SLHDSA.SHAKE128s.Merkle.sign (m := Id) message secretSeed publicSeed
      (SLHDSA.SHAKE128s.Hypertree.address layer tree) leaf =
      { wots := SLHDSA.SHAKE128s.Wots.sign (m := Id) message secretSeed publicSeed
          (Extraction.Hypertree.wotsAddress layer tree leaf),
        authentication := fun j => SLHDSA.SHAKE128s.Merkle.node (m := Id) secretSeed publicSeed
          (SLHDSA.SHAKE128s.Hypertree.address layer tree) j.val
            (Nat.xor (leaf.val / 2 ^ j.val) 1) } := by
    simp only [SLHDSA.SHAKE128s.Merkle.sign_eq_sequenceFin,
      SLHDSA.SHAKE128s.Correctness.sequenceFin_id, bind,
      pure]
    rfl
  rw [hsign]
  cases xsig
  simp only [XmssSignature.mk.injEq]
  exact ⟨hwots, funext hauth⟩

/-- **The seven-layer structural soundness chain.** Either a concrete fault occurs at some
layer, or the segment's incoming message equals the honest input threaded through it *and* every
layer carries the signature the honest signer writes there. The second conjunct is what the
induction proves at each layer anyway: a layer with no fault has the honest WOTS signature and
the honest siblings, which is the honest layer signature. -/
theorem rootFromSignature_fault_or_signed (secretSeed publicSeed rootTarget : Digest)
    (remaining layer tree : Nat) (leaf : SLHDSA.SHAKE128s.Hypertree.LeafIndex)
    (message expectedInput : Digest) (signatures : Fin remaining → XmssSignature)
    (htop : SLHDSA.SHAKE128s.Hypertree.rootFromSignature (m := Id) publicSeed remaining
        signatures layer tree leaf message = rootTarget)
    (hexp : honestFold secretSeed publicSeed remaining layer tree expectedInput = rootTarget) :
    (message = expectedInput ∧
        signatures = SLHDSA.SHAKE128s.Hypertree.signLayers (m := Id) secretSeed publicSeed
          remaining layer tree leaf expectedInput) ∨
      HypertreeFault secretSeed publicSeed remaining signatures layer tree leaf message
        expectedInput := by
  induction remaining generalizing layer tree leaf message expectedInput with
  | zero =>
    -- No layers: the fold and the recovery both return their input, and there is nothing to pin.
    refine Or.inl ⟨?_, ?_⟩
    · simp only [SLHDSA.SHAKE128s.Hypertree.rootFromSignature] at htop
      simp only [honestFold] at hexp
      exact htop.trans hexp.symm
    · funext i
      exact i.elim0
  | succ remaining ih =>
    -- Peel the bottom layer and apply the induction to the upper segment.
    rw [SLHDSA.SHAKE128s.Hypertree.rootFromSignature] at htop
    simp only [bind] at htop
    set root₀ := SLHDSA.SHAKE128s.Merkle.publicKeyFromSignature (m := Id) leaf (signatures 0)
      message publicSeed (SLHDSA.SHAKE128s.Hypertree.address layer tree) with hroot₀
    have hexp' : honestFold secretSeed publicSeed remaining (layer + 1)
        (tree / 2 ^ subtreeHeight) (honestNode secretSeed publicSeed layer tree) = rootTarget := by
      rw [honestFold] at hexp; exact hexp
    rcases ih (layer + 1) (tree / 2 ^ subtreeHeight) (SLHDSA.SHAKE128s.Hypertree.nextLeaf tree)
        root₀ (honestNode secretSeed publicSeed layer tree) (fun i => signatures i.succ)
        htop hexp' with ⟨hcanon, hrest⟩ | hfault
    · -- The upper segment recovered the honest node, pinning this layer's output.
      have hbottom : SLHDSA.SHAKE128s.Merkle.publicKeyFromSignature (m := Id) leaf (signatures 0)
          message publicSeed (SLHDSA.SHAKE128s.Hypertree.address layer tree) =
          SLHDSA.SHAKE128s.Merkle.node (m := Id) secretSeed publicSeed
            (SLHDSA.SHAKE128s.Hypertree.address layer tree) subtreeHeight 0 := hcanon
      rcases Extraction.Hypertree.layer_canonical_or_collision secretSeed publicSeed message
          layer tree leaf (signatures 0) hbottom with ⟨hwots, hauth⟩ | hcollision
      · by_cases hmessage : message = expectedInput
        · refine Or.inl ⟨hmessage, ?_⟩
          subst hmessage
          have hzero := xmss_eq_sign secretSeed publicSeed message layer tree leaf (signatures 0)
            hwots hauth
          rw [signLayers_succ, SLHDSA.SHAKE128s.Correctness.Merkle.publicKeyFromSignature_sign,
            show SLHDSA.SHAKE128s.Merkle.node (m := Id) secretSeed publicSeed
                (SLHDSA.SHAKE128s.Hypertree.address layer tree) subtreeHeight 0 =
              honestNode secretSeed publicSeed layer tree from rfl, ← hrest]
          funext i
          induction i using Fin.cases with
          | zero => exact hzero
          | succ j => rfl
        · exact Or.inr (Or.inr (Or.inl ⟨hwots, hmessage⟩))
      · exact Or.inr (Or.inl hcollision)
    · exact Or.inr (Or.inr (Or.inr hfault))

/-- The honest fold over `remaining + 1` layers reaches the top subtree root, independent
of its incoming message. -/
theorem honestFold_eq (secretSeed publicSeed : Digest) (remaining layer tree : Nat)
    (input : Digest) :
    honestFold secretSeed publicSeed (remaining + 1) layer tree input =
      honestNode secretSeed publicSeed (layer + remaining)
        (tree / 2 ^ (subtreeHeight * remaining)) := by
  induction remaining generalizing layer tree input with
  | zero => simp only [honestFold, Nat.add_zero, Nat.mul_zero, pow_zero, Nat.div_one]
  | succ remaining ih =>
    rw [honestFold, ih (layer + 1) (tree / 2 ^ subtreeHeight)
      (honestNode secretSeed publicSeed layer tree)]
    have hlayer : layer + 1 + remaining = layer + (remaining + 1) := by omega
    have hexponent : subtreeHeight + subtreeHeight * remaining =
        subtreeHeight * (remaining + 1) := by ring
    rw [hlayer, Nat.div_div_eq_div_mul, ← pow_add, hexponent]

/-- **A forged hypertree signature accepted against an honestly generated key either contains a
concrete structural fault at some layer, or it is the signature the honest signer writes** — in
particular its recovered FORS public key, the bottom message, is the honest one. -/
theorem verify_fault_or_fors_signed (secretSeed publicSeed : Digest) (pk : PublicKey)
    (tree : SLHDSA.SHAKE128s.Hypertree.TreeIndex) (leaf : SLHDSA.SHAKE128s.Hypertree.LeafIndex)
    (forsKey honestForsKey : Digest) (signature : HypertreeSignature)
    (hseed : pk.seed = publicSeed)
    (hroot : pk.root = honestNode secretSeed publicSeed (layers - 1) 0)
    (haccept : SLHDSA.SHAKE128s.Hypertree.verify (m := Id) forsKey signature pk tree leaf = true) :
    (forsKey = honestForsKey ∧
        signature = SLHDSA.SHAKE128s.Hypertree.signLayers (m := Id) secretSeed publicSeed layers 0
          tree.toNat leaf honestForsKey) ∨
      HypertreeFault secretSeed publicSeed layers signature 0 tree.toNat leaf forsKey
        honestForsKey := by
  have htop : SLHDSA.SHAKE128s.Hypertree.rootFromSignature (m := Id) publicSeed layers
      signature 0 tree.toNat leaf forsKey = pk.root := by
    rw [← hseed]
    simp only [SLHDSA.SHAKE128s.Hypertree.verify, bind, pure] at haccept
    exact (beq_iff_eq (α := Digest)).mp haccept
  have hexp : honestFold secretSeed publicSeed layers 0 tree.toNat honestForsKey = pk.root := by
    have hfold : honestFold secretSeed publicSeed layers 0 tree.toNat honestForsKey =
        honestNode secretSeed publicSeed (layers - 1) 0 := by
      have h := honestFold_eq secretSeed publicSeed (layers - 1) 0 tree.toNat honestForsKey
      have htree : tree.toNat / 2 ^ (subtreeHeight * (layers - 1)) = 0 := by
        apply Nat.div_eq_of_lt
        have := tree.isLt
        simpa only [show totalHeight - subtreeHeight = subtreeHeight * (layers - 1) from rfl]
          using this
      rw [Nat.zero_add, htree] at h
      exact h
    rw [hfold, hroot]
  exact rootFromSignature_fault_or_signed secretSeed publicSeed pk.root layers 0 tree.toNat
    leaf forsKey honestForsKey signature htop hexp

/-- The same, read only for the recovered FORS public key. -/
theorem verify_fault_or_fors_canonical (secretSeed publicSeed : Digest) (pk : PublicKey)
    (tree : SLHDSA.SHAKE128s.Hypertree.TreeIndex) (leaf : SLHDSA.SHAKE128s.Hypertree.LeafIndex)
    (forsKey honestForsKey : Digest) (signature : HypertreeSignature)
    (hseed : pk.seed = publicSeed)
    (hroot : pk.root = honestNode secretSeed publicSeed (layers - 1) 0)
    (haccept : SLHDSA.SHAKE128s.Hypertree.verify (m := Id) forsKey signature pk tree leaf = true) :
    forsKey = honestForsKey ∨
      HypertreeFault secretSeed publicSeed layers signature 0 tree.toNat leaf forsKey
        honestForsKey :=
  (verify_fault_or_fors_signed secretSeed publicSeed pk tree leaf forsKey honestForsKey signature
    hseed hroot haccept).imp And.left id

end SLHDSA.SHAKE128s.Extraction.HypertreeChain
