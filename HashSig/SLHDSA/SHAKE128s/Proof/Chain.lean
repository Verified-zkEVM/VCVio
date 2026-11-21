/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.SLHDSA.SHAKE128s.Statement.Scheme
public import VCVio.Algorithms.IndexedChain.Witnesses

/-!
# SHAKE128s chain correspondence

The first-step recursive evaluator implements the shared indexed chain under a lawful monad.
Its FIPS hash address is the supplied zero-based position. This correspondence preserves the
existing evaluator, including its definition for callback monads without algebraic laws.
-/

public section

namespace SLHDSA.SHAKE128s.Wots

/-- The first-step evaluator and the shared final-step kernel execute the same callbacks. -/
theorem chain_eq_indexedChain {m : Type → Type} [Monad m] [LawfulMonad m]
    [HasQuery HashSpec m] (publicSeed : Digest) (address : Address)
    (start steps : Nat) (value : Digest) :
    chain (m := m) publicSeed address start steps value =
      VCVio.Algorithms.IndexedChain.chainM (m := m)
        (fun j x => Hashing.tweakable publicSeed
          { address with hashOrIndex := BitVec.ofNat 32 j } (bytesBE n x)) start steps value := by
  induction steps generalizing start value with
  | zero => rfl
  | succ steps ih =>
    rw [chain, VCVio.Algorithms.IndexedChain.chainM_succ_left]
    exact bind_congr fun x => ih (start + 1) x

end SLHDSA.SHAKE128s.Wots
