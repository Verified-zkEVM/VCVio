/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CacheReplay

/-!
# A WOTS chain's queries are cached

The companion to `MerkleEntry` for the other fold shape. A WOTS chain is a direct recursion
rather than a `foldlM`, so the peeling lemmas for folds do not apply to it and it gets its own
induction — but the shape of the argument is the same: the step at offset `o` consults its
input at the chain's own partial value after `o` steps, computed under `CacheReplay.replay`.

That partial value is `Wots.chain` itself at `o` steps under `CacheReplay.replayQuery`, which
is exactly the value `Extraction.Wots.ChainCollision` is stated about, so
`WotsCharge.deviatingCollision_of_chainCollision` can take the entry directly.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.WotsEntry

open CacheReplay

/-- **Every step of a chain consults its input at the chain's own partial value.** -/
theorem queriesUnder_chain (cache : QueryCache HashSpec) (publicSeed : Digest)
    (address : Address) :
    ∀ (steps offset start : Nat) (value : Digest), offset < steps →
      QueriesUnder cache
        (SLHDSA.SHAKE128s.Wots.chain (m := OracleComp HashSpec) publicSeed address start steps
          value)
        (Hashing.tweakableInput publicSeed
          { address with hashOrIndex := BitVec.ofNat 32 (start + offset) }
          (bytesBE n (@SLHDSA.SHAKE128s.Wots.chain Id _ (replayQuery cache) publicSeed address
            start offset value))) := by
  intro steps
  induction steps with
  | zero => intro offset _ _ hoffset; exact absurd hoffset (by omega)
  | succ remaining ih =>
    intro offset start value hoffset
    cases offset with
    | zero =>
      simp only [Nat.add_zero, SLHDSA.SHAKE128s.Wots.chain_zero,
        SLHDSA.SHAKE128s.Wots.chain_succ, pure]
      exact queriesUnder_tweakable cache publicSeed
        { address with hashOrIndex := BitVec.ofNat 32 start } (bytesBE n value) _
    | succ offset =>
      have hrest : offset < remaining := by omega
      have hstep := ih offset (start + 1)
        (Hashing.truncate (replay cache (Hashing.tweakableInput publicSeed
          { address with hashOrIndex := BitVec.ofNat 32 start } (bytesBE n value)))) hrest
      rw [show start + 1 + offset = start + (offset + 1) from by omega] at hstep
      rw [show (SLHDSA.SHAKE128s.Wots.chain (m := OracleComp HashSpec) publicSeed address start
            (remaining + 1) value) =
          (Hashing.hash (m := OracleComp HashSpec) (Hashing.tweakableInput publicSeed
            { address with hashOrIndex := BitVec.ofNat 32 start } (bytesBE n value))) >>=
            (fun answer => SLHDSA.SHAKE128s.Wots.chain (m := OracleComp HashSpec) publicSeed
              address (start + 1) remaining (Hashing.truncate answer)) from by
        simp [SLHDSA.SHAKE128s.Wots.chain_succ, Hashing.tweakable, Hashing.shortHash]]
      refine QueriesUnder.tail _ _ _ ?_
      simp only [SLHDSA.SHAKE128s.Wots.chain_succ, replayFold_step_eq_tweakable] at hstep ⊢
      exact hstep

end SLHDSA.SHAKE128s.WotsEntry
