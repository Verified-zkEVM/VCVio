/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Auxiliary.Adversary
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCR
public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Monadic

/-!
# Honest hash target registration
-/

public section

namespace GXMSS.Reductions

open OracleComp OracleSpec TweakableHash

variable {PP T X H M R : Type} {h w v : ℕ}

/-- Standalone Merkle target-collision problem with the complete registration capacity. -/
@[expose] def merkleTCRProblem (hash : HashInstance PP T X H h w v) :=
  SM_DT_TCR_Problem.standalone hash.thf (2 * (2 ^ h) * v * (2 ^ w))

/-- Local registration state used while choosing honest SM-DT-TCR targets. -/
abbrev TCRSetupM (hash : HashInstance PP T X H h w v) (targets : ℕ) :=
  StateT (List (T × X)) (OracleComp (unifSpec + (SM_DT_TCR_challengeSpec T X H +
    collectionSpec (SM_DT_TCR_Problem.standalone hash.thf targets).thColl)))

/-- Key material obtained by registering every honest target before the public seed is revealed. -/
structure TCRKeyState (PP T X H : Type) (h v : ℕ) where
  /-- Sampled initial value for every epoch and chain. -/
  starts : Fin (2 ^ h) → Fin v → H
  /-- Endpoint array returned by the registered chain computations. -/
  endpoints : Fin (2 ^ h) → Fin v → H
  /-- Root digest of the registered honest Merkle tree. -/
  root : H
  /-- Accepted honest tweak/input pairs in registration order. -/
  targets : List (T × X)
  /-- Independently sampled fallback digest retained by the reduction. -/
  fallback : H

/-- Submit one target and append it locally exactly when the authoritative oracle accepts it. -/
def tcrEval (hash : HashInstance PP T X H h w v) (targets : ℕ)
    (tweak : T) (input : X) (fallback : H) : TCRSetupM hash targets H := do
  let answer ← liftM ((unifSpec + (SM_DT_TCR_challengeSpec T X H +
    collectionSpec (SM_DT_TCR_Problem.standalone hash.thf targets).thColl)).query
      (.inr (.inl (tweak, input))))
  match answer with
  | none => return fallback
  | some value =>
      let registered ← get
      set (registered ++ [(tweak, input)])
      return value

/-- Register one complete honest chain, in positive paper-step order. -/
def tcrFullChain (hash : HashInstance PP T X H h w v) (targets : ℕ)
    (ep : Epoch h) (i : Fin v) (start fallback : H) :
    (s : ℕ) → s ≤ 2 ^ w - 1 → TCRSetupM hash targets H
  | 0, _ => pure start
  | s + 1, hs => do
      let previous ← tcrFullChain hash targets ep i start fallback s (by omega)
      tcrEval hash targets (hash.chainTweak (ep, i, ⟨s, by omega⟩))
        (hash.digestInput previous) fallback

/-- Register every positive step of every honest chain, in epoch-major order. -/
def tcrEndpoints (hash : HashInstance PP T X H h w v) (targets : ℕ)
    (starts : Epoch h → Fin v → H) (fallback : H) :
    TCRSetupM hash targets (Epoch h → Fin v → H) :=
  Fin.mOfFn (2 ^ h) fun ep => Fin.mOfFn v fun i =>
    tcrFullChain hash targets ep i (starts ep i) fallback (2 ^ w - 1) (by omega)

/-- The first challenge-history index of a registered tweak/input target. -/
def registeredIndex [DecidableEq T] [DecidableEq X]
    (targets : List (T × X)) (tweak : T) (input : X) : ℕ :=
  targets.findIdx (fun target => target = (tweak, input))

/-- Membership makes the selected registered index strictly smaller than the history length. -/
theorem registeredIndex_lt_length_of_mem [DecidableEq T] [DecidableEq X]
    (targets : List (T × X)) (tweak : T) (input : X)
    (hmem : (tweak, input) ∈ targets) :
    registeredIndex targets tweak input < targets.length := by
  exact List.findIdx_lt_length_of_exists ⟨(tweak, input), hmem, by simp⟩

/-- Looking up a selected registered index returns that exact target. -/
theorem registeredIndex_lookup_of_mem [DecidableEq T] [DecidableEq X]
    (targets : List (T × X)) (tweak : T) (input : X)
    (hmem : (tweak, input) ∈ targets) :
    targets[registeredIndex targets tweak input]? = some (tweak, input) := by
  have hlt := registeredIndex_lt_length_of_mem targets tweak input hmem
  rw [List.getElem?_eq_getElem hlt]
  congr
  exact of_decide_eq_true (List.findIdx_getElem (w := hlt))

/-- A registered target is within every capacity that bounds the complete target history. -/
theorem registeredIndex_lt_capacity_of_mem [DecidableEq T] [DecidableEq X]
    (targets : List (T × X)) (tweak : T) (input : X) (capacity : ℕ)
    (hmem : (tweak, input) ∈ targets) (hlen : targets.length ≤ capacity) :
    registeredIndex targets tweak input < capacity :=
  (registeredIndex_lt_length_of_mem targets tweak input hmem).trans_le hlen

end GXMSS.Reductions
