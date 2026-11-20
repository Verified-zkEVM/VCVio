/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Wots.Program
import all HashSig.SLHDSA.Wots.Program
public import VCVio.Algorithms.IndexedChain.Basic

/-! # Algebra of ordered callback chains -/

public section

namespace SLHDSA.Wots.Program

universe u v z

variable {Y : Type u} {m : Type u → Type v} [Monad m]

/-- An empty chain returns its initial value. -/
@[simp] theorem chain_zero (step : Nat → Y → m Y) (i : Nat) (x : Y) :
    chain step i 0 x = pure x := by simp only [chain]

/-- The first step precedes all remaining chain effects. -/
theorem chain_head (step : Nat → Y → m Y) (i s : Nat) (x : Y) :
    chain step i (s + 1) x = step i x >>= fun y => chain step (i + 1) s y := by
  simp only [chain]

/-- First-step evaluation agrees with the indexed chain in every lawful callback monad. -/
theorem chain_eq_indexedChain [LawfulMonad m] (step : Nat → Y → m Y) (start steps : Nat)
    (value : Y) : chain step start steps value =
      VCVio.Algorithms.IndexedChain.chainM step start steps value := by
  induction steps generalizing start value with
  | zero => rfl
  | succ steps ih =>
    rw [chain_head, VCVio.Algorithms.IndexedChain.chainM_succ_left]
    exact bind_congr fun value => ih (start + 1) value

/-- The last callback follows the shorter prefix in a lawful monad. -/
theorem chain_prefix [LawfulMonad m] (step : Nat → Y → m Y) (s i : Nat) (x : Y) :
    chain step i (s + 1) x = chain step i s x >>= fun y => step (i + s) y := by
  simp only [chain_eq_indexedChain, VCVio.Algorithms.IndexedChain.chainM_succ]

/-- Primitive pure/bind and step preservation transports an entire ordered chain. -/
theorem chain_natural {n : Type u → Type z} [Monad n]
    (F : m Y → n Y)
    (hpure : ∀ x, F (pure x) = pure x)
    (hbind : ∀ (p : m Y) (k : Y → m Y),
      F (p >>= k) = F p >>= fun y => F (k y))
    (stepm : Nat → Y → m Y) (stepn : Nat → Y → n Y)
    (hstep : ∀ i y, F (stepm i y) = stepn i y) (s : Nat) :
    ∀ (i : Nat) (x : Y), F (chain stepm i s x) = chain stepn i s x := by
  induction s with
  | zero => intro i x; exact hpure x
  | succ s ih =>
    intro i x
    rw [chain_head, hbind, hstep, chain_head]
    exact congrArg (fun k => stepn i x >>= k) (funext fun y => ih (i + 1) y)

end SLHDSA.Wots.Program


namespace SLHDSA.Wots.Program

universe u v w
variable {I : Type w} {Y Family : Type u} {m : Type u → Type v}

/-- Chain collection retains the caller's monadic initialization at every index. -/
theorem runChains_eq (collect : (I → m Y) → m Family) (withInitial : I → (Y → m Y) → m Y)
    (advance : I → Nat → Nat → Y → m Y) (starts lengths : I → Nat) :
    runChains collect withInitial advance starts lengths = collect (fun i =>
      withInitial i (advance i (starts i) (lengths i))) := by
  simp only [runChains]

/-- Public-key tops use every chain's full interval. -/
theorem runTops_publicKey (collect : (I → m Y) → m Family) (withInitial : I → (Y → m Y) → m Y)
    (advance : I → Nat → Nat → Y → m Y) (maxSteps : Nat) :
    runTops collect withInitial advance maxSteps .publicKey =
      runChains collect withInitial advance (fun _ => 0) (fun _ => maxSteps) := by
  simp only [runTops]

/-- Signing tops use the message-selected interval lengths. -/
theorem runTops_sign (collect : (I → m Y) → m Family) (withInitial : I → (Y → m Y) → m Y)
    (advance : I → Nat → Nat → Y → m Y) (maxSteps : Nat) (digits : I → Nat) :
    runTops collect withInitial advance maxSteps (.sign digits) =
      runChains collect withInitial advance (fun _ => 0) digits := by
  simp only [runTops]

/-- Recovery starts at the signature and executes only the complementary suffix. -/
theorem runTops_recover (collect : (I → m Y) → m Family)
    (withInitial : I → (Y → m Y) → m Y) (advance : I → Nat → Nat → Y → m Y) (maxSteps : Nat)
    (signature : I → Y) (digits : I → Nat) :
    runTops collect withInitial advance maxSteps (.recover signature digits) =
      collect (fun i => advance i (digits i) (maxSteps - digits i) (signature i)) := by
  simp only [runTops, runChains]

variable [Monad m]

/-- The public-key result compresses the collected public-key tops once. -/
theorem run_publicKey (collect : (I → m Y) → m Family) (withInitial : I → (Y → m Y) → m Y)
    (advance : I → Nat → Nat → Y → m Y) (compress : Family → m Y) (maxSteps : Nat) :
    run collect withInitial advance compress maxSteps .publicKey = (do
      let tops ← runTops collect withInitial advance maxSteps .publicKey
      compress tops) := by
  simp only [run]

/-- The recovery result compresses the collected suffix tops once. -/
theorem run_recover (collect : (I → m Y) → m Family) (withInitial : I → (Y → m Y) → m Y)
    (advance : I → Nat → Nat → Y → m Y) (compress : Family → m Y) (maxSteps : Nat)
    (signature : I → Y) (digits : I → Nat) :
    run collect withInitial advance compress maxSteps (.recover signature digits) = (do
      let tops ← runTops collect withInitial advance maxSteps (.recover signature digits)
      compress tops) := by
  simp only [run]

end SLHDSA.Wots.Program
