/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Wots.Program
import all HashSig.SLHDSA.Wots.Program
public import Init.Control.Lawful

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

/-- In a lawful monad the final step can equivalently follow the shorter prefix. -/
theorem chain_prefix [LawfulMonad m] (step : Nat → Y → m Y) (s : Nat) :
    ∀ (i : Nat) (x : Y),
      chain step i (s + 1) x = chain step i s x >>= fun y => step (i + s) y := by
  induction s with
  | zero => intro i x; simp [chain]
  | succ s ih =>
    intro i x
    calc
      chain step i (s + 1 + 1) x =
          step i x >>= fun y => chain step (i + 1) (s + 1) y := rfl
      _ = step i x >>= fun y =>
          (chain step (i + 1) s y >>= fun z => step (i + 1 + s) z) :=
        congrArg (fun k => step i x >>= k) (funext fun y => ih (i + 1) y)
      _ = (step i x >>= fun y => chain step (i + 1) s y) >>=
          fun z => step (i + (s + 1)) z := by
        simp only [bind_assoc, Nat.add_assoc, Nat.add_comm 1 s]
      _ = chain step i (s + 1) x >>= fun z => step (i + (s + 1)) z := rfl

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
variable {I : Type w} {Y Family : Type u} {m : Type u → Type v} [Monad m]

/-- Chain collection retains the caller's monadic initialization at every index. -/
theorem runChains_eq (collect : (I → m Y) → m Family) (secret : I → m Y)
    (step : I → Nat → Y → m Y) (starts lengths : I → Nat) :
    runChains collect secret step starts lengths = collect (fun i => do
      let initial ← secret i
      chain (step i) (starts i) (lengths i) initial) := by
  simp only [runChains]

/-- Public-key tops use every chain's full interval. -/
theorem runTops_publicKey (collect : (I → m Y) → m Family) (secret : I → m Y)
    (step : I → Nat → Y → m Y) (maxSteps : Nat) :
    runTops collect secret step maxSteps .publicKey =
      runChains collect secret step (fun _ => 0) (fun _ => maxSteps) := by
  simp only [runTops]

/-- Signing tops use the message-selected interval lengths. -/
theorem runTops_sign (collect : (I → m Y) → m Family) (secret : I → m Y)
    (step : I → Nat → Y → m Y) (maxSteps : Nat) (digits : I → Nat) :
    runTops collect secret step maxSteps (.sign digits) =
      runChains collect secret step (fun _ => 0) digits := by
  simp only [runTops]

/-- Recovery starts at the signature and executes only the complementary suffix. -/
theorem runTops_recover [LawfulMonad m] (collect : (I → m Y) → m Family)
    (secret : I → m Y) (step : I → Nat → Y → m Y) (maxSteps : Nat)
    (signature : I → Y) (digits : I → Nat) :
    runTops collect secret step maxSteps (.recover signature digits) =
      collect (fun i => chain (step i) (digits i) (maxSteps - digits i) (signature i)) := by
  simp only [runTops, runChains, pure_bind]

/-- The public-key result compresses the collected public-key tops once. -/
theorem run_publicKey (collect : (I → m Y) → m Family) (secret : I → m Y)
    (step : I → Nat → Y → m Y) (compress : Family → m Y) (maxSteps : Nat) :
    run collect secret step compress maxSteps .publicKey = (do
      let tops ← runTops collect secret step maxSteps .publicKey
      compress tops) := by
  simp only [run]

/-- The recovery result compresses the collected suffix tops once. -/
theorem run_recover (collect : (I → m Y) → m Family) (secret : I → m Y)
    (step : I → Nat → Y → m Y) (compress : Family → m Y) (maxSteps : Nat)
    (signature : I → Y) (digits : I → Nat) :
    run collect secret step compress maxSteps (.recover signature digits) = (do
      let tops ← runTops collect secret step maxSteps (.recover signature digits)
      compress tops) := by
  simp only [run]

end SLHDSA.Wots.Program
