/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.OracleComp.SimSemantics.SimulateQ
public import ToMathlib.Control.Monad.Fold

/-!
# Simulating finite monadic families

Oracle simulation preserves the index order and collected function of `Fin.mOfFn`. When each
component is simulated to a fixed pure value, the whole family returns that value function.
-/

public section

namespace OracleComp

universe u v

variable {ι : Type v} {spec : OracleSpec ι} {α : Type u}

/-- Simulation commutes with finite monadic sequencing in every lawful target monad. -/
theorem simulateQ_fin_mOfFn {m : Type u → Type*} [Monad m] [LawfulMonad m]
    (impl : QueryImpl spec m) {n : ℕ} (f : Fin n → OracleComp spec α) :
    simulateQ impl (Fin.mOfFn n f) = Fin.mOfFn n (fun i => simulateQ impl (f i)) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [Fin.mOfFn, simulateQ_bind, simulateQ_pure, ih]

/-- A finite family whose simulated components are pure returns the function of those values. -/
theorem simulateQ_fin_mOfFn_pure {m : Type u → Type*} [Monad m] [LawfulMonad m]
    (impl : QueryImpl spec m) {n : ℕ} (f : Fin n → OracleComp spec α) (g : Fin n → α)
    (hfg : ∀ i, simulateQ impl (f i) = pure (g i)) :
    simulateQ impl (Fin.mOfFn n f) = pure g := by
  rw [simulateQ_fin_mOfFn]
  simp_rw [hfg]
  exact Fin.mOfFn_pure n g

end OracleComp
