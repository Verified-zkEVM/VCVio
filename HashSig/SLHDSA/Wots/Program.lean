/-
Copyright (c) 2026 Tom Wambsgans, Nicolas Consigny, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans, Nicolas Consigny, Alexander Hicks
-/

module
public import Init.Control.Basic

/-!
# Callback-parametric WOTS construction

Public-key generation, signing and public-key recovery share their choice of chain intervals
and compression. Callers supply the interval evaluator and the representation of each initial
value, including any secret-derivation effect.
-/

public section

namespace SLHDSA.Wots.Program

universe u v w

variable {I : Type w} {Y Family : Type u} {m : Type u → Type v} [Monad m]

/-- Apply consecutive indexed hash steps, with the remaining work behind the bind. -/
@[expose] def chain (step : Nat → Y → m Y) : Nat → Nat → Y → m Y
  | _, 0, value => pure value
  | start, steps + 1, value => do
    let next ← step start value
    chain step (start + 1) steps next

/-- Collect the chains with explicit initial values and per-chain intervals. -/
@[expose] def runChains (collect : (I → m Y) → m Family) (withInitial : I → (Y → m Y) → m Y)
    (advance : I → Nat → Nat → Y → m Y) (starts lengths : I → Nat) : m Family :=
  collect fun i => withInitial i (advance i (starts i) (lengths i))

/-- The three choices of chain interval and initial value. -/
inductive TopsJob (I : Type w) (Y : Type u) where
  | publicKey
  | sign (digits : I → Nat)
  | recover (signature : I → Y) (digits : I → Nat)

/-- Run the selected chain construction in the caller's native result family. -/
@[expose] def runTops (collect : (I → m Y) → m Family) (withInitial : I → (Y → m Y) → m Y)
    (advance : I → Nat → Nat → Y → m Y) (maxSteps : Nat) : TopsJob I Y → m Family
  | .publicKey => runChains collect withInitial advance (fun _ => 0) (fun _ => maxSteps)
  | .sign digits => runChains collect withInitial advance (fun _ => 0) digits
  | .recover signature digits =>
    runChains collect (fun i k => k (signature i)) advance digits
      (fun i => maxSteps - digits i)

/-- Public entry points with their native signature or node result type. -/
inductive Job (I : Type w) (Y Family : Type u) : Type u → Type (max u w) where
  | publicKeyTops : Job I Y Family Family
  | publicKey : Job I Y Family Y
  | sign (digits : I → Nat) : Job I Y Family Family
  | recoverTops (signature : I → Y) (digits : I → Nat) : Job I Y Family Family
  | recover (signature : I → Y) (digits : I → Nat) : Job I Y Family Y

/-- Execute a WOTS mode, compressing only public-key results. -/
@[expose] def run {α : Type u} (collect : (I → m Y) → m Family) (withInitial : I → (Y → m Y) → m Y)
    (advance : I → Nat → Nat → Y → m Y) (compress : Family → m Y) (maxSteps : Nat) :
    Job I Y Family α → m α
  | .publicKeyTops => runTops collect withInitial advance maxSteps .publicKey
  | .publicKey => do
    let tops ← runTops collect withInitial advance maxSteps .publicKey
    compress tops
  | .sign digits => runTops collect withInitial advance maxSteps (.sign digits)
  | .recoverTops signature digits =>
    runTops collect withInitial advance maxSteps (.recover signature digits)
  | .recover signature digits => do
    let tops ← runTops collect withInitial advance maxSteps (.recover signature digits)
    compress tops

end SLHDSA.Wots.Program
