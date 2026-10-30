/-
Copyright (c) 2026 Tom Wambsgans, Nicolas Consigny, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans, Nicolas Consigny, Alexander Hicks
-/

module
public import Init.Control.Basic

/-!
# Callback-parametric WOTS construction

One ordered chain and one collection mechanism serve public-key generation,
signing, and public-key recovery. Address construction and result representation
are supplied by the caller; secret reads remain monadic actions.
-/

public section

namespace SLHDSA.Wots.Program

universe u v w

variable {I : Type w} {Y Family : Type u} {m : Type u → Type v} [Monad m]

/-- Apply consecutive indexed hash steps, with the remaining work behind the bind. -/
def chain (step : Nat → Y → m Y) : Nat → Nat → Y → m Y
  | _, 0, value => pure value
  | start, steps + 1, value => do
    let next ← step start value
    chain step (start + 1) steps next

/-- Collect the chains with explicit initial values and per-chain intervals. -/
def runChains (collect : (I → m Y) → m Family) (secret : I → m Y)
    (step : I → Nat → Y → m Y) (starts lengths : I → Nat) : m Family :=
  collect fun i => do
    let initial ← secret i
    chain (step i) (starts i) (lengths i) initial

/-- The three choices of chain interval and initial value. -/
inductive TopsJob (I : Type w) (Y : Type u) where
  | publicKey
  | sign (digits : I → Nat)
  | recover (signature : I → Y) (digits : I → Nat)

/-- Run the selected chain construction in the caller's native result family. -/
def runTops (collect : (I → m Y) → m Family) (secret : I → m Y)
    (step : I → Nat → Y → m Y) (maxSteps : Nat) : TopsJob I Y → m Family
  | .publicKey => runChains collect secret step (fun _ => 0) (fun _ => maxSteps)
  | .sign digits => runChains collect secret step (fun _ => 0) digits
  | .recover signature digits =>
    runChains collect (fun i => pure (signature i)) step digits
      (fun i => maxSteps - digits i)

/-- Public entry points with their native signature or node result type. -/
inductive Job (I : Type w) (Y Family : Type u) : Type u → Type (max u w) where
  | publicKeyTops : Job I Y Family Family
  | publicKey : Job I Y Family Y
  | sign (digits : I → Nat) : Job I Y Family Family
  | recoverTops (signature : I → Y) (digits : I → Nat) : Job I Y Family Family
  | recover (signature : I → Y) (digits : I → Nat) : Job I Y Family Y

/-- Execute a WOTS mode, compressing only public-key results. -/
def run {α : Type u} (collect : (I → m Y) → m Family) (secret : I → m Y)
    (step : I → Nat → Y → m Y) (compress : Family → m Y) (maxSteps : Nat) :
    Job I Y Family α → m α
  | .publicKeyTops => runTops collect secret step maxSteps .publicKey
  | .publicKey => do
    let tops ← runTops collect secret step maxSteps .publicKey
    compress tops
  | .sign digits => runTops collect secret step maxSteps (.sign digits)
  | .recoverTops signature digits =>
    runTops collect secret step maxSteps (.recover signature digits)
  | .recover signature digits => do
    let tops ← runTops collect secret step maxSteps (.recover signature digits)
    compress tops

end SLHDSA.Wots.Program
