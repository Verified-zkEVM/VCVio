/-
Copyright (c) 2026 Minhyuk Hwang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Minhyuk Hwang
-/

module

public import VCVio.CryptoFoundations.SymmEncAlg.Defs
public import VCVio.CryptoFoundations.LeftOrRight
public import VCVio.CryptoFoundations.SecExp.Measure
public import VCVio.OracleComp.ProbCompLift
public import VCVio.OracleComp.SimSemantics.Append
public import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# CPA security for multiple encryptions

This file defines the left-or-right chosen-plaintext game of a symmetric encryption scheme
(Katz–Lindell, 3rd ed., §3.4.3, CPA-security for multiple encryptions). The adversary keeps the
scheme's ambient oracles `spec` and gains the left-or-right challenge oracle
`LeftOrRight.oracle (encAlg.encrypt k) leak b` under a key `k` from `encAlg.keygen`: each
admissible pair `(m₀, m₁)` is answered by a fresh encryption of `m_b`. A pair `(m, m)` is an
ordinary encryption query, so the one oracle is both the encryption oracle and the challenge
oracle of the textbook game. The leakage function `leak` states which pairs are admissible:
`fun _ => ()` for fixed-length messages, the length for variable-length ones.

The game mirrors the multi-query game `DEMScheme.IND_CPA_Game` of a data encapsulation mechanism,
which samples a uniform key. A `SymmEncAlg` carries its own key generation, which need not be
uniform, so the experiment here samples the key with `encAlg.keygen`.

## Main definitions

* `SymmEncAlg.IND_CPA_Adversary`: a left-or-right CPA adversary.
* `SymmEncAlg.IND_CPA_Adversary.MakesAtMostQueries`: a bound on its challenge queries.
* `SymmEncAlg.IND_CPA_Experiment`: the experiment at a fixed hidden bit.
* `SymmEncAlg.IND_CPA_Game`, `SymmEncAlg.IND_CPA_Advantage`: the hidden-bit game and its bias.

## Main statements

* `SymmEncAlg.IND_CPA_Advantage_eq_boolDist`: in `ProbComp`, the advantage is the distance between
  the probabilities that the two fixed-bit experiments output `true`.
-/

public section

open OracleSpec OracleComp ENNReal

namespace SymmEncAlg

variable {ι : Type} {spec : OracleSpec ι} {M K C : Type}

/-- A left-or-right CPA adversary: a computation with the scheme's ambient oracles `spec` and the
left-or-right challenge oracle `LeftOrRight.spec M C`, returning a guess of the hidden bit. -/
abbrev IND_CPA_Adversary (_encAlg : SymmEncAlg (OracleComp spec) M K C) :=
  OracleComp (spec + LeftOrRight.spec M C) Bool

/-- A CPA adversary `MakesAtMostQueries q` when it makes at most `q` queries to the challenge
oracle. Queries to the ambient oracles are unrestricted. -/
@[expose] def IND_CPA_Adversary.MakesAtMostQueries {encAlg : SymmEncAlg (OracleComp spec) M K C}
    (adversary : encAlg.IND_CPA_Adversary) (q : ℕ) : Prop :=
  OracleComp.IsQueryBoundP adversary (· matches .inr _) q

variable {Λ : Type} [DecidableEq Λ]

/-- The left-or-right CPA experiment at hidden bit `b`, for the leakage function `leak`: sample a
key with `encAlg.keygen`, then run the adversary with its ambient queries forwarded and its
challenge queries answered by `LeftOrRight.oracle (encAlg.encrypt k) leak b`. -/
@[expose] def IND_CPA_Experiment (encAlg : SymmEncAlg (OracleComp spec) M K C) (leak : M → Λ)
    (adversary : encAlg.IND_CPA_Adversary) (b : Bool) : OracleComp spec Bool := do
  let k ← encAlg.keygen
  simulateQ (QueryImpl.id' spec + LeftOrRight.oracle (encAlg.encrypt k) leak b) adversary

/-- The left-or-right CPA game: sample a uniform hidden bit, run the experiment at that bit, and
return whether the adversary guessed it. -/
@[expose] def IND_CPA_Game (encAlg : SymmEncAlg (OracleComp spec) M K C)
    (runtime : ProbCompRuntime (OracleComp spec)) (leak : M → Λ)
    (adversary : encAlg.IND_CPA_Adversary) : OracleComp spec Bool := do
  let b ← runtime.liftProbComp ($ᵗ Bool)
  let b' ← encAlg.IND_CPA_Experiment leak adversary b
  return (b == b')

/-- The left-or-right CPA advantage: the Boolean bias of the game,
`|Pr[b' = b] - Pr[b' ≠ b]|`. When the game never fails this is twice Katz–Lindell's
`|Pr[PrivK = 1] - 1/2|`, and in `ProbComp` it equals the distance between the two fixed-bit
experiments (`IND_CPA_Advantage_eq_boolDist`). -/
@[expose] noncomputable def IND_CPA_Advantage (encAlg : SymmEncAlg (OracleComp spec) M K C)
    (runtime : ProbCompRuntime (OracleComp spec)) (leak : M → Λ)
    (adversary : encAlg.IND_CPA_Adversary) : ℝ≥0∞ :=
  (runtime.evalDist (encAlg.IND_CPA_Game runtime leak adversary)).boolBias

/-- In `ProbComp`, the CPA advantage is the distance between the probabilities that the
experiments at the two hidden bits output `true`. -/
theorem IND_CPA_Advantage_eq_boolDist (encAlg : SymmEncAlg ProbComp M K C) (leak : M → Λ)
    (adversary : encAlg.IND_CPA_Adversary) :
    encAlg.IND_CPA_Advantage ProbCompRuntime.probComp leak adversary =
      𝒟[encAlg.IND_CPA_Experiment leak adversary true].boolDist
        𝒟[encAlg.IND_CPA_Experiment leak adversary false] := by
  rw [IND_CPA_Advantage, ProbCompRuntime.probComp_evalDist, IND_CPA_Game,
    ← evalDist_boolBias_bind_uniformBool]
  congr 2
  exact bind_congr fun b => by cases b <;> rfl

end SymmEncAlg
