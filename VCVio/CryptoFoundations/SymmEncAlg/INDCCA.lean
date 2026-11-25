/-
Copyright (c) 2026 Minhyuk Hwang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Minhyuk Hwang
-/

module

public import VCVio.CryptoFoundations.SymmEncAlg.INDCPA
public import VCVio.OracleComp.SimSemantics.StateT.Basic

/-!
# CCA security for multiple encryptions

This file defines the left-or-right chosen-ciphertext game of a symmetric encryption scheme
(Katz–Lindell, 3rd ed., §5.1.2). Besides the ambient oracles `spec` and the left-or-right
challenge oracle of the CPA game (`SymmEncAlg.IND_CPA_Experiment`), the adversary gets a
decryption oracle `C →ₒ Option M`. The challenger keeps the list of ciphertexts that the
left-or-right oracle returned, and the decryption oracle answers `none` on each of them; on any
other ciphertext it answers `encAlg.decrypt k c`.

Katz–Lindell state the game with a single challenge pair. This is its left-or-right form with any
number of challenge queries, in which every ciphertext the challenge oracle returned is refused;
a pair `(m, m)` is an ordinary encryption query. A refused query is answered `none`, the same
value as a ciphertext that fails to decrypt. Refusing the ciphertexts of `(m, m)` queries as well
costs the adversary nothing when decryption is correct, since it knows what they decrypt to.
Without correctness the game is weaker than one with a separate encryption oracle whose
ciphertexts may be decrypted.

## Main definitions

* `SymmEncAlg.IND_CCA_Adversary`: a left-or-right CCA adversary.
* `SymmEncAlg.IND_CCA_Adversary.MakesAtMostDecryptionQueries`: a bound on its decryption queries.
* `SymmEncAlg.IND_CCA_challengeImpl`, `SymmEncAlg.IND_CCA_decryptImpl`: the two challenger oracles
  over the log of challenge ciphertexts.
* `SymmEncAlg.IND_CCA_Experiment`, `SymmEncAlg.IND_CCA_Game`, `SymmEncAlg.IND_CCA_Advantage`.

## Main statements

* `SymmEncAlg.IND_CCA_Advantage_eq_boolDist`: in `ProbComp`, the advantage is the distance between
  the probabilities that the two fixed-bit experiments output `true`.
-/

public section

open OracleSpec OracleComp ENNReal

namespace SymmEncAlg

variable {ι : Type} {spec : OracleSpec ι} {M K C : Type}

/-- A left-or-right CCA adversary: a computation with the ambient oracles `spec`, the
left-or-right challenge oracle and the decryption oracle, returning a guess of the hidden bit. -/
abbrev IND_CCA_Adversary (_encAlg : SymmEncAlg (OracleComp spec) M K C) :=
  OracleComp (spec + LeftOrRight.spec M C + (C →ₒ Option M)) Bool

/-- A CCA adversary `MakesAtMostDecryptionQueries q` when it makes at most `q` decryption
queries. -/
@[expose] def IND_CCA_Adversary.MakesAtMostDecryptionQueries
    {encAlg : SymmEncAlg (OracleComp spec) M K C} (adversary : encAlg.IND_CCA_Adversary)
    (q : ℕ) : Prop :=
  OracleComp.IsQueryBoundP adversary (· matches .inr _) q

variable {Λ : Type} [DecidableEq Λ]

/-- The left-or-right oracle of the CCA game at bit `b`: it answers as
`LeftOrRight.oracle (encAlg.encrypt k) leak b` and logs every ciphertext it returns. -/
@[expose, simps]
def IND_CCA_challengeImpl (encAlg : SymmEncAlg (OracleComp spec) M K C) (k : K)
    (leak : M → Λ) (b : Bool) :
    QueryImpl (LeftOrRight.spec M C) (StateT (List C) (OracleComp spec)) where
  toFun mm := do
    let c? ← (LeftOrRight.oracle (encAlg.encrypt k) leak b mm : OracleComp spec (Option C))
    modify fun log => match c? with
      | some c => c :: log
      | none => log
    return c?

/-- The decryption oracle of the CCA game: it rejects every logged challenge ciphertext with
`none` and decrypts any other ciphertext. -/
@[expose, simps]
def IND_CCA_decryptImpl [DecidableEq C] (encAlg : SymmEncAlg (OracleComp spec) M K C)
    (k : K) : QueryImpl (C →ₒ Option M) (StateT (List C) (OracleComp spec)) where
  toFun c := do
    let log ← get
    if c ∈ log then return none else (encAlg.decrypt k c : OracleComp spec (Option M))

/-- The handler of the CCA game at bit `b` under the key `k`. -/
@[expose] def IND_CCA_impl [DecidableEq C] (encAlg : SymmEncAlg (OracleComp spec) M K C) (k : K)
    (leak : M → Λ) (b : Bool) :
    QueryImpl (spec + LeftOrRight.spec M C + (C →ₒ Option M))
      (StateT (List C) (OracleComp spec)) :=
  spec.passthrough + encAlg.IND_CCA_challengeImpl k leak b + encAlg.IND_CCA_decryptImpl k

/-- The left-or-right CCA experiment at hidden bit `b`: sample a key with `encAlg.keygen`, then
run the adversary against the CCA handler from the empty challenge log. -/
@[expose] def IND_CCA_Experiment [DecidableEq C] (encAlg : SymmEncAlg (OracleComp spec) M K C)
    (leak : M → Λ) (adversary : encAlg.IND_CCA_Adversary) (b : Bool) : OracleComp spec Bool := do
  let k ← encAlg.keygen
  (simulateQ (encAlg.IND_CCA_impl k leak b) adversary).run' []

/-- The left-or-right CCA game: sample a uniform hidden bit, run the experiment at that bit, and
return whether the adversary guessed it. -/
@[expose] def IND_CCA_Game [DecidableEq C] (encAlg : SymmEncAlg (OracleComp spec) M K C)
    (runtime : ProbCompRuntime (OracleComp spec)) (leak : M → Λ)
    (adversary : encAlg.IND_CCA_Adversary) : OracleComp spec Bool := do
  let b ← runtime.liftProbComp ($ᵗ Bool)
  let b' ← encAlg.IND_CCA_Experiment leak adversary b
  return (b == b')

/-- The left-or-right CCA advantage: the Boolean bias of the game,
`|Pr[b' = b] - Pr[b' ≠ b]|`. When the game never fails this is twice Katz–Lindell's
`|Pr[PrivK = 1] - 1/2|`, and in `ProbComp` it equals the distance between the two fixed-bit
experiments (`IND_CCA_Advantage_eq_boolDist`). -/
@[expose] noncomputable def IND_CCA_Advantage [DecidableEq C]
    (encAlg : SymmEncAlg (OracleComp spec) M K C) (runtime : ProbCompRuntime (OracleComp spec))
    (leak : M → Λ) (adversary : encAlg.IND_CCA_Adversary) : ℝ≥0∞ :=
  (runtime.evalDist (encAlg.IND_CCA_Game runtime leak adversary)).boolBias

/-- In `ProbComp`, the CCA advantage is the distance between the probabilities that the
experiments at the two hidden bits output `true`. -/
theorem IND_CCA_Advantage_eq_boolDist [DecidableEq C] (encAlg : SymmEncAlg ProbComp M K C)
    (leak : M → Λ) (adversary : encAlg.IND_CCA_Adversary) :
    encAlg.IND_CCA_Advantage ProbCompRuntime.probComp leak adversary =
      𝒟[encAlg.IND_CCA_Experiment leak adversary true].boolDist
        𝒟[encAlg.IND_CCA_Experiment leak adversary false] := by
  rw [IND_CCA_Advantage, ProbCompRuntime.probComp_evalDist, IND_CCA_Game,
    ← evalDist_boolBias_bind_uniformBool]
  congr 2
  exact bind_congr fun b => by cases b <;> rfl

end SymmEncAlg
