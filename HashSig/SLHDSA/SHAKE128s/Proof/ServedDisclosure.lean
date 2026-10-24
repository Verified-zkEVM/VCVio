/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CacheAvailability

/-!
# Availability is monotone in the disclosed set

A node's availability (`GraphStakes`) is monotone in the set of FORS positions the signer has
disclosed (`available_mono_signed`). The disclosed set enters only at the `forsPrf` leaves, so
the statement holds whatever that set is read from, for instance the signing log
(`ServedLog.disclosedByLog`). The state that carries the log is left abstract.
-/

public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.ServedDisclosure

open CanonicalGraph

variable {State : Type}

/-- **Availability is monotone in the disclosed set**, whatever that set is read from. The
disclosed set enters only at the `forsPrf` leaves, so this is the whole of it. -/
theorem available_mono_signed (revealed : WotsKey → Fin chains → Nat)
    {signedLeft signedRight : ForsKey → Finset (Fin (forsTrees * 2 ^ forsHeight))}
    (hsubset : ∀ key, signedLeft key ⊆ signedRight key) (node : Node)
    (havailable : Available revealed signedLeft node) :
    Available revealed signedRight node := by
  cases node with
  | secretSeed => exact havailable
  | structural parent =>
    cases parent with
    | wotsPrf key chain => exact havailable
    | wotsHash key chain step => exact havailable
    | forsPrf key index => exact hsubset key havailable
    | wotsPk key => exact True.intro
    | tree location height index => exact True.intro
    | forsTree key height index => exact True.intro
    | forsRoots key => exact True.intro

variable [HasQuery HashSpec Id]

end SlhDsaSecurity.ServedDisclosure
