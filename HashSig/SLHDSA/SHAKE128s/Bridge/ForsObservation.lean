/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Bridge.Fors
public import VCVio.OracleComp.QueryTracking.WriterCost

/-!
# Stateful cost observations of the SHAKE128s FORS bridge

The complete common-world FORS program equality preserves its mapped signature, any additive
cost on actual raw query inputs and the final state of the shared handler. The policy observes
raw inputs; transporting a policy on typed roles additionally requires a cost pullback law.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.Bridge

open SLHDSA SLHDSA.Security

/-- Retain the complete FORS signature, ordered raw-query cost and arbitrary final cache/state. -/
theorem simulateQ_forsSign_withAddCost_run (indices : Fors.Indices) (md : List Byte)
    (hidx : ∀ i : Fin forsTrees,
      forsIdx FIPS205.params.params md i.val = (indices i).val)
    (sk pk : Digest) (address : Address) (hk : address.kind = .forsTree)
    {m : Type → Type*} [Monad m] {Cache C : Type} [AddMonoid C]
    (handler : QueryImpl (Game.World FIPS205.Answer) (StateT Cache m))
    (cost : (Game.World FIPS205.Answer).Domain → C) (initial : Cache) :
    ((simulateQ (handler.withAddCost cost)
      (simulateQ (relabel answerEquiv)
        (Fors.sign indices sk pk address : OracleComp OracleWorld ForsSignature))).runAdd).run
          initial =
    ((simulateQ (handler.withAddCost cost)
      ((fun signature i => forsTreeOfCore (signature[i.val]'i.isLt)) <$>
        simulateQ (encImpl FIPS205.params)
          (forsSignWithSecretM FIPS205.core
            (oracleSecret FIPS205.core (Equiv.refl _) (digestEquiv pk) (digestEquiv sk))
            md (digestEquiv pk) (toAdrs address) :
            OracleComp (unifSpec + hashSpec FIPS205.core)
              (ForsSigCore FIPS205.params.params FIPS205.core)))).runAdd).run initial :=
  congrArg (fun program =>
    ((simulateQ (handler.withAddCost cost) program).runAdd).run initial)
      (simulateQ_forsSign indices md hidx sk pk address hk)

end SLHDSA.SHAKE128s.Bridge
