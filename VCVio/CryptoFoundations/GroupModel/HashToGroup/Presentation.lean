/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.HashToGroup.Programmed
public import VCVio.CryptoFoundations.GroupModel.ToExplained

/-! # Hash-to-group in the handle presentation

The existing handle-to-explanation translation applies to the programmed hash oracle in its
state monad. Thus it preserves the full private coefficient cache and receipt log as well as
the returned group values. Private coins remain available through the shared random handler.
-/

public section

namespace GroupModel.HashToGroup

open OracleComp OracleSpec Interaction

variable {Label F G κ : Type} {E : Unit → Type}

/-- Translating a handle adversary to an interaction preserves its returned values and all
programmed-hash state. The handle game installs replies using `liftGame` and `pushGroups`. -/
theorem toExplained_programmed_run [DecidableEq Label] [CommSemiring F]
    [AddCommMonoid G] [Module F G] [DecidableEq G] [Fintype κ]
    (B : κ → G) (sample : Label → ProbComp (κ → F))
    (A : HandleAdversary F (discreteSig Unit) E Unit Label (fun _ => Unit) Unit)
    (M : Model F (discreteSig Unit) (fun _ : Unit => G))
    (enc : (s : Unit) → G → E s)
    (random : QueryImpl unifSpec (StateT (State Label (κ → F)) ProbComp))
    (input : Message Unit (fun _ : Unit => G)) :
    (fun z => z.1.value) <$> (toExplained A enc).run
        (withCoins random (programmed B sample)) input =
      (fun z => lookupMessage z.2 z.1) <$>
        A.run M enc random (programmed B sample) input :=
  toExplained_run A M enc random (programmed B sample) input

end GroupModel.HashToGroup
