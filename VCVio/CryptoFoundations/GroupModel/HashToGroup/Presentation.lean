/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.HashToGroup.Coins
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

/-- A translated handle adversary's outputs transport over the coefficient log of its actual
coin-bearing run. Uniform private coins preserve that log. -/
theorem toExplained_programmed_transport [DecidableEq Label] [CommSemiring F]
    [AddCommMonoid G] [Module F G] [DecidableEq G] [Fintype κ]
    (B : κ → G) (sample : Label → ProbComp (κ → F))
    (A : HandleAdversary F (discreteSig Unit) E Unit Label (fun _ => Unit) Unit)
    (enc : (s : Unit) → G → E s) (st : State Label (κ → F))
    (z : (Explained F Unit (fun _ : Unit => G) × Groups (fun _ : Unit => G)) ×
      State Label (κ → F))
    (hz : z ∈ support (((toExplained A enc).run
      (withCoins coins (programmed B sample))
      ⟨(), fun _ => st.2.map (basisMap B)⟩).run st)) :
    (transportExplained (fun _ => z.2.2) z.1.1 ()).map (basisMap B) =
      z.1.1.value.groups () := by
  have hp : (z.1.1, z.2) ∈ support (runProgramWithCoins B sample
      ((toExplained A enc).main ⟨(), fun _ => st.2.map (basisMap B)⟩) st) := by
    rw [runProgramWithCoins, ← runGameWithCoins_run]
    rw [support_map]
    exact ⟨z, hz, rfl⟩
  exact runProgramWithCoins_transport B sample _ st ((toExplained A enc).algebraic _) _ hp

end GroupModel.HashToGroup
