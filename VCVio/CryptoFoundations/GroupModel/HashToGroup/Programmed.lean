/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.HashToGroup.Coins

/-! # Programmed hash-to-group and certified executions

Fresh coefficient vectors are sampled over a fixed reduction basis. The cache retains the
vectors, so repeated replies have exactly the same representation. A certified interaction
explains its outputs over the recorded rows, including any fixed-input rows supplied initially.
-/

public section

namespace GroupModel.HashToGroup

open OracleComp OracleSpec Interaction

variable {Label F G κ Data α Query : Type} {Reply : Query → Type}

/-- The programmed interaction oracle evaluates sampled coefficient vectors over `B`. -/
@[expose] def programmed [DecidableEq Label] [CommSemiring F] [AddCommMonoid G]
    [Module F G] [Fintype κ] (B : κ → G) (sample : Label → ProbComp (κ → F)) :
    QueryImpl (gameSpec Label G) (StateT (State Label (κ → F)) ProbComp) :=
  game (Fintype.linearCombination F B) sample

/-- Uniform fresh programmed outputs perfectly simulate the honest oracle for every adaptive
computation, including the final cache and receipt list after decoding. -/
theorem programmed_simulation [DecidableEq Label] [CommSemiring F] [AddCommMonoid G]
    [Module F G] [Fintype κ] [SampleableType G]
    (B : κ → G) (sample : Label → ProbComp (κ → F))
    (h : ∀ l, Fintype.linearCombination F B <$> sample l =ᵈ ($ᵗ G : ProbComp G))
    (p : OracleComp (gameSpec Label G) α) (st : State Label (κ → F)) :
    Prod.map id (mapState (Fintype.linearCombination F B)) <$>
        (simulateQ (programmed B sample) p).run st =ᵈ
      (simulateQ honest p).run (mapState (Fintype.linearCombination F B) st) :=
  simulateQ_game_mapState (Fintype.linearCombination F B) id sample (fun _ => $ᵗ G) h p st

/-- The two-element reduction basis containing a generator and a challenge. -/
@[expose] def pairBasis (g Z : G) : Fin 2 → G := ![g, Z]

/-- Independent uniform coefficients for generator-and-challenge programming. -/
@[expose] def pairSample [SampleableType F] : ProbComp (Fin 2 → F) := do
  let y ← $ᵗ F
  let x ← $ᵗ F
  pure ![x, y]

/-- The programmed two-coordinate row evaluates to the standard challenge embedding. -/
@[simp] theorem linearCombination_pairBasis [CommSemiring F] [AddCommMonoid G] [Module F G]
    (g Z : G) (x y : F) : Fintype.linearCombination F (pairBasis g Z) ![x, y] = x • g + y • Z := by
  simp [Fintype.linearCombination_apply, pairBasis, Fin.sum_univ_two]

/-- Uniform generator masks make challenge embeddings uniform, for any fixed challenge. -/
theorem pairSample_uniform [CommSemiring F] [AddCommGroup G] [Module F G]
    [SampleableType F] [SampleableType G]
    (g Z : G) (hg : Function.Bijective (· • g : F → G)) :
    Fintype.linearCombination F (pairBasis g Z) <$> (pairSample : ProbComp (Fin 2 → F)) =ᵈ
      ($ᵗ G : ProbComp G) := by
  have h (y : F) : (fun x : F => x • g + y • Z) <$> ($ᵗ F : ProbComp F) =ᵈ
      ($ᵗ G : ProbComp G) :=
    SampleableType.map_uniformSample_evalDistEq_of_bijective
      ((Equiv.addRight (y • Z)).bijective.comp hg)
  simpa [pairSample, map_bind, map_pure, ← map_eq_pure_bind] using
    (EvalDistEq.bind_right ($ᵗ F : ProbComp F) h).trans (EvalDistEq.bind_const _ _)

/-- A uniform scalar represented as the single coordinate of a generator basis. -/
@[expose] def scalarSample [SampleableType F] : ProbComp (Unit → F) :=
  (fun x _ => x) <$> ($ᵗ F : ProbComp F)

/-- Scalar-only programming is uniform whenever scalar multiplication by the generator is
bijective. -/
theorem scalarSample_uniform [CommSemiring F] [AddCommMonoid G] [Module F G]
    [SampleableType F] [SampleableType G]
    (g : G) (hg : Function.Bijective (· • g : F → G)) :
    Fintype.linearCombination F (fun _ : Unit => g) <$> (scalarSample : ProbComp (Unit → F)) =ᵈ
      ($ᵗ G : ProbComp G) := by
  simpa [scalarSample, Fintype.linearCombination_apply] using
    SampleableType.map_uniformSample_evalDistEq_of_bijective hg

/-- Run an explained computation against the programmed oracle and retain its coefficient log. -/
@[expose] def runProgram [DecidableEq Label] [CommSemiring F] [AddCommMonoid G]
    [Module F G] [Fintype κ] (B : κ → G) (sample : Label → ProbComp (κ → F))
    (p : OracleComp (explainedSpec F (fun _ : Unit => G) Label (fun _ => Unit)) α)
    (st : State Label (κ → F)) : ProbComp (α × State Label (κ → F)) :=
  (simulateQ (programmed B sample) (interactionProgram p)).run st

/-- A certified computation's final explanation is valid over the actual recorded coefficient
rows. Initial rows may represent fixed inputs in an enlarged basis. -/
theorem runProgram_valid [DecidableEq Label] [CommSemiring F] [AddCommMonoid G]
    [Module F G] [Fintype κ] (B : κ → G) (sample : Label → ProbComp (κ → F))
    (p : OracleComp (explainedSpec F (fun _ : Unit => G) Label (fun _ => Unit))
      (Explained F Data (fun _ : Unit => G))) (st : State Label (κ → F))
    (hp : IsAlgebraic (fun _ => st.2.map (Fintype.linearCombination F B)) p)
    (z : Explained F Data (fun _ : Unit => G) × State Label (κ → F))
    (hz : z ∈ support (runProgram B sample p st)) :
    z.1.Valid (fun _ => z.2.2.map (Fintype.linearCombination F B)) :=
  run_receipts_valid (programmed B sample) (fun st => st.2.map (Fintype.linearCombination F B))
    (fun q st z hz => by
      obtain ⟨w, hw, rfl⟩ := by
        simpa only [programmed, game, StateT.run_map, support_map, Set.mem_image] using hz
      exact oracle_receipts _ sample q.data st w hw) p st hp z hz

/-- Transport all final outputs of a certified programmed run to the reduction's basis. -/
theorem runProgram_transport [DecidableEq Label] [CommSemiring F] [AddCommMonoid G]
    [Module F G] [Fintype κ] (B : κ → G) (sample : Label → ProbComp (κ → F))
    (p : OracleComp (explainedSpec F (fun _ : Unit => G) Label (fun _ => Unit))
      (Explained F Data (fun _ : Unit => G))) (st : State Label (κ → F))
    (hp : IsAlgebraic (fun _ => st.2.map (Fintype.linearCombination F B)) p)
    (z : Explained F Data (fun _ : Unit => G) × State Label (κ → F))
    (hz : z ∈ support (runProgram B sample p st)) :
    (transportExplained (fun _ => z.2.2) z.1 ()).map (Fintype.linearCombination F B) =
      z.1.value.groups () :=
  transportExplained_evaluate (fun _ => B) (fun _ => z.2.2) z.1
    (runProgram_valid B sample p st hp z hz) ()

end GroupModel.HashToGroup
