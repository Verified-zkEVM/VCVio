/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.HashToGroup.Oracle
public import VCVio.CryptoFoundations.GroupModel.HashToGroup.Transport

/-! # Programmed hash-to-group and certified executions

Fresh coefficient vectors are sampled over a fixed reduction basis. The cache retains the
vectors, so repeated replies have exactly the same representation. A certified interaction
explains its outputs over the recorded rows, including any fixed-input rows supplied initially.
-/

public section

namespace GroupModel.HashToGroup

open OracleComp OracleSpec Interaction

variable {Label F G κ Data α : Type}

/-- The programmed interaction oracle evaluates sampled coefficient vectors over `B`. -/
@[expose] def programmed [DecidableEq Label] [CommSemiring F] [AddCommMonoid G]
    [Module F G] [Fintype κ] (B : κ → G) (sample : Label → ProbComp (κ → F)) :
    QueryImpl (gameSpec Label G) (StateT (State Label (κ → F)) ProbComp) :=
  game (basisMap B) sample

/-- Uniform fresh programmed outputs perfectly simulate the honest oracle for every adaptive
computation, including the final cache and receipt list after decoding. -/
theorem programmed_simulation [DecidableEq Label] [CommSemiring F] [AddCommMonoid G]
    [Module F G] [Fintype κ] [SampleableType G]
    (B : κ → G) (sample : Label → ProbComp (κ → F))
    (h : ∀ l, basisMap B <$> sample l =ᵈ ($ᵗ G : ProbComp G))
    (p : OracleComp (gameSpec Label G) α) (st : State Label (κ → F)) :
    Prod.map id (mapState (basisMap B)) <$> (simulateQ (programmed B sample) p).run st =ᵈ
      (simulateQ honest p).run (mapState (basisMap B) st) :=
  simulateQ_game_mapState (basisMap B) id sample (fun _ => $ᵗ G) h p st

/-- The two-element reduction basis containing a generator and a challenge. -/
@[expose] def pairBasis (g Z : G) : Fin 2 → G := ![g, Z]

/-- Independent uniform coefficients for generator-and-challenge programming. -/
@[expose] def pairSample [SampleableType F] : ProbComp (Fin 2 → F) := do
  let y ← $ᵗ F
  let x ← $ᵗ F
  pure ![x, y]

/-- The programmed two-coordinate row evaluates to the standard challenge embedding. -/
@[simp] theorem basisMap_pairBasis [CommSemiring F] [AddCommMonoid G] [Module F G]
    (g Z : G) (x y : F) : basisMap (pairBasis g Z) ![x, y] = x • g + y • Z := by
  simp [basisMap, pairBasis, Fin.sum_univ_two]

/-- Uniform generator masks make challenge embeddings uniform, for any fixed challenge. -/
theorem pairSample_uniform [CommSemiring F] [AddCommGroup G] [Module F G]
    [SampleableType F] [SampleableType G]
    (g Z : G) (hg : Function.Bijective (· • g : F → G)) :
    basisMap (pairBasis g Z) <$> (pairSample : ProbComp (Fin 2 → F)) =ᵈ
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
    basisMap (fun _ : Unit => g) <$> (scalarSample : ProbComp (Unit → F)) =ᵈ
      ($ᵗ G : ProbComp G) := by
  simpa [scalarSample, basisMap] using
    SampleableType.map_uniformSample_evalDistEq_of_bijective hg

/-- Forward explained requests to the plain game while retaining explanations in the result. -/
@[expose] def interactionProgram
    (p : OracleComp (explainedSpec F (fun _ : Unit => G) Label (fun _ => Unit)) α) :
    OracleComp (gameSpec Label G) α :=
  simulateQ (fun q => (gameSpec Label G).query q.value) p

/-- Run an explained computation against the programmed oracle and retain its coefficient log. -/
@[expose] def runProgram [DecidableEq Label] [CommSemiring F] [AddCommMonoid G]
    [Module F G] [Fintype κ] (B : κ → G) (sample : Label → ProbComp (κ → F))
    (p : OracleComp (explainedSpec F (fun _ : Unit => G) Label (fun _ => Unit)) α)
    (st : State Label (κ → F)) : ProbComp (α × State Label (κ → F)) :=
  (simulateQ (programmed B sample) (interactionProgram p)).run st

private theorem runProgram_pure [DecidableEq Label] [CommSemiring F] [AddCommMonoid G]
    [Module F G] [Fintype κ] (B : κ → G) (sample : Label → ProbComp (κ → F))
    (a : α) (st : State Label (κ → F)) : runProgram B sample (pure a) st = pure (a, st) := by
  simp [runProgram, interactionProgram]

private theorem runProgram_query [DecidableEq Label] [CommSemiring F] [AddCommMonoid G]
    [Module F G] [Fintype κ] (B : κ → G) (sample : Label → ProbComp (κ → F))
    (q : Explained F Label (fun _ : Unit => G))
    (next : Message Unit (fun _ : Unit => G) →
      OracleComp (explainedSpec F (fun _ : Unit => G) Label (fun _ => Unit)) α)
    (st : State Label (κ → F)) :
    runProgram B sample (liftM ((explainedSpec F (fun _ : Unit => G) Label
      (fun _ => Unit)).query q) >>= next) st =
      (oracle (basisMap B) sample q.value.data).run st >>= fun z =>
        runProgram B sample (next (reply z.1)) z.2 := by
  simp [runProgram, interactionProgram, programmed, game, bind_map_left]

private theorem oracle_receipts [DecidableEq Label] (decode : (κ → F) → G)
    (sample : Label → ProbComp (κ → F)) (l : Label) (st : State Label (κ → F))
    (z : G × State Label (κ → F)) (hz : z ∈ support ((oracle decode sample l).run st)) :
    z.2.2.map decode = st.2.map decode ++ [z.1] := by
  rw [oracle_apply] at hz
  cases hc : st.1 l with
  | some c => simp only [hc, support_pure, Set.mem_singleton_iff] at hz; subst z; simp
  | none =>
    simp only [hc, support_map, Set.mem_image] at hz
    obtain ⟨c, _, rfl⟩ := hz
    simp

/-- A certified computation's final explanation is valid over the actual recorded coefficient
rows. Initial rows may represent fixed inputs in an enlarged basis. -/
theorem runProgram_valid [DecidableEq Label] [CommSemiring F] [AddCommMonoid G]
    [Module F G] [Fintype κ] (B : κ → G) (sample : Label → ProbComp (κ → F))
    (p : OracleComp (explainedSpec F (fun _ : Unit => G) Label (fun _ => Unit))
      (Explained F Data (fun _ : Unit => G))) (st : State Label (κ → F))
    (hp : IsAlgebraic (fun _ => st.2.map (basisMap B)) p)
    (z : Explained F Data (fun _ : Unit => G) × State Label (κ → F))
    (hz : z ∈ support (runProgram B sample p st)) :
    z.1.Valid (fun _ => z.2.2.map (basisMap B)) := by
  induction p using OracleComp.inductionOn generalizing st z with
  | pure out =>
    rw [runProgram_pure, support_pure, Set.mem_singleton_iff] at hz
    subst z
    exact hp
  | query_bind q next ih =>
    rw [runProgram_query, mem_support_bind_iff] at hz
    obtain ⟨w, hw, hz⟩ := hz
    apply ih (reply w.1) w.2 _ z hz
    have hn := ((isAlgebraic_query (Reply := fun _ => Unit)
      (fun _ => st.2.map (basisMap B)) q next).mp hp).2 (reply w.1)
    change IsAlgebraic (fun _ => st.2.map (basisMap B) ++ [w.1]) (next (reply w.1)) at hn
    rwa [oracle_receipts (basisMap B) sample q.value.data st w hw]

/-- Transport all final outputs of a certified programmed run to the reduction's basis. -/
theorem runProgram_transport [DecidableEq Label] [CommSemiring F] [AddCommMonoid G]
    [Module F G] [Fintype κ] (B : κ → G) (sample : Label → ProbComp (κ → F))
    (p : OracleComp (explainedSpec F (fun _ : Unit => G) Label (fun _ => Unit))
      (Explained F Data (fun _ : Unit => G))) (st : State Label (κ → F))
    (hp : IsAlgebraic (fun _ => st.2.map (basisMap B)) p)
    (z : Explained F Data (fun _ : Unit => G) × State Label (κ → F))
    (hz : z ∈ support (runProgram B sample p st)) :
    (transportExplained (fun _ => z.2.2) z.1 ()).map (basisMap B) = z.1.value.groups () :=
  transportExplained_evaluate (fun _ => B) (fun _ => z.2.2) z.1
    (runProgram_valid B sample p st hp z hz) ()

end GroupModel.HashToGroup
