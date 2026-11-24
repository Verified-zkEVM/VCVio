/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.CoordinateFork.Operational
public import VCVio.CryptoFoundations.Rewinding.FinderBridge
public import VCVio.CryptoFoundations.Rewinding.ThresholdSemantics

/-!
# Figure 11 of Fenzi–Moghaddas–Nguyen as a black-box finder

`coordFinder k` asks a Boolean acceptance oracle about complete challenge vectors `ι → S`: it
draws a challenge, asks whether it accepts, and on acceptance collects `k - 1` further accepting
neighbours in every coordinate, drawing each coordinate's replacement values without replacement.
Every oracle call is charged, including the rejected ones.
-/

public section

open Finset CoordinateWise OracleComp OracleSpec ProbComp
open scoped ENNReal

namespace Rewinding

/-- Running a finite sequence of programs against a fixed acceptance function adds up their
counters: each member runs from the counter its predecessors leave, and its law does not depend on
that starting value except through the offset (`Rewinding.counted_run_add`). -/
theorem counted_mOfFn {Q α β : Type} (f : Q → α) :
    ∀ {n : ℕ} (g : Fin n → OracleComp (unifSpec + rerunSpec Q α) β) (count : ℕ),
      (simulateQ (coins (S := ℕ) + counted f) (Fin.mOfFn n g)).run count =
        (fun v : Fin n → β × ℕ => (fun i => (v i).1, count + ∑ i, (v i).2)) <$>
          Fin.mOfFn n fun i => (simulateQ (coins (S := ℕ) + counted f) (g i)).run 0
  | 0, g, count => by
      simp only [Fin.mOfFn, simulateQ_pure, StateT.run_pure, map_pure, Finset.univ_eq_empty,
        Finset.sum_empty, add_zero]
      congr 2
      funext i
      exact i.elim0
  | n + 1, g, count => by
      have hrest := fun c => counted_mOfFn f (fun i : Fin n => g i.succ) c
      simp only [Fin.mOfFn, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
        map_bind]
      rw [show count = 0 + count from (zero_add count).symm, counted_run_add, zero_add,
        bind_map_left]
      refine bind_congr fun p => ?_
      simp only [hrest, bind_map_left, map_pure]
      refine bind_congr fun v => ?_
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      congr 2
      · funext i
        refine Fin.cases rfl (fun _ => rfl) i
      · ring

/-- `Rewinding.counted_mOfFn` over a finite index type. -/
theorem counted_mPi {Q α β : Type} (f : Q → α) {ι : Type} [Fintype ι]
    (g : ι → OracleComp (unifSpec + rerunSpec Q α) β) (count : ℕ) :
    (simulateQ (coins (S := ℕ) + counted f) (Fintype.mPi g)).run count =
      (fun v : ι → β × ℕ => (fun i => (v i).1, count + ∑ i, (v i).2)) <$>
        Fintype.mPi fun i => (simulateQ (coins (S := ℕ) + counted f) (g i)).run 0 := by
  simp only [Fintype.mPi, simulateQ_map, StateT.run_map, counted_mOfFn, Functor.map_map]
  congr 1
  funext v
  simp only [Equiv.arrowCongr_apply, Equiv.refl_apply, Function.comp_apply, Prod.mk.injEq]
  refine ⟨rfl, ?_⟩
  congr 1
  rw [Equiv.symm_symm]
  exact (Equiv.sum_comp (Fintype.equivFin ι) fun k => (v k).2).symm

end Rewinding

namespace OracleComp

variable {ι S : Type} [DecidableEq ι] [Fintype ι] [DecidableEq S] [Fintype S]

/-- The coordinate-`j` neighbours of `c₀`: the challenges that replace `c₀ j` by another value. -/
@[expose] noncomputable def neighbourPool (c₀ : ι → S) (j : ι) : List (ι → S) :=
  (altPool c₀ j).map (Function.update c₀ j)

/-- Ask the acceptance oracle about coordinate-`j` neighbours of `c₀`, drawn without replacement,
until `k - 1` of them accept or they run out, and return the accepting ones. -/
@[expose] noncomputable def coordNeighbours (k : ℕ) (c₀ : ι → S) (j : ι) :
    OracleComp (unifSpec + Rewinding.accSpec (fun _ : ι => S)) (List (ι → S)) :=
  Rewinding.collectChildren (fun n => (unifSpec.query n)) Rewinding.acceptanceChild (k - 1)
    (neighbourPool c₀ j)

/-- **Figure 11 of Fenzi–Moghaddas–Nguyen as a black-box finder.** Draw a challenge `c₀` and ask
the acceptance oracle about it. On acceptance, collect `k - 1` accepting coordinate-`j` neighbours
of `c₀` for every `j`, and return the coordinate-wise special sound set they form with `c₀` if
every coordinate supplied them. -/
@[expose] noncomputable def coordFinder [SampleableType (ι → S)] (k : ℕ) :
    OracleComp (unifSpec + Rewinding.accSpec (fun _ : ι => S)) (Option (Finset (ι → S))) := do
  let c₀ ← OracleComp.liftComp ($ᵗ (ι → S)) (unifSpec + Rewinding.accSpec (fun _ : ι => S))
  let b ← (Rewinding.accSpec (fun _ : ι => S)).query c₀
  if b then do
    let d ← Fintype.mPi (coordNeighbours k c₀)
    let A : ι → Finset S := fun j => ((d j).map (· j)).toFinset
    pure (if ∀ j, (A j).card = k - 1 then some (coordFamily c₀ A) else none)
  else pure none

omit [Fintype ι] [Fintype S] in
/-- The accepting neighbours collected from a run of draws, read back in coordinate `j`, are the
accepting values that run drew. -/
theorem toFinset_map_filter_neighbours (ρ : (ι → S) → Bool) (c₀ : ι → S) (j : ι) (l : List S) :
    (((l.map (Function.update c₀ j)).filter ρ).map (· j)).toFinset =
      collected ρ c₀ (fun _ => l) j := by
  simp only [collected, List.filter_map, List.map_map]
  congr 1
  conv_rhs => rw [← List.map_id (List.filter _ l)]
  refine List.map_congr_left fun x _ => ?_
  simp

/-- Against a fixed acceptance function, the finder's output and its count of acceptance-oracle
calls have exactly the law of `coordForkOp`: the table loop's lookups are the finder's oracle
calls. -/
theorem runFinder_coordFinder [SampleableType (ι → S)] (k : ℕ) (ρ : (ι → S) → Bool) :
    Rewinding.runFinder (coordFinder k) ρ = coordForkOp k ρ := by
  have hcol : ∀ j c₀, (simulateQ (Rewinding.coins (S := ℕ) + Rewinding.counted ρ)
      (coordNeighbours k c₀ j)).run 0 =
        (fun d : List S => ((d.map (Function.update c₀ j)).filter ρ, d.length)) <$>
          coordDraws k ρ c₀ j := by
    intro j c₀
    rw [coordNeighbours, Rewinding.collectChildren_counted ρ _ (k - 1) _ rfl 0, neighbourPool,
      ProbComp.drawUntil_map _ _ _ _ _ rfl, Functor.map_map]
    simp [coordDraws, Function.comp_def]
  have hcoins : ∀ {α : Type} (oa : ProbComp α) (s : ℕ),
      (simulateQ (Rewinding.coins (S := ℕ)) oa).run s = (·, s) <$> oa := by
    intro α oa s
    simp [Rewinding.coins, simulateQ_liftTarget]
  simp only [Rewinding.runFinder, coordFinder, coordForkOp, simulateQ_bind, StateT.run_bind,
    QueryImpl.simulateQ_add_liftComp_left, hcoins, bind_map_left]
  refine bind_congr fun c₀ => ?_
  simp only [QueryImpl.simulateQ_add_liftM_query_right, Rewinding.counted, StateT.run_bind,
    StateT.run_modify, StateT.run_pure, pure_bind, zero_add]
  cases hacc : ρ c₀ with
  | false => simp [coordForkOpAt, hacc]
  | true =>
      simp only [ite_true, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
        Rewinding.counted_mPi, hcol, ← Fintype.mPi_map, bind_map_left, Functor.map_map,
        coordForkOpAt, hacc, ite_true]
      refine bind_congr fun d => ?_
      have hc : ∀ j, collected ρ c₀ (fun _ => d j) j = collected ρ c₀ d j := fun _ => rfl
      simp only [toFinset_map_filter_neighbours, hc]
      by_cases h : ∀ j, #(collected ρ c₀ d j) = k - 1
      · simp only [h, implies_true, ↓reduceIte]
      · simp only [h, ↓reduceIte]

/-- **Figure 11 of Fenzi–Moghaddas–Nguyen meets the black-box finder contract**, at error
`κ = ℓ (k - 1) / N` and at most `1 + ℓ (k - 1)` acceptance-oracle calls in expectation, where
`ℓ = Fintype.card ι` and `N = Fintype.card S`. Every returned set is coordinate-wise `k`-special
sound and accepting.

The success field is the affine form `ε ≤ κ + (1 - κ) p`
(`CoordinateWise.div_card_filter_le_affine`), so `Rewinding.ResetPolicy.finder_bounds` carries the
success and cost guarantees to frozen reruns of a prover. The threshold finder
(`Rewinding.isTreeFinder_thresholdFinder`) has the smaller error `1 - (1 - (k - 1) / N) ^ ℓ` on
`ℓ` rounds, at the cost of `k ^ ℓ` runs. -/
theorem isFinder_coordFinder [SampleableType (ι → S)] [Nonempty S] (k : ℕ) :
    Rewinding.IsFinder (fun ρ X => IsCoordSpecialSound k X ∧ ∀ c ∈ X, ρ c = true)
      (coordFinder (ι := ι) (S := S) k)
      ((Fintype.card ι : ℝ≥0∞) * (k - 1 : ℕ) / Fintype.card S)
      (1 + Fintype.card ι * (k - 1 : ℕ)) where
  sound ρ z hz X hX := by
    rw [runFinder_coordFinder] at hz
    obtain ⟨o, n⟩ := z
    obtain rfl : o = some X := hX
    exact coordForkOp_success hz
  success ρ := by
    rw [runFinder_coordFinder, prEvent_isSome_coordForkOp]
    exact CoordinateWise.div_card_filter_le_affine (accept := fun c => ρ c = true) k
  cost ρ := by
    rw [Rewinding.expectedCalls_eq_lintegral_counter, runFinder_coordFinder]
    exact lintegral_cost_coordForkOp_le k ρ

end OracleComp
