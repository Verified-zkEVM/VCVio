/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import ToMathlib.Combinatorics.MonotoneStructure
public import VCVio.CryptoFoundations.CoordinateFork.Extraction

/-!
# Non-vacuity of coordinate-wise special soundness

`SigmaProtocol.CoordSpeciallySoundAt` universally quantifies over a set of transcripts that is
simultaneously accepting and coordinate-wise `k`-special sound. If no such set could exist the
definition would hold of every extractor for uninteresting reasons, so `docs/agents/gotchas.md` §14
asks for a kernel-checked witness.

This file supplies one at `ι = Fin 2`, `S = Fin 3`, `k = 2` against a toy Σ-protocol whose verifier
is *not* constantly accepting: it accepts a response exactly when the response is the statement.
The witness set is a `coordFamily`, whose special soundness is checked by `decide`.
-/

@[expose] public section

open Finset CoordinateWise OracleComp OracleComp.EvalDist SigmaProtocol

open scoped ENNReal

namespace VCVioTest.Forking

/-- Challenge vectors of length two over a three-element alphabet. -/
abbrev SChal : Type := Fin 2 → Fin 3

/-- A toy Σ-protocol on challenge vectors. Statements, witnesses and responses are all `Fin 3`; the
relation is equality, and the verifier accepts exactly when the response equals the statement. The
verifier is deliberately not constantly `true`, so an accepting transcript carries information. -/
def toySigma : SigmaProtocol (Fin 3) (Fin 3) Unit Unit SChal (Fin 3) (fun x w => x == w) where
  commit _ _ := pure ((), ())
  respond _ w _ _ := pure w
  verify x _ _ resp := resp == x
  sim _ := pure ()
  extract _ r₁ _ _ := pure r₁

/-- The toy extractor: return the response of any one transcript it is handed. It accepts the
statement explicitly, matching the paper's extractor interface, but does not need to inspect it. -/
noncomputable def toyExt : Fin 3 → Unit → Finset (SChal × Fin 3) → ProbComp (Fin 3) :=
  fun _ _ T => pure ((T.toList.head?).elim 0 Prod.snd)

/-- The toy verifier rejects some transcripts, so accepting is a real constraint. -/
example : toySigma.verify 0 () 0 1 = false := by decide

/-- **Non-vacuity, conclusion side.** The toy protocol is coordinate-wise `2`-special sound: any
transcript set whose challenges are `SS(Fin 3, 2, 2)` is nonempty, and every accepting transcript
pins the response to the statement. -/
theorem toySigma_coordSpeciallySoundAt (x : Fin 3) :
    toySigma.CoordSpeciallySoundAt 2 toyExt x := by
  intro pc T hacc hss w hw
  obtain ⟨⟨e, heX, -⟩, -⟩ := hss
  obtain ⟨p, hpT, -⟩ := Finset.mem_image.mp heX
  simp only [toyExt, support_pure, Set.mem_singleton_iff] at hw
  cases hh : T.toList.head? with
  | none =>
      rw [List.head?_eq_none_iff, Finset.toList_eq_nil] at hh
      exact absurd (hh ▸ hpT) (Finset.notMem_empty p)
  | some q =>
      have hq : q ∈ T := Finset.mem_toList.mp (List.mem_of_mem_head? hh)
      have hv := hacc q hq
      simp only [toySigma, beq_iff_eq] at hv
      rw [hh] at hw
      simp [hw, hv]

/-- The centre of the witness challenge set. -/
def centre : SChal := ![0, 0]

/-- One replacement per coordinate, giving `ℓ * (k - 1) + 1 = 3` challenges in all. -/
def replacements : Fin 2 → Finset (Fin 3) := fun _ => {1}

example : ∀ j, centre j ∉ replacements j := by decide

example : ∀ j, (replacements j).card = 2 - 1 := by decide

/-- **Non-vacuity, hypothesis side.** A concrete accepting transcript set whose challenges form an
`SS(Fin 3, 2, 2)` set exists, so the premises of `CoordSpeciallySoundAt` are jointly satisfiable
and the theorem above is not about an empty quantifier. -/
theorem exists_accepting_toySigma (x : Fin 3) :
    ∃ T : Finset (SChal × Fin 3), (∀ p ∈ T, toySigma.verify x () p.1 p.2 = true) ∧
      IsCoordSpecialSound 2 (T.image Prod.fst) :=
  exists_accepting_isCoordSpecialSound toySigma () centre replacements (by decide) (by decide)
    (fun _ => x) fun _ _ => by simp [toySigma]

/-! ## The composite extractor -/

/-- The honest-looking prover that always answers with the statement, so every challenge accepts. -/
def toyProver (x : Fin 3) : ProbComp (SChal → Fin 3) := pure fun _ => x

theorem acceptTable_toyProver (x : Fin 3) :
    acceptTable (toySigma.verify x ()) (toyProver x) = pure fun _ => true := by
  simp [acceptTable, toyProver, toySigma]

private theorem one_sub_two_thirds : (1 : ℝ≥0∞) - 2 / 3 = 1 / 3 := by
  refine ENNReal.sub_eq_of_eq_add (by finiteness) ?_
  rw [ENNReal.div_add_div_same, show (1 : ℝ≥0∞) + 2 = 3 by norm_num,
    ENNReal.div_self (by simp) (by finiteness)]

/-- **Non-vacuity of the fixed-statement extraction bound.** Against the always-accepting prover,
the composite returns a valid witness with probability at least `1 - 2/3 = 1/3`, so the table-model
loss `ℓ(k-1)/|S| = 2/3` leaves real slack at these parameters. -/
theorem one_third_le_probEvent_extracted (x : Fin 3) :
    (1 : ℝ≥0∞) / 3 ≤ Pr[Extracted (fun x w => x == w) x |
      toySigma.coordExtract 2 toyExt x () (toyProver x)] := by
  have h := sub_div_le_probEvent_extracted_coordExtract toySigma 2 toyExt x
    (toySigma_coordSpeciallySoundAt x) () (toyProver x)
  refine le_trans (le_of_eq ?_) h
  rw [acceptTable_toyProver, acceptRatio_pure_const_true,
    show (Fintype.card (Fin 2) : ℝ≥0∞) * (2 - 1 : ℕ) / Fintype.card (Fin 3) = 2 / 3 from by simp,
    one_sub_two_thirds]

/-! ## A deliberately wrong extractor -/

/-- An extractor that always returns zero, ignoring both the statement and the transcripts. -/
def badToyExt : Fin 3 → Unit → Finset (SChal × Fin 3) → ProbComp (Fin 3) :=
  fun _ _ _ => pure 0

/-- **Negative control.** The non-vacuous transcript hypotheses reject a bad extractor: at
statement `1`, always returning witness `0` violates the relation. -/
theorem not_toySigma_coordSpeciallySoundAt_bad :
    ¬ toySigma.CoordSpeciallySoundAt 2 badToyExt 1 := by
  rintro hbad
  obtain ⟨T, hacc, hss⟩ := exists_accepting_toySigma 1
  have hw : (0 : Fin 3) ∈ support (badToyExt 1 () T) := by simp [badToyExt]
  have := hbad () T hacc hss 0 hw
  simp at this

/-! ## The generic structure's `t`-value -/

/-- **Non-vacuity of the §7.3 combinatorial bound.** At `ℓ = 2`, `|S| = 3`, the relevant monotone
structure's `t`-value is at least `3 ^ 1 + 1 = 4`. This checks only the structural lower bound; it
does not assert a runtime lower bound for the generic extractor. -/
theorem four_le_tValue :
    4 ≤ tValue (coordStructure 2) (∅ : Finset SChal) := by
  have h := pow_add_one_le_tValue (ι := Fin 2) (S := Fin 3)
  simpa using h

end VCVioTest.Forking
