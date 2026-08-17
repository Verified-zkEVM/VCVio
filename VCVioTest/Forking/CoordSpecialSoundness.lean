/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.CryptoFoundations.CoordinateFork.SpecialSoundness

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

open Finset CoordinateWise OracleComp SigmaProtocol

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

/-- The toy extractor: return the response of any one transcript it is handed. -/
noncomputable def toyExt : Unit → Finset (SChal × Fin 3) → ProbComp (Fin 3) :=
  fun _ T => pure ((T.toList.head?).elim 0 Prod.snd)

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

end VCVioTest.Forking
