/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Auxiliary.ChainWitnesses
public import HashSig.GXMSS.Security.Auxiliary.ChainSelection
public import HashSigTest.GXMSS.MerkleWitnesses
import all HashSig.GXMSS.Chain

/-!
# GXMSS chain witness and selector controls

The admitted order-sensitive hash exercises positive-step merge/cut witnesses. Selector controls
separate the pointwise nonmaximum-output premise from the stronger two-codeword corollary.
Private chain bodies are used only by concrete implementation controls.
-/

public section
namespace GXMSS.ChainFoundationProbe
open GXMSS.MerkleWitnessProbe GXMSS.Reductions IncomparableEncoding

/-- Two starts merge at paper position three, whose finite tweak coordinate is two. -/
theorem aligned : (witnessInstance 3 3).findChainCollision () 5 0 2 3 8 9 = some 0 := by decide

/-- The designated value is reached at position two from predecessor four. -/
theorem cut_preimage :
    (witnessInstance 3 3).findChainCut () 5 0 0 2 3 4 6 = some (.inl 4) := by decide

/-- At cut two, values four and five merge strictly after the cut, at position three. -/
theorem cut_collision :
    (witnessInstance 3 3).findChainCut () 5 0 0 2 3 4 10 = some (.inr 0) := by decide

/-- No predecessor offset exists in a zero-span merge search. -/
theorem zero_span : (witnessInstance 3 3).findChainCollision () 5 0 2 0 8 9 = none := by decide

/-- An endpoint cut retains its actual predecessor even with no remaining merge span. -/
theorem endpoint_cut :
    (witnessInstance 3 3).findChainCut () 5 0 0 2 2 4 6 = some (.inl 4) := by decide

/-- A single low digit has a nonmaximum coordinate. -/
@[expose] def lowWord : Codeword 1 2 := fun _ => 0

/-- A single highest digit has no final step after it. -/
@[expose] def highWord : Codeword 1 2 := fun _ => 1

/-- An incomparable singleton code may encode both messages to the same word. -/
@[expose] def singletonEncoding (word : Codeword 1 2) :
    IncomparableEncoding Unit Bool Unit (Fin 1) 1 2 where
  code := {word}
  incomparable := by
    intro x hx y hy hne
    exact (hne ((Set.mem_singleton_iff.mp hx).trans
      (Set.mem_singleton_iff.mp hy).symm)).elim
  encode _ _ _ _ := some ⟨word, by simp⟩

/-- The pointwise core premise holds without a second codeword. -/
theorem low_nonmaximum : (singletonEncoding lowWord).NoMaximumOutput := by
  intro pp msg randomizer ep word hw
  change some lowWord = some word at hw
  cases Option.some.inj hw
  exact ⟨0, by decide⟩

/-- This successful singleton encoder cannot satisfy the two-distinct-codewords premise. -/
theorem low_not_two : ¬ ∃ x y : Codeword 1 2,
    x ∈ (singletonEncoding lowWord).code ∧ y ∈ (singletonEncoding lowWord).code ∧ x ≠ y := by
  rintro ⟨x, y, hx, hy, hne⟩
  change x = lowWord at hx
  change y = lowWord at hy
  exact hne (hx.trans hy.symm)

/-- The actual GXMSS selector applies the weaker admitted encoding premise. -/
theorem singleton_selected :
    (findNonMaximumCoordinate (w := 1) lowWord).isSome :=
  findNonMaximumCoordinate_isSome (h := 0) (w := 1) (v := 1)
    (singletonEncoding lowWord) low_nonmaximum
    () false () 0 lowWord rfl

/-- Incomparability of a singleton maximum word does not establish the pointwise premise. -/
theorem high_not_nonmaximum : ¬ (singletonEncoding highWord).NoMaximumOutput := by
  intro hnonmax
  obtain ⟨i, hi⟩ := hnonmax () false () 0 highWord rfl
  exact (Nat.lt_irrefl 1) hi

/-- The first qualifying coordinate wins when more than one is available. -/
theorem first_coordinate :
    findNonMaximumCoordinate (w := 2) ![2, 1] = some 0 := by decide

/-- A leading maximum digit is skipped without changing the later index. -/
theorem later_coordinate :
    findNonMaximumCoordinate (w := 2) ![3, 2] = some 1 := by decide

/-- An all-maximum word has no invented index. -/
theorem no_coordinate : findNonMaximumCoordinate (w := 2) ![3, 3] = none := by decide

/-- An empty vector never creates a coordinate. -/
theorem empty_coordinate :
    findNonMaximumCoordinate (w := 1) (v := 0) Fin.elim0 = none := by decide

/-- Seven positive positions per epoch give the sharp finite selector count. -/
theorem exact_guess_count : Fintype.card (Guess 3 3 1) = 56 := by
  rw [guess_cardinality]
  decide

/-- A zero chain count is an empty selector domain, with no sampler asserted. -/
theorem empty_guess : Fintype.card (Guess 3 3 0) = 0 := by
  rw [guess_cardinality]
  decide

/-- Zero digit bits leave no positive chain position. -/
theorem zero_bits_guess : Fintype.card (Guess 3 0 1) = 0 := by
  rw [guess_cardinality]
  decide

end GXMSS.ChainFoundationProbe
