/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.ToExplained
public import VCVio.CryptoFoundations.GroupModel.OfExplained

/-!
Exact round trips between handles and certified explanations

The translations preserve output values and all ambient monadic effects when decoding
is a left inverse of encoding. The internal tables and coefficient vectors may differ.
-/

public section

open OracleComp OracleSpec

namespace GroupModel

open Interaction

variable {S F Input Query Result : Type} {G E : S → Type} {Reply : Query → Type}
    [CommSemiring F] [Fintype S] [DecidableEq S]
    [∀ s, AddCommMonoid (G s)] [∀ s, Module F (G s)] [∀ s, DecidableEq (G s)]
    {N : Type → Type} [Monad N] [LawfulMonad N]

/-- Compiling and explaining a certified adversary preserves its output values and effects. -/
theorem toExplained_ofExplained_run
    (B : Interaction.Adversary F G Input (CoinQuery Query) (CoinReply Reply) Result)
    (M : Model F (discreteSig S) G) (enc : (s : S) → G s → E s)
    (dec : (s : S) → E s → G s) (hdec : ∀ s g, dec s (enc s g) = g)
    (random : QueryImpl unifSpec N) (game : QueryImpl (plainSpec G Query Reply) N)
    (input : Message Input G) :
    (fun z => z.1.value) <$>
        (toExplained (ofExplained B dec) enc).run (withCoins random game) input =
      (fun z => z.1.value) <$> B.run (withCoins random game) input := by
  rw [toExplained_run (M := M), ofExplained_run M enc random game B dec hdec]

/-- Explaining and compiling a handle adversary preserves its final read-back values and effects. -/
theorem ofExplained_toExplained_run
    (A : HandleAdversary F (discreteSig S) E Input Query Reply Result)
    (M : Model F (discreteSig S) G) (enc : (s : S) → G s → E s)
    (dec : (s : S) → E s → G s) (hdec : ∀ s g, dec s (enc s g) = g)
    (random : QueryImpl unifSpec N) (game : QueryImpl (plainSpec G Query Reply) N)
    (input : Message Input G) :
    (fun z => lookupMessage z.2 z.1) <$>
        (ofExplained (toExplained A enc) dec).run M enc random game input =
      (fun z => lookupMessage z.2 z.1) <$> A.run M enc random game input := by
  rw [ofExplained_run M enc random game _ dec hdec, toExplained_run A M]

end GroupModel
