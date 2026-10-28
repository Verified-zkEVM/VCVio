/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Chain
import all HashSig.GXMSS.Chain

/-!
# Chain indexing examples

The paper loop with start two and length three visits positions three, four and five.
These tests retain the ordered call trace, so a shifted recurrence cannot pass by coincidence.
-/

public section

namespace GXMSS.ChainProbe

/-- The three visited positive positions for `w=3`, start two and length three. -/
theorem positions_at_three : chainWith (fun j xs => xs ++ [j]) 2 3 [] = [3, 4, 5] := rfl

/-- The full chain for `w=3` visits all seven positive positions in order. -/
theorem positions_full : chainWith (fun j xs => xs ++ [j]) 0 7 [] = [1, 2, 3, 4, 5, 6, 7] := rfl

/-- Splitting at digit three leaves the unshifted digit as the second start position. -/
theorem positions_split :
    chainWith (fun j xs => xs ++ [j]) 3 4
      (chainWith (fun j xs => xs ++ [j]) 0 3 []) = [1, 2, 3, 4, 5, 6, 7] := rfl

/-- With zero available positions, a chain of length zero makes no hash calls. -/
theorem positions_zero : chainWith (fun j xs => xs ++ [j]) 0 0 [] = [] := rfl

/-- A trace digest preserves the ordered calls and input order. -/
abbrev TraceDigest := List ℕ

/-- Distinct tags distinguish the three input embeddings. -/
abbrev TraceInput := TraceDigest ⊕ ((TraceDigest × TraceDigest) ⊕ (Fin 1 → TraceDigest))

/-- Chain and tree tweak labels occupy distinct constructors. -/
abbrev TraceTweak := (ℕ × ℕ × ℕ) ⊕ (ℕ × ℕ)

/-- A common hash instance records finite-to-paper chain labels, tree addresses and input order.
The tags 1000, 2000 and 3000 mark chain, vector and pair hashing respectively. -/
@[expose] def traceInstance (h w : ℕ) :
    HashInstance Unit TraceTweak TraceInput TraceDigest h w 1 where
  thf := {
    seedGen := pure ()
    eval := fun _ t x => match t, x with
      | .inl (e, i, j), .inl xs => xs ++ [1000, e + 1, i + 1, j + 1]
      | .inr (z, i), .inr (.inl (l, r)) => l ++ r ++ [3000, z, i]
      | .inr (z, i), .inr (.inr xs) => xs 0 ++ [2000, z, i]
      | _, _ => [9999] }
  digestInput := ⟨Sum.inl, by intro a b hab; exact Sum.inl.inj hab⟩
  pairInput := ⟨fun x => .inr (.inl x), by intro a b hab; exact Sum.inl.inj (Sum.inr.inj hab)⟩
  vectorInput := ⟨fun x => .inr (.inr x), by intro a b hab; exact Sum.inr.inj (Sum.inr.inj hab)⟩
  chainTweak := ⟨fun (e, i, j) => .inl (e.val, i.val, j.val), by
    intro a b hab
    simpa only [Sum.inl.injEq, Prod.ext_iff, Fin.ext_iff] using hab⟩
  treeTweak := ⟨fun (z, i) => .inr (z.val, i.val), by
    intro a b hab
    simpa only [Sum.inr.injEq, Prod.ext_iff, Fin.ext_iff] using hab⟩
  chain_ne_tree := by
    intro c t heq
    cases c
    cases t
    cases heq

/-- The actual common-hash chain shifts epoch/chain labels but preserves positive step positions. -/
theorem adapter_positions :
    (traceInstance 3 3).chain () 2 0 2 3 [] =
      [1000, 3, 1, 3, 1000, 3, 1, 4, 1000, 3, 1, 5] := by decide

/-- With zero chain positions the actual adapter performs no calls. -/
theorem adapter_zero : (traceInstance 0 0).chain () 0 0 0 0 [] = [] := by decide

/-- The sole width-zero digit completes without an external bound or a hash call. -/
theorem digit_zero_width {PP T X H : Type} {h v : ℕ}
    (P : HashInstance PP T X H h 0 v) (pp : PP) (e : Fin (2 ^ h)) (i : Fin v)
    (digit : Fin (2 ^ 0)) (x : H) :
    P.chain pp e i digit (2 ^ 0 - 1 - digit.val) (P.chain pp e i 0 digit x) = x := by
  rw [P.chain_complete_digit]
  exact P.chain_zero pp e i 0 x

end GXMSS.ChainProbe
