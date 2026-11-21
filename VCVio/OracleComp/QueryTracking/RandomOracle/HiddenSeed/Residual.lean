/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/
module

public import VCVio.OracleComp.QueryTracking.RandomOracle.HiddenSeed

/-!
# Local tables for auxiliary queries and residual private keys

Keep selected private keys available to the outer game.
Sample each other private key and each auxiliary query once in a separate local table.
-/

public section
open OracleSpec OracleComp
open scoped OracleSpec.PrimitiveQuery
namespace SecretEncoding.Residual

variable {I J X Z R : Type} (pub : OracleSpec I) (aux : OracleSpec J)

/-- The local caches hold answers to auxiliary queries and keys indexed by `Z`. -/
abbrev Local (Z R : Type) := aux.QueryCache × (Z →ₒ R).QueryCache

/-- The original game caches both public oracles and private keys indexed by `X ⊕ Z`. -/
abbrev Source (X Z R : Type) := SplitCache (pub + aux) (X ⊕ Z) R

/-- Select the external public cache and the retained private labels. -/
@[expose] def baseState (s : Source pub aux X Z R) : SplitCache pub X R :=
  (s.1.fst, .ofFn fun x => s.2 (.inl x))

/-- Preserve all auxiliary entries and the complementary private keys. -/
@[expose] def localState (s : Source pub aux X Z R) : Local aux Z R :=
  (s.1.snd, .ofFn fun z => s.2 (.inr z))

variable (X Z R) [DecidableEq I] [DecidableEq J] [DecidableEq X] [DecidableEq Z]
  [∀ i, SampleableType (pub.Range i)] [∀ j, SampleableType (aux.Range j)] [SampleableType R]

/-- An auxiliary or residual query performs its own cached random draw.
Only uniform sampling, ordinary public queries and selected private keys reach the outer game. -/
@[expose] noncomputable def handler : QueryImpl ((pub + aux).withDerivations (X ⊕ Z) R)
    (StateT (Local aux Z R) (OracleComp (pub.withDerivations X R)))
  | .inl (.inl n) => liftM (liftM ((pub.withDerivations X R).query (.inl (.inl n))) :
      OracleComp (pub.withDerivations X R) _)
  | .inl (.inr (.inl i)) => liftM (liftM ((pub.withDerivations X R).query (.inl (.inr i))) :
      OracleComp (pub.withDerivations X R) _)
  | .inl (.inr (.inr j)) => StateT.mk fun s =>
      (fun z => (z.1, (z.2, s.2))) <$>
        (liftM ((aux.randomOracle j).run s.1) : OracleComp (pub.withDerivations X R) _)
  | .inr (.inl x) => liftM (liftM ((pub.withDerivations X R).query (.inr x)) :
      OracleComp (pub.withDerivations X R) _)
  | .inr (.inr z) => StateT.mk fun s =>
      (fun w => (w.1, (s.1, w.2))) <$>
        (liftM (((Z →ₒ R).randomOracle z).run s.2) : OracleComp (pub.withDerivations X R) _)

private theorem step (t : ((pub + aux).withDerivations (X ⊕ Z) R).Domain)
    (s : Source pub aux X Z R) :
    (simulateQ (idealImpl pub X R)
      ((handler (pub := pub) (aux := aux) (X := X) (Z := Z) (R := R) t).run
        (localState pub aux s))).run (baseState pub aux s) =
    (fun w => ((w.1, localState pub aux w.2), baseState pub aux w.2)) <$>
      (idealImpl (pub + aux) (X ⊕ Z) R t).run s := by
  rcases t with ((n | (i | j)) | (x | z))
  · simp [handler, idealImpl, Functor.map_map]
  · cases h : s.1 (.inl i) with
    | some u => simp [handler, idealImpl, baseState, localState, h]
    | none =>
      suffices store : ∀ u : pub.Range i,
          (s.1.cacheQuery (.inl i) u).snd = s.1.snd ∧
          (s.1.cacheQuery (.inl i) u).fst = s.1.fst.cacheQuery i u by
        simp [handler, idealImpl, baseState, localState, h,
          Functor.map_map, fun u => (store u).1, fun u => (store u).2]
      intro u
      constructor
      · ext k
        simp
      · ext k
        by_cases hk : k = i
        · subst k
          simp
        · simp [hk]
  · cases h : s.1 (.inr j) with
    | some u => simp [handler, idealImpl, baseState, localState, h]
    | none =>
      suffices store : ∀ u : aux.Range j,
          (s.1.cacheQuery (.inr j) u).fst = s.1.fst ∧
          (s.1.cacheQuery (.inr j) u).snd = s.1.snd.cacheQuery j u by
        simp [handler, idealImpl, run_simulateQ_idealImpl_liftM, baseState, localState, h,
          Functor.map_map, fun u => (store u).1, fun u => (store u).2]
      intro u
      constructor
      · ext k
        simp
      · ext k
        by_cases hk : k = j
        · subst k
          simp
        · simp [hk]
  · cases h : s.2 (.inl x) with
    | some u => simp [handler, idealImpl, baseState, localState, h]
    | none =>
      suffices store : ∀ u : R,
          (QueryCache.ofFn (fun k => (s.2.cacheQuery (.inl x) u) (.inl k)) :
            (X →ₒ R).QueryCache) = (baseState pub aux s).2.cacheQuery x u by
        simp [handler, idealImpl, baseState, localState, h,
          Functor.map_map, store]
      intro u
      ext k
      by_cases hk : k = x
      · subst k
        simp
      · simp [hk, baseState]
  · cases h : s.2 (.inr z) with
    | some u => simp [handler, idealImpl, baseState, localState, h]
    | none =>
      suffices store : ∀ u : R,
          (QueryCache.ofFn (fun k => (s.2.cacheQuery (.inr z) u) (.inr k)) :
            (Z →ₒ R).QueryCache) = (localState pub aux s).2.cacheQuery z u by
        simp [handler, idealImpl, run_simulateQ_idealImpl_liftM, baseState, localState, h,
          Functor.map_map, store]
      intro u
      ext k
      by_cases hk : k = z
      · subst k
        simp
      · simp [hk, localState]

/-- Localizing the two residual tables preserves the actual return value and all four final tables.
The equality holds for adaptive programs and arbitrary warm initial caches. -/
theorem run {α : Type} (body : OracleComp ((pub + aux).withDerivations (X ⊕ Z) R) α)
    (s : Source pub aux X Z R) :
    (simulateQ (idealImpl pub X R)
      ((simulateQ (handler (pub := pub) (aux := aux) (X := X) (Z := Z) (R := R)) body).run
        (localState pub aux s))).run
        (baseState pub aux s) =
    (fun w => ((w.1, localState pub aux w.2), baseState pub aux w.2)) <$>
      (simulateQ (idealImpl (pub + aux) (X ⊕ Z) R) body).run s := by
  induction body using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rw [step]
    simp only [bind_map_left]
    exact bind_congr fun w => ih w.1 w.2

end SecretEncoding.Residual
