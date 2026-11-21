/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/
module

public import VCVio.OracleComp.QueryTracking.RandomOracle.PairedValue
public import VCVio.OracleComp.QueryTracking.RandomOracle.HiddenSeed
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Paired public and private words in the ideal derivation game

Public and private words have independent caches and may use different key types.
The remaining public oracles keep their response types and complete cache.
-/
public section
open OracleSpec OracleComp
open scoped OracleSpec.PrimitiveQuery

namespace OracleComp.RandomOraclePairedValue
namespace Derivations

variable {A L X F H : Type} (aux : OracleSpec A) (e : F ≃ H × H)

/-- Draw uniform samples, query public words or the auxiliary oracle, or derive a private word at `X`. -/
abbrev World (L X V : Type) := ((L →ₒ V) + aux).withDerivations X V

/-- The state stores both public tables and the private derivation table. -/
abbrev Cache (L X V : Type) := SecretEncoding.SplitCache ((L →ₒ V) + aux) X V

/-- Read two distinct rows at the same physical key and reconstruct the full reply. -/
@[expose] def pair {D : Type} (k : D) : OracleComp ((D ⊕ D) →ₒ H) F := do
  let lo ← liftM (((D ⊕ D) →ₒ H).query (.inl k))
  let hi ← liftM (((D ⊕ D) →ₒ H).query (.inr k))
  return e.symm (lo, hi)

/-- Embed a single public-table lookup alongside the auxiliary and private oracles. -/
@[expose] def publicWord : QueryImpl (L →ₒ H) (OracleComp (World aux L X H)) :=
  fun k => liftM ((World aux L X H).query (.inl (.inr (.inl k))))

/-- Embed a single private-table lookup without exposing it to the public table. -/
@[expose] def privateWord : QueryImpl (X →ₒ H) (OracleComp (World aux L X H)) :=
  fun k => liftM ((World aux L X H).query (.inr k))

/-- Hashes stay public, derivations stay private, and every auxiliary query is forwarded once. -/
@[expose] def expand : QueryImpl (World aux L X F)
    (OracleComp (World aux (L ⊕ L) (X ⊕ X) H))
  | .inl (.inl n) => liftM ((World aux (L ⊕ L) (X ⊕ X) H).query (.inl (.inl n)))
  | .inl (.inr (.inl k)) => simulateQ (publicWord aux) (pair e k)
  | .inl (.inr (.inr a)) => liftM ((World aux (L ⊕ L) (X ⊕ X) H).query (.inl (.inr (.inr a))))
  | .inr k => simulateQ (privateWord aux) (pair e k)

/-- Both word tables split. The complete auxiliary table is carried along with them. -/
@[expose] def splitState (s : Cache aux L X F) : Cache aux (L ⊕ L) (X ⊕ X) H :=
  (QueryCache.addEquiv _ aux (splitCache e s.1.fst, s.1.snd), splitCache e s.2)

/-- A private word can be reconstructed only from a complete pair in the private table. -/
@[expose] def joinState (s : Cache aux (L ⊕ L) (X ⊕ X) H) : Cache aux L X F :=
  (QueryCache.addEquiv _ aux (joinCache e s.1.fst, s.1.snd), joinCache e s.2)

/-- Joining the image of a mixed state recovers its complete initial state. -/
theorem join_split (s : Cache aux L X F) : joinState aux e (splitState aux e s) = s := by
  obtain ⟨c, p⟩ := s
  change (QueryCache.addEquiv _ aux (joinCache e (splitCache e c.fst), c.snd),
    joinCache e (splitCache e p)) = _
  rw [joinCache_splitCache, joinCache_splitCache]
  exact Prod.ext ((QueryCache.addEquiv _ aux).apply_symm_apply c) rfl

private theorem split_frame (c : (L →ₒ F).QueryCache) (a : aux.QueryCache)
    (p : (X →ₒ F).QueryCache) :
    splitState aux e (QueryCache.addEquiv _ aux (c, a), p) =
      (QueryCache.addEquiv _ aux (splitCache e c, a), splitCache e p) := rfl

variable [DecidableEq A] [DecidableEq L] [DecidableEq X] [SampleableType F] [SampleableType H]
  [∀ a, SampleableType (aux.Range a)]

private theorem public_step {V : Type} [SampleableType V] (k : L)
    (c : (L →ₒ V).QueryCache) (a : aux.QueryCache) (p : (X →ₒ V).QueryCache) :
    (SecretEncoding.idealImpl ((L →ₒ V) + aux) X V (.inl (.inr (.inl k)))).run
      (QueryCache.addEquiv _ aux (c, a), p) =
    (fun z => (z.1, (QueryCache.addEquiv _ aux (z.2, a), p))) <$>
      ((L →ₒ V).randomOracle k).run c := by
  simp only [SecretEncoding.idealImpl, StateT.run_mk]
  rw [← QueryImpl.run_parallelStateT_randomOracle_map_eq]
  simp [QueryImpl.parallelStateT, Functor.map_map, Prod.map]

private theorem aux_step {V : Type} [SampleableType V] (k : A)
    (c : (L →ₒ V).QueryCache) (a : aux.QueryCache) (p : (X →ₒ V).QueryCache) :
    (SecretEncoding.idealImpl ((L →ₒ V) + aux) X V (.inl (.inr (.inr k)))).run
      (QueryCache.addEquiv _ aux (c, a), p) =
    (fun z => (z.1, (QueryCache.addEquiv _ aux (c, z.2), p))) <$>
      (aux.randomOracle k).run a := by
  simp only [SecretEncoding.idealImpl, StateT.run_mk]
  rw [← QueryImpl.run_parallelStateT_randomOracle_map_eq]
  simp [QueryImpl.parallelStateT, Functor.map_map, Prod.map]

private theorem map_state {α S T : Type} (f : S → T) :
    (Prod.map id f : α × S → _) = fun z => (z.1, f z.2) := by
  funext ⟨_, _⟩
  rfl

private theorem run_public {V α : Type} [SampleableType V]
    (prog : OracleComp (L →ₒ V) α) (c : (L →ₒ V).QueryCache)
    (a : aux.QueryCache) (p : (X →ₒ V).QueryCache) :
    (simulateQ (SecretEncoding.idealImpl ((L →ₒ V) + aux) X V)
      (simulateQ (publicWord aux) prog)).run (QueryCache.addEquiv _ aux (c, a), p) =
    (fun z => (z.1, (QueryCache.addEquiv _ aux (z.2, a), p))) <$>
      (simulateQ (L →ₒ V).randomOracle prog).run c := by
  rw [← QueryImpl.simulateQ_compose]
  simpa only [map_state] using (map_run_simulateQ_eq_of_query_map_eq _ _
    (fun t => (QueryCache.addEquiv _ aux (t, a), p))
    (fun k c => by
      simpa [QueryImpl.compose, publicWord, map_state] using (public_step aux k c a p).symm)
    prog c).symm

private theorem run_private {V α : Type} [SampleableType V]
    (prog : OracleComp (X →ₒ V) α) (c : ((L →ₒ V) + aux).QueryCache)
    (p : (X →ₒ V).QueryCache) :
    (simulateQ (SecretEncoding.idealImpl ((L →ₒ V) + aux) X V)
      (simulateQ (privateWord aux) prog)).run (c, p) =
    (fun z => (z.1, (c, z.2))) <$> (simulateQ (X →ₒ V).randomOracle prog).run p := by
  rw [← QueryImpl.simulateQ_compose]
  simpa only [map_state] using (map_run_simulateQ_eq_of_query_map_eq _ _ (fun t => (c, t))
    (fun k s => by simp [QueryImpl.compose, privateWord, SecretEncoding.idealImpl, map_state])
    prog p).symm

private theorem pair_word {D : Type} [DecidableEq D] (k : D) (c : (D →ₒ F).QueryCache) :
    (fun z => (z.1, splitCache e z.2)) <$> ((D →ₒ F).randomOracle k).run c =ᵈ
      (simulateQ ((D ⊕ D) →ₒ H).randomOracle (pair e k)).run (splitCache e c) := by
  have h := (run_pair_macro_evalDistEq_full_joint e k c).map
    (fun z : F × (D →ₒ F).QueryCache × ((D ⊕ D) →ₒ H).QueryCache => (z.1, z.2.2))
  simpa [Functor.map_map, Function.comp_def, pair] using h

private theorem step (t : (World aux L X F).Domain) (s : Cache aux L X F) :
    Prod.map id (splitState aux e) <$>
      (SecretEncoding.idealImpl ((L →ₒ F) + aux) X F t).run s =ᵈ
    (simulateQ (SecretEncoding.idealImpl (((L ⊕ L) →ₒ H) + aux) (X ⊕ X) H)
      (expand aux e t)).run (splitState aux e s) := by
  obtain ⟨ca, p⟩ := s
  obtain ⟨⟨c, a⟩, rfl⟩ := (QueryCache.addEquiv (L →ₒ F) aux).surjective ca
  rcases t with (n | (k | port)) | x
  · simp [expand, SecretEncoding.idealImpl, Functor.map_map, map_state]
  · have h := (pair_word e k c).map (fun z =>
      (z.1, (QueryCache.addEquiv _ aux (z.2, a), splitCache e p)))
    rw [public_step aux k c a p, split_frame]
    simp only [expand, run_public, Functor.map_map, map_state, split_frame] at h ⊢
    with_unfolding_all exact h
  · rw [aux_step aux port c a p, split_frame]
    simp only [expand, simulateQ_spec_query, aux_step aux port (splitCache e c) a (splitCache e p),
      map_state, Functor.map_map, split_frame]
    rfl
  · have h := (pair_word e x p).map (fun z =>
      (z.1, (QueryCache.addEquiv _ aux (splitCache e c, a), z.2)))
    rw [split_frame]
    simp only [expand, run_private, SecretEncoding.idealImpl, StateT.run_mk, Functor.map_map,
      map_state, split_frame] at h ⊢
    with_unfolding_all exact h

/-- Pairing both word tables preserves every adaptive observation and both complete terminal
states, including the cache of the auxiliary ports. -/
theorem run_joint {α : Type} (program : OracleComp (World aux L X F) α)
    (initial : Cache aux L X F) :
    (fun z => (z.1, z.2, splitState aux e z.2)) <$>
      (simulateQ (SecretEncoding.idealImpl ((L →ₒ F) + aux) X F) program).run initial =ᵈ
    (fun z => (z.1, joinState aux e z.2, z.2)) <$>
      (simulateQ (SecretEncoding.idealImpl (((L ⊕ L) →ₒ H) + aux) (X ⊕ X) H)
        (simulateQ (expand aux e) program)).run (splitState aux e initial) := by
  have coupled := evalDistEq_map_run_simulateQ_eq_of_query_evalDistEq_map_eq
    (SecretEncoding.idealImpl ((L →ₒ F) + aux) X F)
    (QueryImpl.compose (SecretEncoding.idealImpl (((L ⊕ L) →ₒ H) + aux) (X ⊕ X) H)
      (expand aux e))
    (splitState aux e) (step aux e) program initial
  simpa only [QueryImpl.simulateQ_compose, Functor.map_map, Function.comp_def, map_state,
    join_split]
    using coupled.map (fun z => (z.1, joinState aux e z.2, z.2))

end Derivations
end OracleComp.RandomOraclePairedValue
