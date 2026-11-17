/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.BLS.Invariants
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-! # Deferred challenge sampling for BLS

The selected random-oracle answer in the Boneh–Lynn–Shacham game can be sampled before
the adversary runs. Scalar tags retain every other sampled preimage; the selected tag
contains no preimage. A probabilistic state map relates the deferred and upfront draws.
-/

public section

open OracleComp OracleSpec

namespace BLS

/-- Replace the selected scalar by a challenge tag, preserving the indexed history. -/
@[expose] def tagState {V M : Type} (j : ℕ) (s : OracleState V M) :
    OracleState (Option V) M :=
  { cache := QueryCache.ofFn fun msg => (s.cache msg).map fun (v, i) =>
      (if i = j then none else some v, i)
    count := s.count
    signed := s.signed
    selected := s.selected.map (fun _ => none)
    bad := s.bad }

/-- Complete a scalar history with its selected challenge; sample that challenge independently
when the selected insertion has not yet occurred. -/
@[expose] def fillChallenge {V W M : Type} [SampleableType W]
    (f : V → W) (j : ℕ) (s : OracleState V M) :
    ProbComp (OracleState (Option V) M × W) :=
  match s.selected with
  | none => (fun h => (tagState j s, h)) <$> ($ᵗ W : ProbComp W)
  | some v => pure (tagState j s, f v)

/-- Draw a challenge tag at the guessed insertion and an independent scalar elsewhere. -/
@[expose] def tagDraw {V : Type} [SampleableType V] (j n : ℕ) : ProbComp (Option V) :=
  if n = j then pure none else some <$> ($ᵗ V : ProbComp V)

/-- Honest hash/signing handler with an upfront challenge and scalar-tagged other entries.
The challenge is an immutable component of its state. -/
private abbrev programmedOracle {V W M : Type} [SampleableType V] [DecidableEq M]
    (f : V → W) (sign : W → W) (j : ℕ) :
    QueryImpl ((unifSpec + (M →ₒ W)) + (M →ₒ W))
      (StateT (OracleState (Option V) M × W) ProbComp) :=
  fun t s => (fun z => (z.1, z.2, s.2)) <$>
    (indexedOracle (tagDraw j) (fun tag => tag.elim s.2 f)
      (fun tag => sign (tag.elim s.2 f)) (some j) t).run s.1

private theorem tagState_insert {V M : Type} [DecidableEq M]
    (j : ℕ) (s : OracleState V M) (msg : M) (v : V) :
    tagState j (s.insert (some j) msg v) =
      (tagState j s).insert (some j) msg (if s.count = j then none else some v) := by
  apply OracleState.ext
  · apply QueryCache.ext
    intro n
    by_cases hn : n = msg
    · subst n
      simp [tagState, OracleState.insert]
    · simp [tagState, OracleState.insert, hn]
  · rfl
  · rfl
  · by_cases hj : s.count = j
    · simp [tagState, OracleState.insert, hj]
    · simp [tagState, OracleState.insert, hj, Ne.symm hj]
  · rfl

private theorem tagState_recordSign {V M : Type}
    (j : ℕ) (s : OracleState V M) (msg : M) (i : ℕ) :
    tagState j (s.recordSign (some j) msg i) =
      (tagState j s).recordSign (some j) msg i := rfl

private theorem fillChallenge_recordSign {V W M : Type} [SampleableType W]
    (f : V → W) (j : ℕ) (s : OracleState V M) (msg : M) (i : ℕ) :
    fillChallenge f j (s.recordSign (some j) msg i) =
      (fun z => (z.1.recordSign (some j) msg i, z.2)) <$> fillChallenge f j s := by
  cases hc : s.selected <;>
    simp [fillChallenge, OracleState.recordSign, tagState, hc, Functor.map_map]

private theorem fillChallenge_insert_target {V W M : Type} [SampleableType W]
    [DecidableEq M] (f : V → W) (j : ℕ) (s : OracleState V M) (msg : M) (v : V)
    (hj : s.count = j) :
    fillChallenge f j (s.insert (some j) msg v) =
      pure ((tagState j s).insert (some j) msg none, f v) := by
  have hsel : (s.insert (some j) msg v).selected = some v := by
    simp [OracleState.insert, hj]
  simp only [fillChallenge, hsel, tagState_insert, hj, ↓reduceIte]

private theorem fillChallenge_insert_other {V W M : Type} [SampleableType W]
    [DecidableEq M] (f : V → W) (j : ℕ) (s : OracleState V M) (msg : M) (v : V)
    (hj : s.count ≠ j) :
    fillChallenge f j (s.insert (some j) msg v) =
      (fun z => (z.1.insert (some j) msg (some v), z.2)) <$> fillChallenge f j s := by
  have htag := tagState_insert j s msg v
  simp only [ite_eq_right_iff.mpr (fun h => (hj h).elim)] at htag
  have hsel : (s.insert (some j) msg v).selected = s.selected := by
    simp [OracleState.insert, Ne.symm hj]
  cases hc : s.selected <;>
    simp [fillChallenge, hsel, hc, htag, Functor.map_map]

/-- An indexed scalar lookup followed by challenge completion agrees in distribution with
completing the challenge first and using the programmed tag lookup. -/
private theorem indexedEntry_fillChallenge {V W M γ : Type} [SampleableType V] [SampleableType W]
    [DecidableEq M] (f : V → W) (hf : Function.Bijective f) (j : ℕ)
    (msg : M) (s : OracleState V M) (hs : SelectionInv j s)
    (k : W → ℕ → (OracleState (Option V) M × W) → ProbComp γ) :
    ((indexedEntry (fun _ => $ᵗ V) (some j) msg).run s >>= fun z =>
      fillChallenge f j z.2 >>= k (f z.1.1) z.1.2) =ᵈ
    (fillChallenge f j s >>= fun st =>
      (indexedEntry (tagDraw j) (some j) msg).run st.1 >>= fun z =>
        k (z.1.1.elim st.2 f) z.1.2 (z.2, st.2)) := by
  cases hc : s.cache msg with
  | some vi =>
    obtain ⟨v, i⟩ := vi
    by_cases hi : i = j
    · subst i
      have hsel := hs.selected msg v hc
      simp [indexedEntry, StateT.run, hc, fillChallenge, hsel, tagState]
    · cases hsel : s.selected <;>
        simp [indexedEntry, StateT.run, hc, fillChallenge, hsel, tagState, hi,
          bind_map_left]
  | none =>
    have hcache : (tagState j s).cache msg = none := by simp [tagState, hc]
    have hcount : (tagState j s).count = s.count := rfl
    by_cases hj : s.count = j
    · have hsel : s.selected = none := hs.pending.mpr hj.le
      simp only [indexedEntry, StateT.run, hc, bind_map_left]
      simp only [fillChallenge_insert_target f j s msg _ hj, pure_bind]
      simp only [fillChallenge, hsel, bind_map_left, hcache, hcount, tagDraw, hj,
        ↓reduceIte, map_pure, pure_bind, Option.elim_none]
      have heq := (SampleableType.map_uniformSample_evalDistEq_of_bijective hf).bind_left
        (fun h => k h j ((tagState j s).insert (some j) msg none, h))
      simpa only [bind_map_left, hj] using heq
    · simp only [indexedEntry, StateT.run, hc, bind_map_left]
      simp only [fillChallenge_insert_other f j s msg _ hj, bind_map_left]
      cases hsel : s.selected with
      | some v =>
        simp [fillChallenge, hsel, hcache, hcount, tagDraw, hj, bind_map_left]
      | none =>
        simp only [fillChallenge, hsel, bind_map_left, hcache, hcount, tagDraw, hj,
          ↓reduceIte, Functor.map_map, bind_map_left, Option.elim_some]
        exact OracleComp.EvalDistEq.bind_bind_swap _ _ _

/-- Challenge completion intertwines the honest scalar handler with the upfront-programmed
handler on every state satisfying the selected-value invariant. -/
private theorem indexedOracle_fillChallenge_intertwines {V W M : Type}
    [SampleableType V] [SampleableType W] [DecidableEq M]
    (f : V → W) (hf : Function.Bijective f) (sign : W → W) (j : ℕ) :
    QueryImpl.IntertwinesOn (SelectionInv j) (fillChallenge (M := M) f j)
      (indexedOracle (fun _ => $ᵗ V) f (sign ∘ f) (some j))
      (programmedOracle f sign j) := by
  intro t s hs γ _ k
  rcases t with (t | msg) | msg
  · change 𝒟[((fun v => (v, s)) <$> (unifSpec.query t : ProbComp _)) >>=
      fun z => fillChallenge f j z.2 >>= k z.1] = _
    simp only [bind_map_left, programmedOracle, StateT.run]
    change 𝒟[(unifSpec.query t : ProbComp _) >>= fun a => fillChallenge f j s >>= k a] =
      𝒟[fillChallenge f j s >>= fun st =>
        ((fun z => (z.1, z.2, st.2)) <$>
          ((fun a => (a, st.1)) <$> (unifSpec.query t : ProbComp _))) >>=
          fun z => k z.1 z.2]
    simp only [Functor.map_map, bind_map_left]
    exact evalDist_bind_bind_swap_of_uniform _ _ _
  · simp only [programmedOracle, indexedOracle, HAdd.hAdd, QueryImpl.add, StateT.run, bind_map_left]
    exact (indexedEntry_fillChallenge f hf j msg s hs (fun v _ st => k v st)).evalDist_eq
  · simp only [programmedOracle, indexedOracle, HAdd.hAdd, QueryImpl.add,
      StateT.run, bind_map_left, fillChallenge_recordSign, Function.comp_apply]
    exact (indexedEntry_fillChallenge f hf j msg s hs
      (fun v i st => k (sign v) (st.1.recordSign (some j) msg i, st.2))).evalDist_eq

/-- The selected random-oracle answer may be sampled before an arbitrary adaptive execution.
The final scalar history is completed by its selected challenge on the left. -/
theorem simulateQ_fillChallenge_evalDistEq {V W M α : Type}
    [SampleableType V] [SampleableType W] [DecidableEq M]
    (f : V → W) (hf : Function.Bijective f) (sign : W → W) (j : ℕ)
    (oa : OracleComp ((unifSpec + (M →ₒ W)) + (M →ₒ W)) α)
    (s : OracleState V M) (hs : SelectionInv j s) :
    ((simulateQ (indexedOracle (fun _ => $ᵗ V) f (sign ∘ f) (some j)) oa).run s >>=
      fun z => (fun st => (z.1, st)) <$> fillChallenge f j z.2) =ᵈ
    (fillChallenge f j s >>= fun st => (simulateQ
      (show QueryImpl ((unifSpec + (M →ₒ W)) + (M →ₒ W))
        (StateT (OracleState (Option V) M × W) ProbComp) from
        fun t s => (fun z => (z.1, z.2, s.2)) <$>
          (indexedOracle (tagDraw j) (fun tag => tag.elim s.2 f)
            (fun tag => sign (tag.elim s.2 f)) (some j) t).run s.1) oa).run st) := by
  let : MeasurableSpace (α × (OracleState (Option V) M × W)) := ⊤
  apply EvalDistEq.of_evalDist_eq
  have h := (indexedOracle_fillChallenge_intertwines f hf sign j).evalDist_simulateQ_run
    (indexedOracle_preserves_selectionInv (fun _ => $ᵗ V) f (sign ∘ f) j)
    oa s hs (fun a st => pure (a, st))
  simpa only [bind_pure_comp, bind_pure, Prod.eta, id_map] using h

/-- The upfront challenge remains unchanged throughout the programmed execution. -/
theorem programmedOracle_run {V W M α : Type} [SampleableType V] [DecidableEq M]
    (f : V → W) (sign : W → W) (j : ℕ)
    (oa : OracleComp ((unifSpec + (M →ₒ W)) + (M →ₒ W)) α)
    (s : OracleState (Option V) M) (h : W) :
    (simulateQ
      (show QueryImpl ((unifSpec + (M →ₒ W)) + (M →ₒ W))
        (StateT (OracleState (Option V) M × W) ProbComp) from
        fun t s => (fun z => (z.1, z.2, s.2)) <$>
          (indexedOracle (tagDraw j) (fun tag => tag.elim s.2 f)
            (fun tag => sign (tag.elim s.2 f)) (some j) t).run s.1) oa).run (s, h) =
      (fun z => (z.1, z.2, h)) <$>
        (simulateQ (indexedOracle (tagDraw j) (fun tag => tag.elim h f)
          (fun tag => sign (tag.elim h f)) (some j)) oa).run s := by
  symm
  exact map_run_simulateQ_eq_of_query_map_eq _ _ (fun st => (st, h))
    (fun _ _ => rfl) oa s

/-- Tagging an empty history leaves an empty tag history. -/
theorem tagState_empty {V M : Type} (j : ℕ) :
    tagState j (OracleState.empty : OracleState V M) = OracleState.empty := by
  apply OracleState.ext <;> simp [tagState, OracleState.empty]
  rfl

end BLS
