/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.SimSemantics.StateT.UntilBad
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection
public import VCVio.OracleComp.SimSemantics.QueryImpl.Compose
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
# Hidden-seed derivations from a random oracle

A program over `pub.withDerivations X R = unifSpec + pub + (X →ₒ R)` makes public random-oracle
queries and *derivation* queries `x : X`. A `SecretEncoding pub S X R` places each derivation at
a public point: under the secret `s : S`, the derivation of `x` is the public answer at
`E.enc s x`, and `E.enc s` is injective with every encoded point answered in `R`.

* The real game `SecretEncoding.realImpl E s` answers both kinds of query from one lazily sampled
  public cache, reading a derivation `x` at `E.enc s x`.
* The ideal game `SecretEncoding.idealImpl pub X R` answers public queries from the public cache
  and derivations from an independent table; the secret does not enter it.

The two agree until a public query hits an encoded point. The proof couples them on a split
state (public cache, derivation table, flag): the coupled real game
`SecretEncoding.coupledImpl E s` stores the answers at encoded points in the table, and merging
the split state (`SecretEncoding.merge`) recovers the real cache exactly
(`SecretEncoding.map_run_simulateQ_coupledImpl`). The flagged ideal game
`SecretEncoding.flaggedIdealImpl E s` adds to the ideal game a flag raised by every public query
at an encoded point. Off the flag, the two take identically distributed steps
(`SecretEncoding.agreeUntilBad_coupledImpl_flaggedIdealImpl`), so the fundamental lemma
`QueryImpl.AgreeUntilBad.prEvent_simulateQ_run_le_add_bad_right` applies.

## Main statements

- `SecretEncoding.prEvent_realImpl_le_add`: for a fixed secret, an event of the real game is at
  most the same event of the ideal game, read on the merged cache, plus the probability that the
  flagged ideal game raises its flag.
- `SecretEncoding.agreeUntilBad_coupledImpl_flaggedIdealImpl`: the coupled real game and the
  flagged ideal game agree until the flag.
- `SecretEncoding.map_run_simulateQ_coupledImpl` and
  `SecretEncoding.map_run_simulateQ_flaggedIdealImpl`: the coupled and flagged games project onto
  the real and ideal games.
-/

public section

open OracleComp OracleSpec MeasureTheory

namespace OracleSpec

variable {ι : Type} (pub : OracleSpec ι) (X R : Type)

/-- Programs with uniform sampling, a public random oracle `pub`, and derivation queries
`X →ₒ R`. -/
abbrev withDerivations : OracleSpec ((ℕ ⊕ ι) ⊕ X) := unifSpec + pub + (X →ₒ R)

end OracleSpec

/-- An injective, secret-keyed encoding of derivation inputs as public oracle inputs, each
answered in `R`. -/
structure SecretEncoding {ι : Type} (pub : OracleSpec ι) (S X R : Type) where
  /-- The public oracle input at which the derivation of `x` under secret `s` is read. -/
  enc : S → X → ι
  /-- The public oracle answers every encoded point in `R`. -/
  range_eq : ∀ s x, pub.Range (enc s x) = R
  /-- Distinct derivation inputs have distinct encodings. -/
  injective : ∀ s, Function.Injective (enc s)

namespace SecretEncoding

variable {ι : Type} {pub : OracleSpec ι} {S X R : Type} (E : SecretEncoding pub S X R)

/-- Every point witnessed as an encoding is answered in `R`. -/
theorem range_eq_of_enc_eq {s : S} {x : X} {t : ι} (h : E.enc s x = t) : pub.Range t = R :=
  h ▸ E.range_eq s x

/-! ## Split state: public cache, derivation table, flag -/

/-- The public cache off the encoded points, paired with the derivation table. -/
abbrev SplitCache (pub : OracleSpec ι) (X R : Type) := pub.QueryCache × (X →ₒ R).QueryCache

open Classical in
/-- Rebuild the real public cache from a split state: an encoded point `E.enc s x` reads the
table at `x`, every other point reads the public cache. -/
noncomputable def merge (s : S) (st : SplitCache pub X R) : pub.QueryCache :=
  .ofFn fun t => if h : ∃ x, E.enc s x = t then
    (st.2 h.choose).map (cast (E.range_eq_of_enc_eq h.choose_spec).symm) else st.1 t

/-- The merged cache at an encoded point reads the table at any witness of the encoding. -/
theorem merge_apply_of_enc_eq (s : S) (st : SplitCache pub X R) {x : X} {t : ι}
    (hx : E.enc s x = t) :
    (E.merge s st) t = (st.2 x).map (cast (E.range_eq_of_enc_eq hx).symm) := by
  have key : ∀ y (hy : E.enc s y = t),
      (st.2 y).map (cast (E.range_eq_of_enc_eq hy).symm) =
        (st.2 x).map (cast (E.range_eq_of_enc_eq hx).symm) := by
    intro y hy
    obtain rfl := E.injective s (hy.trans hx.symm)
    rfl
  simp only [merge, QueryCache.ofFn_apply]
  split
  · rename_i h
    exact key _ h.choose_spec
  · rename_i h
    exact absurd ⟨x, hx⟩ h

/-- The merged cache at `E.enc s x` reads the table at `x`. -/
theorem merge_apply_enc (s : S) (st : SplitCache pub X R) (x : X) :
    (E.merge s st) (E.enc s x) = (st.2 x).map (cast (E.range_eq s x).symm) :=
  E.merge_apply_of_enc_eq s st rfl

/-- The merged cache at a point that encodes nothing reads the public cache. -/
theorem merge_apply_of_not_exists (s : S) (st : SplitCache pub X R) {t : ι}
    (ht : ¬∃ x, E.enc s x = t) : (E.merge s st) t = st.1 t := by
  simp only [merge, QueryCache.ofFn_apply, ht, ↓reduceDIte]

/-- Merging two empty caches gives the empty cache. -/
@[simp] theorem merge_empty (s : S) : E.merge s ((∅, ∅) : SplitCache pub X R) = ∅ := by
  refine QueryCache.ext fun t ↦ ?_
  by_cases ht : ∃ x, E.enc s x = t
  · obtain ⟨x, rfl⟩ := ht
    simp only [merge_apply_enc, QueryCache.empty_apply, Option.map_none]
  · simp only [E.merge_apply_of_not_exists s _ ht, QueryCache.empty_apply]

variable [DecidableEq ι]

/-- Filling the table at `x` fills the merged cache at `E.enc s x`. -/
theorem merge_cacheQuery_table [DecidableEq X] (s : S) (st : SplitCache pub X R) (x : X)
    (u : pub.Range (E.enc s x)) :
    E.merge s (st.1, st.2.cacheQuery x (cast (E.range_eq s x) u)) =
      (E.merge s st).cacheQuery (E.enc s x) u := by
  refine QueryCache.ext fun t ↦ ?_
  by_cases ht : ∃ y, E.enc s y = t
  · obtain ⟨y, rfl⟩ := ht
    rw [merge_apply_enc]
    dsimp only
    by_cases hy : y = x
    · subst hy
      simp only [QueryCache.cacheQuery_self, Option.map_some, cast_cast, cast_eq]
    · rw [QueryCache.cacheQuery_of_ne _ _ hy,
        QueryCache.cacheQuery_of_ne _ _ fun h ↦ hy (E.injective s h), merge_apply_enc]
  · rw [E.merge_apply_of_not_exists s _ ht,
      QueryCache.cacheQuery_of_ne _ _ fun h ↦ ht ⟨x, h.symm⟩, E.merge_apply_of_not_exists s _ ht]

/-- Filling the public cache at a point that encodes nothing fills the merged cache there. -/
theorem merge_cacheQuery_public (s : S) (st : SplitCache pub X R) {t : ι}
    (ht : ¬∃ x, E.enc s x = t) (u : pub.Range t) :
    E.merge s (st.1.cacheQuery t u, st.2) = (E.merge s st).cacheQuery t u := by
  refine QueryCache.ext fun t' ↦ ?_
  by_cases ht' : ∃ y, E.enc s y = t'
  · obtain ⟨y, rfl⟩ := ht'
    rw [merge_apply_enc, QueryCache.cacheQuery_of_ne _ _ fun h ↦ ht ⟨y, h⟩, merge_apply_enc]
  · rw [E.merge_apply_of_not_exists s _ ht']
    dsimp only
    by_cases h : t' = t
    · subst h
      simp only [QueryCache.cacheQuery_self]
    · rw [QueryCache.cacheQuery_of_ne _ _ h, QueryCache.cacheQuery_of_ne _ _ h,
        E.merge_apply_of_not_exists s _ ht']

variable [∀ t, SampleableType (pub.Range t)]

/-- Answer a derivation query `x` by the public query at `E.enc s x`. -/
@[expose] def deriveImpl (s : S) :
    QueryImpl (pub.withDerivations X R) (OracleComp (unifSpec + pub)) := fun
  | .inl t => (unifSpec + pub).query t
  | .inr x => cast (E.range_eq s x) <$> (unifSpec + pub).query (.inr (E.enc s x))

/-- The real game: derivations and public queries share one lazily sampled public cache. -/
@[expose] noncomputable def realImpl (s : S) :
    QueryImpl (pub.withDerivations X R) (StateT pub.QueryCache ProbComp) :=
  pub.romImpl ∘ₛ E.deriveImpl s

/-! ## The real game, query by query -/

/-- The real game forwards a uniform query and leaves the cache unchanged. -/
theorem realImpl_run_unif (s : S) (n : ℕ) (C : pub.QueryCache) :
    (E.realImpl s (.inl (.inl n))).run C =
      (fun u => (u, C)) <$> (unifSpec.query n : ProbComp _) := by
  simp [realImpl, deriveImpl, unifFwdImpl, bind_pure_comp]

/-- The real game answers a public query from its random oracle. -/
theorem realImpl_run_pub (s : S) (t : ι) (C : pub.QueryCache) :
    (E.realImpl s (.inl (.inr t))).run C = (pub.randomOracle t).run C := by
  simp only [realImpl, deriveImpl, QueryImpl.apply_compose, simulateQ_spec_query]
  rfl

/-- The real game answers a derivation `x` by the random oracle at `E.enc s x`. -/
theorem realImpl_run_derive (s : S) (x : X) (C : pub.QueryCache) :
    (E.realImpl s (.inr x)).run C =
      Prod.map (cast (E.range_eq s x)) id <$> (pub.randomOracle (E.enc s x)).run C := by
  simp only [realImpl, deriveImpl, QueryImpl.apply_compose, simulateQ_map, simulateQ_spec_query,
    StateT.run_map]
  rfl

/-! ## The coupled real game -/

variable [DecidableEq X]

/-- A public query at the encoded point `t = E.enc s x` in the coupled real game: read or
fill the derivation table at `x`, and raise the flag. -/
noncomputable def encodedStep (s : S) {t : ι} (x : X) (hx : E.enc s x = t)
    (st : SplitCache pub X R × Bool) : ProbComp (pub.Range t × (SplitCache pub X R × Bool)) :=
  match st.1.2 x with
  | some v => pure (cast (E.range_eq_of_enc_eq hx).symm v, (st.1, true))
  | none => do
      let u ← $ᵗ pub.Range t
      pure (u, ((st.1.1, st.1.2.cacheQuery x (cast (E.range_eq_of_enc_eq hx) u)), true))

open Classical in
/-- The real game on a split state: answers at encoded points live in the derivation table, all
other public answers in the public cache; a public query at an encoded point raises the flag.
Its samplers are those of the real game. -/
noncomputable def coupledImpl (s : S) :
    QueryImpl (pub.withDerivations X R) (StateT (SplitCache pub X R × Bool) ProbComp) := fun
  | .inl (.inl n) => StateT.mk fun st => (fun u => (u, st)) <$> (unifSpec.query n : ProbComp _)
  | .inl (.inr t) => StateT.mk fun st =>
      if h : ∃ x, E.enc s x = t then E.encodedStep s h.choose h.choose_spec st
      else (fun z => (z.1, ((z.2, st.1.2), st.2))) <$> (pub.randomOracle t).run st.1.1
  | .inr x => StateT.mk fun st =>
      match st.1.2 x with
      | some v => pure (v, st)
      | none => do
          let u ← $ᵗ pub.Range (E.enc s x)
          pure (cast (E.range_eq s x) u,
            ((st.1.1, st.1.2.cacheQuery x (cast (E.range_eq s x) u)), st.2))

/-- A public query of the coupled real game at a point `E.enc s x` is the encoded step at `x`. -/
theorem coupledImpl_run_of_enc_eq (s : S) {x : X} {t : ι} (hx : E.enc s x = t)
    (st : SplitCache pub X R × Bool) :
    (E.coupledImpl s (.inl (.inr t))).run st = E.encodedStep s x hx st := by
  simp only [coupledImpl, StateT.run_mk]
  have key : ∀ y (hy : E.enc s y = t), E.encodedStep s y hy st = E.encodedStep s x hx st := by
    intro y hy
    obtain rfl := E.injective s (hy.trans hx.symm)
    rfl
  split
  · exact key _ _
  · rename_i h
    exact absurd ⟨x, hx⟩ h

/-- A public query of the coupled real game at a point that encodes nothing is answered from the
public cache. -/
theorem coupledImpl_run_of_not_exists (s : S) {t : ι} (ht : ¬∃ x, E.enc s x = t)
    (st : SplitCache pub X R × Bool) :
    (E.coupledImpl s (.inl (.inr t))).run st =
      (fun z => (z.1, ((z.2, st.1.2), st.2))) <$> (pub.randomOracle t).run st.1.1 := by
  simp only [coupledImpl, StateT.run_mk]
  split
  · rename_i h
    exact absurd h ht
  · rfl

/-- Forgetting the flag and merging the split state turns the coupled game into the real one. -/
theorem map_run_simulateQ_coupledImpl (s : S) {α : Type}
    (oa : OracleComp (pub.withDerivations X R) α) (st : SplitCache pub X R × Bool) :
    Prod.map id (E.merge s ∘ Prod.fst) <$> (simulateQ (E.coupledImpl s) oa).run st =
      (simulateQ (E.realImpl s) oa).run (E.merge s st.1) := by
  refine map_run_simulateQ_eq_of_query_map_eq _ _ _ (fun t st ↦ ?_) oa st
  rcases t with (n | t) | x
  · simp only [coupledImpl, StateT.run_mk, realImpl_run_unif, Functor.map_map, Prod.map_apply,
      id_eq, Function.comp_apply]
    rfl
  · by_cases ht : ∃ x, E.enc s x = t
    · obtain ⟨x, rfl⟩ := ht
      rw [E.coupledImpl_run_of_enc_eq s rfl, realImpl_run_pub, randomOracle.run_eq,
        Function.comp_apply, merge_apply_enc]
      unfold encodedStep
      cases hT : st.1.2 x with
      | some v => simp
      | none =>
        simp only [Option.map_none, map_bind, map_pure, Prod.map_apply, id_eq]
        refine bind_congr fun u ↦ ?_
        rw [← merge_cacheQuery_table]
        rfl
    · rw [E.coupledImpl_run_of_not_exists s ht, realImpl_run_pub, randomOracle.run_eq,
        randomOracle.run_eq, Function.comp_apply, E.merge_apply_of_not_exists s _ ht]
      cases hc : st.1.1 t with
      | some v => simp
      | none =>
        simp only [map_bind, map_pure, Prod.map_apply, id_eq, Function.comp_apply]
        refine bind_congr fun u ↦ ?_
        rw [← E.merge_cacheQuery_public s _ ht]
  · rw [realImpl_run_derive, randomOracle.run_eq, Function.comp_apply, merge_apply_enc]
    simp only [coupledImpl, StateT.run_mk]
    cases hT : st.1.2 x with
    | some v => simp [cast_cast]
    | none =>
      simp only [Option.map_none, map_bind, map_pure, Prod.map_apply, id_eq]
      refine bind_congr fun u ↦ ?_
      rw [← merge_cacheQuery_table]
      rfl

/-! ## The ideal game and its flagged form -/

variable [SampleableType R]

variable (pub X R) in
/-- The ideal game: public queries read the public cache and derivations an independent table,
both lazily sampled; no secret enters it. -/
@[expose] noncomputable def idealImpl :
    QueryImpl (pub.withDerivations X R) (StateT (SplitCache pub X R) ProbComp) := fun
  | .inl (.inl n) => StateT.mk fun st => (fun u => (u, st)) <$> (unifSpec.query n : ProbComp _)
  | .inl (.inr t) => StateT.mk fun st =>
      (fun z => (z.1, (z.2, st.2))) <$> (pub.randomOracle t).run st.1
  | .inr x => StateT.mk fun st =>
      (fun z => (z.1, (st.1, z.2))) <$> ((X →ₒ R).randomOracle x).run st.2

open Classical in
/-- Whether a query is a public query at a point `E.enc s x`. -/
@[expose] noncomputable def encodedQuery (s : S) : (pub.withDerivations X R).Domain → Bool
  | .inl (.inr t) => decide (∃ x, E.enc s x = t)
  | _ => false

/-- The ideal game with a flag, raised by every public query at a point encoded under `s`. -/
@[expose] noncomputable def flaggedIdealImpl (s : S) :
    QueryImpl (pub.withDerivations X R) (StateT (SplitCache pub X R × Bool) ProbComp) :=
  (idealImpl pub X R).extendState fun t _ _ _ f ↦ f || E.encodedQuery s t

/-- Forgetting the flag turns the flagged ideal game into the ideal one. -/
theorem map_run_simulateQ_flaggedIdealImpl (s : S) {α : Type}
    (oa : OracleComp (pub.withDerivations X R) α) (st : SplitCache pub X R) (f : Bool) :
    Prod.map id Prod.fst <$> (simulateQ (E.flaggedIdealImpl s) oa).run (st, f) =
      (simulateQ (idealImpl pub X R) oa).run st :=
  extendState_run_proj_eq _ _ oa st f

/-- Once raised, the flag of the flagged ideal game stays raised. -/
theorem flaggedIdealImpl_preservesInv (s : S) :
    QueryImpl.PreservesInv (E.flaggedIdealImpl s) fun st ↦ st.2 = true := by
  intro t st hst z hz
  simp only [flaggedIdealImpl, QueryImpl.extendState_apply, support_bind, support_pure,
    Set.mem_iUnion, Set.mem_singleton_iff] at hz
  obtain ⟨_, -, rfl⟩ := hz
  simp [hst]

/-- Off the flag, the coupled real game and the flagged ideal game take identically distributed
steps: they differ only in the samplers of the derivation answers, both uniform on `R`, and on
public queries at encoded points, which raise the flag in both. -/
theorem agreeUntilBad_coupledImpl_flaggedIdealImpl (s : S) :
    QueryImpl.AgreeUntilBad (E.coupledImpl s) (E.flaggedIdealImpl s) fun st ↦ st.2 = true := by
  rintro t ⟨⟨c, T⟩, f⟩ hf Q
  simp only [Bool.not_eq_true] at hf
  subst hf
  rcases t with (n | t) | x
  · have h : (E.coupledImpl s (.inl (.inl n))).run ((c, T), false) =
        (E.flaggedIdealImpl s (.inl (.inl n))).run ((c, T), false) := by
      simp [coupledImpl, flaggedIdealImpl, idealImpl, encodedQuery]
    rw [h]
  · by_cases ht : ∃ x, E.enc s x = t
    · obtain ⟨x, rfl⟩ := ht
      refine (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hz' ↦ hz'.2 ?_).trans
        (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hz' ↦ hz'.2 ?_).symm
      · rw [E.coupledImpl_run_of_enc_eq s rfl] at hz
        unfold encodedStep at hz
        split at hz
        · simp only [support_pure, Set.mem_singleton_iff] at hz
          rw [hz]
        · simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hz
          obtain ⟨_, -, rfl⟩ := hz
          rfl
      · simp only [flaggedIdealImpl, QueryImpl.extendState_apply, support_bind, support_pure,
          Set.mem_iUnion, Set.mem_singleton_iff] at hz
        obtain ⟨_, -, rfl⟩ := hz
        simp [encodedQuery]
    · have h : (E.coupledImpl s (.inl (.inr t))).run ((c, T), false) =
          (E.flaggedIdealImpl s (.inl (.inr t))).run ((c, T), false) := by
        rw [E.coupledImpl_run_of_not_exists s ht]
        simp [flaggedIdealImpl, idealImpl, encodedQuery, ht]
      rw [h]
  · cases hT : T x with
    | some v =>
      have h : (E.coupledImpl s (.inr x)).run ((c, T), false) =
          (E.flaggedIdealImpl s (.inr x)).run ((c, T), false) := by
        simp [coupledImpl, flaggedIdealImpl, idealImpl, hT, encodedQuery]
      rw [h]
    | none =>
      have h₁ : (E.coupledImpl s (.inr x)).run ((c, T), false) =
          (fun u ↦ (u, ((c, T.cacheQuery x u), false))) <$>
            (cast (E.range_eq s x) <$> ($ᵗ pub.Range (E.enc s x))) := by
        simp [coupledImpl, hT]
      have h₂ : (E.flaggedIdealImpl s (.inr x)).run ((c, T), false) =
          (fun u ↦ (u, ((c, T.cacheQuery x u), false))) <$> ($ᵗ R) := by
        simp [flaggedIdealImpl, idealImpl, hT, encodedQuery]
      rw [h₁, h₂, prEvent_map (cast (E.range_eq s x) <$> ($ᵗ pub.Range (E.enc s x))),
        prEvent_map ($ᵗ R), SampleableType.prEvent_map_cast_uniformSample]

/-- Real game against the ideal game, for a fixed secret: an event of the real game is at most
the event, read on the merged cache, in the ideal game, plus the chance that the flagged ideal
game makes a public query at an encoded point. -/
theorem prEvent_realImpl_le_add (s : S) {α : Type} (oa : OracleComp (pub.withDerivations X R) α)
    (P : α × pub.QueryCache → Prop) :
    Pr{let z ← (simulateQ (E.realImpl s) oa).run ∅}[P z] ≤
      Pr{let z ← (simulateQ (idealImpl pub X R) oa).run (∅, ∅)}[P (z.1, E.merge s z.2)] +
        Pr{let z ← (simulateQ (E.flaggedIdealImpl s) oa).run ((∅, ∅), false)}[z.2.2 = true] := by
  have h := E.map_run_simulateQ_coupledImpl s oa ((∅, ∅), false)
  rw [merge_empty] at h
  rw [← h, prEvent_map,
    ← E.map_run_simulateQ_flaggedIdealImpl s oa (∅, ∅) false, prEvent_map]
  exact (E.agreeUntilBad_coupledImpl_flaggedIdealImpl s).prEvent_simulateQ_run_le_add_bad_right
    (E.flaggedIdealImpl_preservesInv s) oa _ _

end SecretEncoding
