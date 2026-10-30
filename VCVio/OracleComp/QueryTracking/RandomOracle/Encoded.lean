/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Commute
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.OracleComp.SimSemantics.StateT.UntilBad
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# An encoded random oracle until a clash of encodings

A family of typed random oracles `spec` can be implemented by one random oracle `D →ₒ M`: a typed
point `t` is answered by the single oracle at its encoding `encode t`, truncated to the typed
range (`OracleComp.RandomOracleEncoding`). On the common interface
`unifSpec + (spec + (D →ₒ M))`, which also offers the raw inputs of the single oracle, this file
compares two worlds.

* The single-oracle world `RandomOracleEncoding.singleImpl` answers typed points and raw inputs by
  one lazy random oracle. It is the random oracle model of the single oracle after the program
  translation `RandomOracleEncoding.encodeImpl`
  (`RandomOracleEncoding.simulateQ_romImpl_simulateQ_encodeImpl`).
* The typed world `RandomOracleEncoding.typedImpl` answers typed points by independent lazy random
  oracles, and a raw input `x` by a router that reads it as the typed point `route x` and
  completes the typed answer there with a private value of `x`. On uniform and typed queries it is
  the random oracle model `spec.romImpl` with the table of private values passive
  (`RandomOracleEncoding.typedImpl_inl_run`, `RandomOracleEncoding.typedImpl_inr_inl_run`).

The two worlds agree until a clash, two cached typed points with the same encoding
(`RandomOracleEncoding.Clash`): an event of the output of the single-oracle world is at most the
same event, or a clash of the final typed cache, in the typed world
(`RandomOracleEncoding.prEvent_simulateQ_singleImpl_run_le`). For an injective encoding of the
inputs of one random oracle into another, `OracleComp.RandomOracleRouting` (`Routing.lean`)
preserves the whole output measure without a clash term.

## Scope

The router reads every encoding as a typed point: `route` is total on the image of `encode`
(`RandomOracleEncoding.isSome_route_encode`). A raw input that encodes a cached typed point is
then answered in the typed world from that point's typed answer, as the single oracle answers it.
An encoding whose router leaves some encoding unread is not an instance of
`OracleComp.RandomOracleEncoding`.

## Proof

The single-oracle world samples a whole value of `M` at the first touch of an encoding, while the
typed world samples only the typed answer, so no deterministic map of states relates the two. The
probabilistic map `RandomOracleEncoding.fill` reads a single-oracle cache off a typed state: it
queries the table of private values, as a lazy random oracle, at the encoding of every cached
typed point, and completes each typed answer with the value found there
(`RandomOracleEncoding.singleView`). A cache is a function, so a typed state can cache infinitely
many points, and drawing a value for each of them is then no finite computation; the fill is
meaningful only on the states with finitely many cached typed points, and the step condition is
stated on the invariant `RandomOracleEncoding.StateInv` through `QueryImpl.IntertwinesOn`.

The patched typed world `RandomOracleEncoding.patchedImpl` takes the steps of the typed world,
except on a step that creates a clash and from a state with a clash, where it fills, takes the
step of the single-oracle world and keeps the filled cache. Either way its typed cache after a
step is `RandomOracleEncoding.mark`, the typed cache with the queried typed point recorded
(`RandomOracleEncoding.mem_support_typedHashImpl_run`). The fill intertwines it with the
single-oracle world (`RandomOracleEncoding.intertwinesOn_fill_patchedImpl_singleImpl`); it agrees
with the typed world until a clash (`RandomOracleEncoding.agreeUntilBad_typedImpl_patchedImpl`);
and `QueryImpl.IntertwinesOn.prEvent_simulateQ_run_le_or_bad` combines the two. The steps commute
with the draws of the fill because queries to a lazy random oracle commute
(`randomOracle.evalDist_run_bind_simulateQ_run_swap`,
`randomOracle.evalDist_simulateQ_queryAll_run_bind_of_perm`), and a fresh typed answer completed
by a fresh private value is a fresh value of the single oracle
(`RandomOracleEncoding.evalDist_bind_complete`), which holds whenever every value of `M` splits
into a typed answer and a tail (`RandomOracleEncoding.ofSplit`).

## Main statements

- `OracleComp.RandomOracleEncoding`: an encoding of typed oracles into one oracle, with
  truncation, completion and the routing of raw inputs; `RandomOracleEncoding.ofSplit` builds one
  from a splitting of the single oracle's values.
- `RandomOracleEncoding.singleImpl`, `RandomOracleEncoding.typedImpl`: the single-oracle and the
  typed world.
- `RandomOracleEncoding.Clash`: two cached typed points share an encoding; a clash has a cached
  point that `route` does not read back from its encoding
  (`RandomOracleEncoding.Clash.exists_route_ne`).
- `RandomOracleEncoding.prEvent_simulateQ_singleImpl_run_le`: the single-oracle world is bounded
  by the typed world or a clash; `RandomOracleEncoding.prEvent_simulateQ_romImpl_encodeImpl_run_le`
  is the same statement for the random oracle model of the single oracle after the encoding.
-/

public section

open OracleComp OracleSpec MeasureTheory

namespace OracleComp

/-- An encoding of a family of typed random oracles `spec` into one random oracle `D →ₒ M`.

A typed point `t` is encoded as the input `encode t` of the single oracle, and its typed answer
is the truncation `trunc t` of the `M`-valued answer there. Completing a typed answer `r` with a
value `p` of `M`, `complete t r p`, keeps what `trunc t` reads from `r` and the rest from `p`;
a uniform typed answer completed with an independent uniform value is a uniform value of `M`
whose truncation is the typed answer (`evalDist_bind_complete`). The partial map `route` reads a
raw input `x` as the typed point it encodes: it is defined on every encoding, and a typed point it
returns encodes `x`. -/
structure RandomOracleEncoding {ι : Type} (spec : OracleSpec ι) (D M : Type) [SampleableType M]
    [∀ t, SampleableType (spec.Range t)] where
  /-- The input of the single oracle that encodes a typed point. -/
  encode : ι → D
  /-- The typed answer read off a value of the single oracle. -/
  trunc : (t : ι) → M → spec.Range t
  /-- A value of the single oracle carrying a typed answer, completed from another value. -/
  complete : (t : ι) → spec.Range t → M → M
  /-- The typed point that a raw input of the single oracle is read as, if any. -/
  route : D → Option ι
  encode_eq_of_route_eq_some {x : D} {t : ι} : route x = some t → encode t = x
  isSome_route_encode (t : ι) : (route (encode t)).isSome
  trunc_complete (t : ι) (r : spec.Range t) (p : M) : trunc t (complete t r p) = r
  evalDist_bind_complete (t : ι) {γ : Type} [MeasurableSpace γ]
    (f : spec.Range t → M → ProbComp γ) :
    𝒟[do let r ← $ᵗ spec.Range t; let p ← $ᵗ M; f r (complete t r p)] =
      𝒟[do let w ← $ᵗ M; f (trunc t w) w]

namespace RandomOracleEncoding

variable {ι D M : Type} {spec : OracleSpec ι} [SampleableType M]
  [∀ t, SampleableType (spec.Range t)]

/-- The encoding of `spec` into `D →ₒ M` by `encode` and `route` in which every value of `M`
splits, for each typed point `t`, into a typed answer at `t` and a tail in `Tail t`: truncating
takes the typed answer, and completing a typed answer joins it to the tail of the completing
value. -/
@[expose] noncomputable def ofSplit {Tail : ι → Type} [∀ t, SampleableType (Tail t)]
    (encode : ι → D) (route : D → Option ι)
    (encode_eq_of_route_eq_some : ∀ {x t}, route x = some t → encode t = x)
    (isSome_route_encode : ∀ t, (route (encode t)).isSome)
    (split : (t : ι) → M ≃ spec.Range t × Tail t) : RandomOracleEncoding spec D M where
  encode := encode
  trunc t w := (split t w).1
  complete t r p := (split t).symm (r, (split t p).2)
  route := route
  encode_eq_of_route_eq_some := encode_eq_of_route_eq_some
  isSome_route_encode := isSome_route_encode
  trunc_complete t r p := by simp
  evalDist_bind_complete t _ _ f :=
    SampleableType.evalDist_uniformSample_bind_equiv_symm (split t) f

variable (E : RandomOracleEncoding spec D M)

/-! ## The single-oracle world -/

section single

variable [DecidableEq D]

/-- The typed oracles answered through the single random oracle: a typed point is the query at
its encoding, truncated. -/
@[expose] noncomputable def truncatedImpl :
    QueryImpl spec (StateT (D →ₒ M).QueryCache ProbComp) :=
  fun t ↦ E.trunc t <$> (D →ₒ M).randomOracle (E.encode t)

/-- The typed oracles and the raw inputs answered by the single random oracle. -/
@[expose] noncomputable def singleHashImpl :
    QueryImpl (spec + (D →ₒ M)) (StateT (D →ₒ M).QueryCache ProbComp) :=
  E.truncatedImpl + (D →ₒ M).randomOracle

/-- The single-oracle world: uniform sampling passes through, typed points and raw inputs are
answered by the single random oracle. -/
@[expose] noncomputable def singleImpl :
    QueryImpl (unifSpec + (spec + (D →ₒ M))) (StateT (D →ₒ M).QueryCache ProbComp) :=
  unifFwdImpl (D →ₒ M) + E.singleHashImpl

/-- The encoding as a program translation: a uniform query and a raw input are the same query of
`unifSpec + (D →ₒ M)`, and a typed point is the query of the single oracle at its encoding,
truncated. -/
@[expose] def encodeImpl :
    QueryImpl (unifSpec + (spec + (D →ₒ M))) (OracleComp (unifSpec + (D →ₒ M)))
  | .inl n => (query (spec := unifSpec + (D →ₒ M)) (.inl n) : OracleComp _ (Fin (n + 1)))
  | .inr (.inl t) => E.trunc t <$> (query (spec := unifSpec + (D →ₒ M)) (.inr (E.encode t)) :
      OracleComp _ M)
  | .inr (.inr x) => (query (spec := unifSpec + (D →ₒ M)) (.inr x) : OracleComp _ M)

variable {E}

/-- A typed query of the single-oracle world is the truncated query at its encoding. -/
theorem singleHashImpl_inl_run (t : ι) (b : (D →ₒ M).QueryCache) :
    (E.singleHashImpl (.inl t)).run b =
      (fun z ↦ (E.trunc t z.1, z.2)) <$> ((D →ₒ M).randomOracle (E.encode t)).run b := by
  simp only [singleHashImpl, QueryImpl.add_apply_inl, truncatedImpl, StateT.run_map]

/-- A raw input of the single-oracle world is the query of the single oracle. -/
theorem singleHashImpl_inr_run (x : D) (b : (D →ₒ M).QueryCache) :
    (E.singleHashImpl (.inr x)).run b = ((D →ₒ M).randomOracle x).run b := by
  simp only [singleHashImpl, QueryImpl.add_apply_inr]

/-- The single-oracle world is the random oracle model of the single oracle after the
encoding. -/
theorem romImpl_compose_encodeImpl : (D →ₒ M).romImpl ∘ₛ E.encodeImpl = E.singleImpl := by
  funext u
  rcases u with n | t | x
  · rfl
  · rfl
  · simp [encodeImpl, singleImpl, singleHashImpl]

/-- Running the encoding of a computation in the random oracle model of the single oracle is
running the computation in the single-oracle world. -/
theorem simulateQ_romImpl_simulateQ_encodeImpl {α : Type}
    (oa : OracleComp (unifSpec + (spec + (D →ₒ M))) α) :
    simulateQ (D →ₒ M).romImpl (simulateQ E.encodeImpl oa) = simulateQ E.singleImpl oa := by
  rw [← QueryImpl.simulateQ_compose, romImpl_compose_encodeImpl]

end single

/-! ## The typed world -/

section typed

variable [DecidableEq ι] [DecidableEq D]

/-- Independent lazy random oracles for the typed points and for a private table of the raw
inputs, on the pair of their caches. -/
@[expose] noncomputable def pairImpl : QueryImpl (spec + (D →ₒ M))
    (StateT (spec.QueryCache × (D →ₒ M).QueryCache) ProbComp) :=
  QueryImpl.parallelStateT spec.randomOracle (D →ₒ M).randomOracle

/-- The router: a raw input `x` draws its private value `p`; if `x` is read as a typed point `q`,
the answer is the typed answer at `q` completed from `p`, and otherwise it is `p`. -/
@[expose] noncomputable def routerImpl :
    QueryImpl (D →ₒ M) (StateT (spec.QueryCache × (D →ₒ M).QueryCache) ProbComp) :=
  fun x ↦ do
    let p ← (pairImpl (spec := spec) (D := D) (M := M) (.inr x) :
      StateT (spec.QueryCache × (D →ₒ M).QueryCache) ProbComp M)
    match E.route x with
    | some q => (E.complete q · p) <$> (pairImpl (D := D) (M := M) (.inl q) :
        StateT (spec.QueryCache × (D →ₒ M).QueryCache) ProbComp (spec.Range q))
    | none => pure p

/-- The typed oracles answered by independent lazy random oracles, and the raw inputs by the
router. -/
@[expose] noncomputable def typedHashImpl :
    QueryImpl (spec + (D →ₒ M)) (StateT (spec.QueryCache × (D →ₒ M).QueryCache) ProbComp) :=
  (fun t ↦ pairImpl (spec := spec) (D := D) (M := M) (.inl t)) + E.routerImpl

/-- The typed world: uniform sampling passes through, typed points are answered by independent
lazy random oracles and raw inputs by the router. -/
@[expose] noncomputable def typedImpl : QueryImpl (unifSpec + (spec + (D →ₒ M)))
    (StateT (spec.QueryCache × (D →ₒ M).QueryCache) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (spec.QueryCache × (D →ₒ M).QueryCache) ProbComp) + E.typedHashImpl

variable {E}

/-- A typed query of the typed world queries the typed lazy random oracle on the typed cache. -/
theorem typedHashImpl_inl_run (t : ι) (s : spec.QueryCache × (D →ₒ M).QueryCache) :
    (E.typedHashImpl (.inl t)).run s =
      (fun z ↦ (z.1, (z.2, s.2))) <$> (spec.randomOracle t).run s.1 := by
  obtain ⟨c, pv⟩ := s
  rfl

/-- A raw input of the typed world draws its private value, then completes the typed answer at the
typed point it is read as, if any. -/
theorem typedHashImpl_inr_run (x : D) (s : spec.QueryCache × (D →ₒ M).QueryCache) :
    (E.typedHashImpl (.inr x)).run s =
      ((D →ₒ M).randomOracle x).run s.2 >>= fun z ↦ match E.route x with
        | some q => (fun y ↦ (E.complete q y.1 z.1, (y.2, z.2))) <$>
            (spec.randomOracle q).run s.1
        | none => pure (z.1, (s.1, z.2)) := by
  obtain ⟨c, pv⟩ := s
  simp only [typedHashImpl, QueryImpl.add_apply_inr, routerImpl, StateT.run_bind]
  change ((fun z ↦ (z.1, (c, z.2))) <$> ((D →ₒ M).randomOracle x).run pv) >>= _ = _
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  refine bind_congr fun z ↦ ?_
  cases E.route x with
  | some q =>
    simp only [StateT.run_bind, Function.comp_apply, StateT.run_pure]
    change ((fun y ↦ (y.1, (y.2, z.2))) <$> (spec.randomOracle q).run c) >>= _ = _
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
    rfl
  | none => rfl

/-- On a uniform query the typed world is the random oracle model of `spec`, with the table of
private values passive. -/
theorem typedImpl_inl_run (n : ℕ) (c : spec.QueryCache) (pv : (D →ₒ M).QueryCache) :
    (E.typedImpl (.inl n)).run (c, pv) =
      (fun z ↦ (z.1, (z.2, pv))) <$> (spec.romImpl (.inl n)).run c := by
  simp [typedImpl, OracleSpec.romImpl, unifFwdImpl]

/-- On a typed query the typed world is the random oracle model of `spec`, with the table of
private values passive. -/
theorem typedImpl_inr_inl_run (t : ι) (c : spec.QueryCache) (pv : (D →ₒ M).QueryCache) :
    (E.typedImpl (.inr (.inl t))).run (c, pv) =
      (fun z ↦ (z.1, (z.2, pv))) <$> (spec.romImpl (.inr t)).run c :=
  typedHashImpl_inl_run (E := E) t (c, pv)

end typed

/-! ## Clashes and the single-oracle view of a typed state -/

/-- Two distinct cached typed points share an encoding. -/
@[expose] def Clash (c : spec.QueryCache) : Prop :=
  ∃ q q', q ≠ q' ∧ (c q).isSome ∧ (c q').isSome ∧ E.encode q = E.encode q'

/-- Some cached typed point is encoded as `x`. -/
@[expose] def Covered (c : spec.QueryCache) (x : D) : Prop :=
  ∃ q, E.encode q = x ∧ (c q).isSome

open Classical in
/-- The single-oracle cache that a typed cache `c` and a table `pv` describe: at a tabulated
input covered by a cached typed point, the typed answer completed from the tabulated value, and
at any other tabulated input, the tabulated value. Without a clash at most one cached typed point
covers an input; with a clash the covering point is an arbitrary choice among them. -/
noncomputable def singleView (c : spec.QueryCache) (pv : (D →ₒ M).QueryCache) :
    (D →ₒ M).QueryCache :=
  .ofFn fun x ↦ (pv x).map fun p ↦
    if h : E.Covered c x then ((c h.choose).map fun r ↦ E.complete h.choose r p).getD p else p

section view

variable {E}

/-- A clash survives any change of the typed cache that keeps every cached point cached. -/
theorem Clash.mono {c c' : spec.QueryCache} (h : ∀ q, (c q).isSome → (c' q).isSome)
    (hc : E.Clash c) : E.Clash c' := by
  obtain ⟨q, q', hne, hq, hq', he⟩ := hc
  exact ⟨q, q', hne, h q hq, h q' hq', he⟩

/-- A clash has a cached point that `route` does not read back from its encoding, and another
cached point with the same encoding: `route` reads back at most one point of an encoding. -/
theorem Clash.exists_route_ne {c : spec.QueryCache} (hc : E.Clash c) :
    ∃ q q', q ≠ q' ∧ (c q).isSome ∧ (c q').isSome ∧ E.encode q = E.encode q' ∧
      E.route (E.encode q) ≠ some q := by
  obtain ⟨q, q', hne, hq, hq', he⟩ := hc
  by_cases hfix : E.route (E.encode q) = some q
  · refine ⟨q', q, hne.symm, hq', hq, he.symm, fun hfix' => hne ?_⟩
    exact Option.some.inj (hfix.symm.trans ((congrArg E.route he).trans hfix'))
  · exact ⟨q, q', hne, hq, hq', he, hfix⟩

/-- The single view at an input no cached typed point encodes is the table entry. -/
theorem singleView_apply_of_not_covered {c : spec.QueryCache} {pv : (D →ₒ M).QueryCache} {x : D}
    (h : ¬E.Covered c x) : E.singleView c pv x = pv x := by
  simp [singleView, h]

/-- Without a clash, the single view at the encoding of a cached typed point is the table entry
completed by its typed answer. -/
theorem singleView_apply_encode {c : spec.QueryCache} {pv : (D →ₒ M).QueryCache} {q : ι}
    {r : spec.Range q} (hc : ¬E.Clash c) (hq : c q = some r) :
    E.singleView c pv (E.encode q) = (pv (E.encode q)).map (E.complete q r) := by
  have hcov : E.Covered c (E.encode q) := ⟨q, rfl, by simp [hq]⟩
  simp only [singleView, QueryCache.ofFn_apply, hcov, ↓reduceDIte]
  congr 1
  funext p
  have key : ∀ q', E.encode q' = E.encode q → (c q').isSome →
      ((c q').map fun r' ↦ E.complete q' r' p).getD p = E.complete q r p := by
    intro q' he hs
    by_cases hne : q' = q
    · subst hne
      simp [hq]
    · exact absurd ⟨q', q, hne, hs, by simp [hq], he⟩ hc
  exact key _ hcov.choose_spec.1 hcov.choose_spec.2

/-- The inputs the fill queries are the encodings covered by cached typed points. -/
theorem mem_map_encode_toList_iff {c : spec.QueryCache} (hf : {q | (c q).isSome}.Finite)
    (x : D) : x ∈ hf.toFinset.toList.map E.encode ↔ E.Covered c x := by
  simp only [List.mem_map, Finset.mem_toList, Set.Finite.mem_toFinset, Set.mem_ofPred_eq,
    Covered]
  exact ⟨fun ⟨q, hq, he⟩ ↦ ⟨q, he, hq⟩, fun ⟨q, he, hq⟩ ↦ ⟨q, hq, he⟩⟩

end view

/-! ## Recording a typed point -/

section mark

variable [DecidableEq ι]

/-- The step of the typed world at `u` caches a new typed point whose encoding is already
covered. -/
def Collides (c : spec.QueryCache) : (spec + (D →ₒ M)).Domain → Prop
  | .inl t => c t = none ∧ E.Covered c (E.encode t)
  | .inr x => ∃ q, E.route x = some q ∧ c q = none ∧ E.Covered c x

/-- The typed cache after a step at `u` answered by `a`, recording the typed point that the step
of the typed world would cache. -/
def mark (c : spec.QueryCache) :
    (u : (spec + (D →ₒ M)).Domain) → (spec + (D →ₒ M)).Range u → spec.QueryCache
  | .inl t, a => c.cacheQuery t a
  | .inr x, a => match E.route x with
    | some q => c.cacheQuery q (E.trunc q a)
    | none => c

variable {E}

/-- Caching a new typed point whose encoding is covered creates a clash. -/
theorem clash_cacheQuery_of_covered {c : spec.QueryCache} {q : ι} (hq : c q = none)
    (hcov : E.Covered c (E.encode q)) (r : spec.Range q) : E.Clash (c.cacheQuery q r) := by
  obtain ⟨q', he, hq'⟩ := hcov
  have hne : q' ≠ q := by rintro rfl; simp [hq] at hq'
  refine ⟨q', q, hne, ?_, by simp, he⟩
  rwa [QueryCache.cacheQuery_of_ne _ _ hne]

/-- Caching a typed point whose encoding is not covered creates no clash. -/
theorem not_clash_cacheQuery {c : spec.QueryCache} {q : ι} (hc : ¬E.Clash c)
    (hcov : ¬E.Covered c (E.encode q)) (r : spec.Range q) : ¬E.Clash (c.cacheQuery q r) := by
  rintro ⟨q₁, q₂, hne, h₁, h₂, he⟩
  rw [QueryCache.isSome_cacheQuery_apply_iff] at h₁ h₂
  rcases h₁ with rfl | h₁ <;> rcases h₂ with rfl | h₂
  · exact hne rfl
  · exact hcov ⟨q₂, he.symm, h₂⟩
  · exact hcov ⟨q₁, he, h₁⟩
  · exact hc ⟨q₁, q₂, hne, h₁, h₂, he⟩

/-- Recording a step keeps every cached typed point cached. -/
theorem isSome_mark {c : spec.QueryCache} {u : (spec + (D →ₒ M)).Domain}
    (a : (spec + (D →ₒ M)).Range u) {q : ι} (hq : (c q).isSome) : (E.mark c u a q).isSome := by
  rcases u with t | x
  · simp [mark, QueryCache.isSome_cacheQuery_apply_iff, hq]
  · simp only [mark]
    cases E.route x <;> simp [QueryCache.isSome_cacheQuery_apply_iff, hq]

/-- Recording a step that creates a clash, or any step from a state with a clash, leaves a
clash. -/
theorem clash_mark {c : spec.QueryCache} {u : (spec + (D →ₒ M)).Domain}
    (h : E.Clash c ∨ E.Collides c u) (a : (spec + (D →ₒ M)).Range u) :
    E.Clash (E.mark c u a) := by
  rcases h with h | h
  · exact h.mono fun q hq ↦ isSome_mark a hq
  · rcases u with t | x
    · exact clash_cacheQuery_of_covered h.1 h.2 a
    · obtain ⟨q, hr, hq, hcov⟩ := h
      obtain rfl := E.encode_eq_of_route_eq_some hr
      simp only [mark, hr]
      exact clash_cacheQuery_of_covered hq hcov _

/-- Recording a step keeps finitely many typed points cached. -/
theorem finite_mark {c : spec.QueryCache} (hf : {q | (c q).isSome}.Finite)
    (u : (spec + (D →ₒ M)).Domain) (a : (spec + (D →ₒ M)).Range u) :
    {q | (E.mark c u a q).isSome}.Finite := by
  have hins : ∀ (t : ι) (r : spec.Range t), {q | ((c.cacheQuery t r) q).isSome}.Finite :=
    fun t _ ↦ (hf.insert t).subset fun q hq ↦ by
      simp only [Set.mem_ofPred_eq, QueryCache.isSome_cacheQuery_apply_iff] at hq
      simpa using hq
  rcases u with t | x
  · exact hins t a
  · simp only [mark]
    cases E.route x with
    | some q => exact hins q _
    | none => exact hf

end mark

/-! ## The fill -/

section fill

variable [DecidableEq D]

open Classical in
/-- The single-oracle cache of a typed state, drawing what the typed state leaves open. Without a
clash and with finitely many cached typed points, the table is queried, as a lazy random oracle,
at the encoding of each cached typed point, and the result is read through `singleView`; with a
clash the table is the single-oracle cache itself. A typed state with infinitely many cached
typed points has no finite fill, and its fill is the empty cache; such states are outside the
invariant `StateInv` on which the fill is used. -/
noncomputable def fill (s : spec.QueryCache × (D →ₒ M).QueryCache) :
    ProbComp (D →ₒ M).QueryCache :=
  if E.Clash s.1 then pure s.2 else
    if h : {q | (s.1 q).isSome}.Finite then
      (fun w ↦ E.singleView s.1 w.2) <$> (simulateQ (D →ₒ M).randomOracle
        ((D →ₒ M).queryAll (h.toFinset.toList.map E.encode))).run s.2
    else pure ∅

variable {E}

/-- Tabulating an input no cached typed point encodes tabulates it in the single view. -/
theorem singleView_cacheQuery_of_not_covered {c : spec.QueryCache} {pv : (D →ₒ M).QueryCache}
    {x : D} (h : ¬E.Covered c x) (p : M) :
    E.singleView c (pv.cacheQuery x p) = (E.singleView c pv).cacheQuery x p := by
  refine QueryCache.ext fun x' ↦ ?_
  by_cases hx : x' = x
  · subst hx
    rw [singleView_apply_of_not_covered h]
    simp
  · simp [singleView, QueryCache.cacheQuery_of_ne _ _ hx]

/-- At an input no cached typed point encodes, querying the single oracle on the single view is
querying the table and reading the result through the single view. -/
theorem randomOracle_run_singleView {c : spec.QueryCache} {pv : (D →ₒ M).QueryCache} {x : D}
    (h : ¬E.Covered c x) :
    ((D →ₒ M).randomOracle x).run (E.singleView c pv) =
      (fun z ↦ (z.1, E.singleView c z.2)) <$> ((D →ₒ M).randomOracle x).run pv := by
  rw [_root_.randomOracle.run_eq, _root_.randomOracle.run_eq, singleView_apply_of_not_covered h]
  cases pv x with
  | some p => simp
  | none => simp [singleView_cacheQuery_of_not_covered h]

/-- The fill of a typed state with a clash is its table. -/
theorem fill_of_clash {c : spec.QueryCache} {pv : (D →ₒ M).QueryCache} (h : E.Clash c) :
    E.fill (c, pv) = pure pv := by
  simp [fill, h]

/-- The fill of a typed state without a clash and with finitely many cached typed points queries
the table at their encodings and reads the result through the single view. -/
theorem fill_of_not_clash {c : spec.QueryCache} {pv : (D →ₒ M).QueryCache} (h : ¬E.Clash c)
    (hf : {q | (c q).isSome}.Finite) :
    E.fill (c, pv) = (fun w ↦ E.singleView c w.2) <$> (simulateQ (D →ₒ M).randomOracle
      ((D →ₒ M).queryAll (hf.toFinset.toList.map E.encode))).run pv := by
  simp only [fill, h, hf, ↓reduceIte, ↓reduceDIte]

/-- The fill of the empty typed state is the empty cache. -/
theorem fill_empty : E.fill (∅, ∅) = pure ∅ := by
  have hc : ¬E.Clash (∅ : spec.QueryCache) := by
    rintro ⟨q, _, _, hq, _⟩
    simp at hq
  have hf : {q | ((∅ : spec.QueryCache) q).isSome}.Finite := by simp
  rw [fill_of_not_clash hc hf]
  have h0 : hf.toFinset = ∅ := by simp
  simp only [h0, Finset.toList_empty, List.map_nil, OracleSpec.queryAll_nil, simulateQ_pure,
    StateT.run_pure, map_pure]
  exact congrArg pure (QueryCache.ext fun x ↦ by simp [singleView])

/-- After the fill's queries, the encoding of every cached typed point is tabulated. -/
theorem isSome_apply_encode_of_mem_support_queryAll {c : spec.QueryCache}
    {pv : (D →ₒ M).QueryCache} (hf : {q | (c q).isSome}.Finite) {w : Unit × (D →ₒ M).QueryCache}
    (hw : w ∈ support ((simulateQ (D →ₒ M).randomOracle
      ((D →ₒ M).queryAll (hf.toFinset.toList.map E.encode))).run pv))
    {q : ι} (hq : (c q).isSome) : (w.2 (E.encode q)).isSome :=
  ((QueryImpl.withCaching_queryAll_le_and_isSome_iff _ hw).2 _).2
    (.inr ((mem_map_encode_toList_iff hf _).2 ⟨q, rfl, hq⟩))

end fill

/-! ## The patched typed world and the intertwining -/

section intertwining

variable [DecidableEq ι] [DecidableEq D]

open Classical in
/-- The typed world patched to follow the single-oracle world through `fill` on the steps that
create a clash and from states with a clash: such a step fills the single-oracle cache, takes the
step of the single-oracle world there, keeps the filled cache as its table and records the queried
typed point. -/
noncomputable def patchedHashImpl :
    QueryImpl (spec + (D →ₒ M)) (StateT (spec.QueryCache × (D →ₒ M).QueryCache) ProbComp) :=
  fun u ↦ StateT.mk fun s ↦
    if E.Clash s.1 ∨ E.Collides s.1 u then do
      let b ← E.fill s
      let z ← (E.singleHashImpl u).run b
      pure (z.1, (E.mark s.1 u z.1, z.2))
    else (E.typedHashImpl u).run s

/-- The patched typed world on the whole interface. -/
noncomputable def patchedImpl : QueryImpl (unifSpec + (spec + (D →ₒ M)))
    (StateT (spec.QueryCache × (D →ₒ M).QueryCache) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (spec.QueryCache × (D →ₒ M).QueryCache) ProbComp) + E.patchedHashImpl

/-- The invariant of the patched typed world: finitely many typed points are cached, and without
a clash every tabulated raw input read as a typed point has that point cached. -/
def StateInv (s : spec.QueryCache × (D →ₒ M).QueryCache) : Prop :=
  {q | (s.1 q).isSome}.Finite ∧
    (¬E.Clash s.1 → ∀ x, (s.2 x).isSome → ∀ q, E.route x = some q → (s.1 q).isSome)

variable {E}

/-- A step of the typed world records exactly the queried typed point in the typed cache, and
tabulates at most the queried raw input. -/
theorem mem_support_typedHashImpl_run {u : (spec + (D →ₒ M)).Domain} {c : spec.QueryCache}
    {pv : (D →ₒ M).QueryCache}
    {z : (spec + (D →ₒ M)).Range u × (spec.QueryCache × (D →ₒ M).QueryCache)}
    (hz : z ∈ support ((E.typedHashImpl u).run (c, pv))) :
    z.2.1 = E.mark c u z.1 ∧ ∀ x, (z.2.2 x).isSome → (pv x).isSome ∨ u = .inr x := by
  rcases u with t | x
  · rw [typedHashImpl_inl_run, support_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact ⟨QueryImpl.withCaching_run_eq_cacheQuery _ hy, fun _ hx ↦ .inl hx⟩
  · rw [typedHashImpl_inr_run, mem_support_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    have htab : ∀ x', (y.2 x').isSome → (pv x').isSome ∨ (.inr x : ι ⊕ D) = .inr x' :=
      fun x' hx' ↦ ((QueryImpl.withCaching_run_isSome_apply_iff _ hy x').1 hx').imp_right
        fun h ↦ by rw [h]
    cases hr : E.route x with
    | none =>
      rw [hr, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨by simp [mark, hr], htab⟩
    | some q =>
      rw [hr, support_map] at hz
      obtain ⟨y', hy', rfl⟩ := hz
      refine ⟨?_, htab⟩
      simp only [mark, hr, E.trunc_complete]
      exact QueryImpl.withCaching_run_eq_cacheQuery _ hy'

/-- Without a clash, caching a typed point `q` with an uncovered encoding and tabulating its
encoding tabulates there, in the single view, the typed answer completed from the table entry. -/
theorem singleView_cacheQuery_cacheQuery {c : spec.QueryCache} {pv : (D →ₒ M).QueryCache}
    {q : ι} (hc : ¬E.Clash c) (hcov : ¬E.Covered c (E.encode q)) (r : spec.Range q) (p : M) :
    E.singleView (c.cacheQuery q r) (pv.cacheQuery (E.encode q) p) =
      (E.singleView c pv).cacheQuery (E.encode q) (E.complete q r p) := by
  have hc' := not_clash_cacheQuery hc hcov r
  refine QueryCache.ext fun x ↦ ?_
  by_cases hx : x = E.encode q
  · subst hx
    rw [singleView_apply_encode hc' (QueryCache.cacheQuery_self _ _ _)]
    simp
  · rw [QueryCache.cacheQuery_of_ne _ _ hx]
    by_cases hx' : E.Covered c x
    · obtain ⟨q', rfl, hs⟩ := hx'
      obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.1 hs
      have hne : q' ≠ q := by rintro rfl; exact hx rfl
      rw [singleView_apply_encode hc' (r := r') (by rwa [QueryCache.cacheQuery_of_ne _ _ hne]),
        singleView_apply_encode hc hr', QueryCache.cacheQuery_of_ne _ _ hx]
    · have hx'' : ¬E.Covered (c.cacheQuery q r) x := by
        rintro ⟨q', he, hs⟩
        rw [QueryCache.isSome_cacheQuery_apply_iff] at hs
        rcases hs with rfl | hs
        · exact hx he.symm
        · exact hx' ⟨q', he, hs⟩
      rw [singleView_apply_of_not_covered hx'', singleView_apply_of_not_covered hx',
        QueryCache.cacheQuery_of_ne _ _ hx]

/-- Caching a typed point `q` with an uncovered encoding fills by querying the table at the
encoding of `q` first and then at the encodings of the other cached typed points. -/
theorem evalDist_fill_cacheQuery_bind {c : spec.QueryCache} {pv : (D →ₒ M).QueryCache} {q : ι}
    (hc : ¬E.Clash c) (hf : {q | (c q).isSome}.Finite) (hcov : ¬E.Covered c (E.encode q))
    (r : spec.Range q) {γ : Type} [MeasurableSpace γ] (g : (D →ₒ M).QueryCache → ProbComp γ) :
    𝒟[E.fill (c.cacheQuery q r, pv) >>= g] =
      𝒟[((D →ₒ M).randomOracle (E.encode q)).run pv >>= fun z ↦
        (simulateQ (D →ₒ M).randomOracle ((D →ₒ M).queryAll (hf.toFinset.toList.map E.encode))).run
          z.2 >>= fun w ↦ g (E.singleView (c.cacheQuery q r) w.2)] := by
  have hq : c q = none := by
    cases hcq : c q with
    | none => rfl
    | some _ => exact absurd ⟨q, rfl, by simp [hcq]⟩ hcov
  have hf' : {q' | ((c.cacheQuery q r) q').isSome}.Finite := by
    refine (hf.insert q).subset fun q' hq' ↦ ?_
    simp only [Set.mem_ofPred_eq, QueryCache.isSome_cacheQuery_apply_iff] at hq'
    simpa using hq'
  have hset : hf'.toFinset = insert q hf.toFinset := by
    ext q'
    simp [QueryCache.isSome_cacheQuery_apply_iff]
  have hperm : (hf'.toFinset.toList.map E.encode).Perm
      (E.encode q :: hf.toFinset.toList.map E.encode) := by
    rw [hset, ← List.map_cons]
    exact (Finset.toList_insert (by simp [hq])).map _
  rw [fill_of_not_clash (not_clash_cacheQuery hc hcov r) hf', bind_map_left]
  refine (_root_.randomOracle.evalDist_simulateQ_queryAll_run_bind_of_perm hperm pv
    fun b ↦ g (E.singleView (c.cacheQuery q r) b)).trans ?_
  simp only [OracleSpec.queryAll_cons, simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
    OracleQuery.input_query, id_map, StateT.run_bind, bind_assoc]

/-- A fresh typed answer at a point `q` with an uncovered encoding, a fresh table entry there and
the fill of the other cached typed points, read through the single view, are the fill followed by
a fresh value of the single oracle at the encoding of `q`, truncated to the typed answer. -/
private theorem evalDist_fresh {c : spec.QueryCache} {pv : (D →ₒ M).QueryCache} {q : ι}
    (hc : ¬E.Clash c) (hf : {q | (c q).isSome}.Finite)
    (hraw : ∀ x, (pv x).isSome → ∀ q, E.route x = some q → (c q).isSome)
    (hcov : ¬E.Covered c (E.encode q)) {γ : Type} [MeasurableSpace γ]
    (g : spec.Range q → M → (D →ₒ M).QueryCache → ProbComp γ) :
    𝒟[$ᵗ spec.Range q >>= fun r ↦ ((D →ₒ M).randomOracle (E.encode q)).run pv >>= fun z ↦
      (simulateQ (D →ₒ M).randomOracle ((D →ₒ M).queryAll (hf.toFinset.toList.map E.encode))).run
        z.2 >>= fun w ↦ g r (E.complete q r z.1) (E.singleView (c.cacheQuery q r) w.2)] =
    𝒟[E.fill (c, pv) >>= fun b ↦ ((D →ₒ M).randomOracle (E.encode q)).run b >>= fun z ↦
      g (E.trunc q z.1) z.1 z.2] := by
  have hpv : pv (E.encode q) = none := by
    obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.1 (E.isSome_route_encode q)
    cases hx : pv (E.encode q) with
    | none => rfl
    | some _ => exact absurd ⟨q', E.encode_eq_of_route_eq_some hq',
        hraw _ (by simp [hx]) q' hq'⟩ hcov
  rw [fill_of_not_clash hc hf, bind_map_left]
  calc _ = 𝒟[$ᵗ spec.Range q >>= fun r ↦ (simulateQ (D →ₒ M).randomOracle
          ((D →ₒ M).queryAll (hf.toFinset.toList.map E.encode))).run pv >>= fun w ↦
            ((D →ₒ M).randomOracle (E.encode q)).run w.2 >>= fun z ↦
              g r (E.complete q r z.1) (E.singleView (c.cacheQuery q r) z.2)] :=
        evalDist_bind_congr_of_support _ _ _ fun r _ ↦
          _root_.randomOracle.evalDist_run_bind_simulateQ_run_swap (E.encode q) _ pv
            fun p _ b ↦ g r (E.complete q r p) (E.singleView (c.cacheQuery q r) b)
    _ = 𝒟[(simulateQ (D →ₒ M).randomOracle
          ((D →ₒ M).queryAll (hf.toFinset.toList.map E.encode))).run pv >>= fun w ↦
            $ᵗ spec.Range q >>= fun r ↦ ((D →ₒ M).randomOracle (E.encode q)).run w.2 >>= fun z ↦
              g r (E.complete q r z.1) (E.singleView (c.cacheQuery q r) z.2)] :=
        OracleComp.evalDist_bind_bind_swap _ _ _
    _ = _ := evalDist_bind_congr_of_support _ _ _ fun w hw ↦ by
        have hwx : w.2 (E.encode q) = none := by
          rw [QueryImpl.withCaching_queryAll_apply_of_not_mem _ hw
            (by rwa [mem_map_encode_toList_iff]), hpv]
        simp only [_root_.randomOracle.run_eq, singleView_apply_of_not_covered hcov, hwx,
          bind_assoc, pure_bind, singleView_cacheQuery_cacheQuery hc hcov]
        exact E.evalDist_bind_complete q fun r v ↦
          g r v ((E.singleView c w.2).cacheQuery (E.encode q) v)

/-- Without a clash and away from the steps that create one, a step of the typed world followed
by the fill has the distribution of the fill followed by the step of the single-oracle world. -/
private theorem evalDist_typedHashImpl_run_bind_fill {c : spec.QueryCache}
    {pv : (D →ₒ M).QueryCache} (hc : ¬E.Clash c) (hf : {q | (c q).isSome}.Finite)
    (hraw : ∀ x, (pv x).isSome → ∀ q, E.route x = some q → (c q).isSome)
    (u : (spec + (D →ₒ M)).Domain) (hcol : ¬E.Collides c u) {γ : Type} [MeasurableSpace γ]
    (f : (spec + (D →ₒ M)).Range u → (D →ₒ M).QueryCache → ProbComp γ) :
    𝒟[(E.typedHashImpl u).run (c, pv) >>= fun z ↦ E.fill z.2 >>= f z.1] =
      𝒟[E.fill (c, pv) >>= fun b ↦ (E.singleHashImpl u).run b >>= fun z ↦ f z.1 z.2] := by
  rcases u with t | x
  · simp only [typedHashImpl_inl_run, singleHashImpl_inl_run, bind_map_left]
    rw [_root_.randomOracle.run_eq]
    cases hct : c t with
    | some r =>
      simp only [pure_bind, fill_of_not_clash hc hf, bind_map_left]
      refine evalDist_bind_congr_of_support _ _ _ fun w hw ↦ ?_
      obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1
        (isSome_apply_encode_of_mem_support_queryAll hf hw (q := t) (by simp [hct]))
      rw [_root_.randomOracle.run_eq, singleView_apply_encode hc hct, hp]
      simp [E.trunc_complete]
    | none =>
      simp only [bind_assoc, pure_bind]
      refine (evalDist_bind_congr_of_support _ _ _ fun r _ ↦
        evalDist_fill_cacheQuery_bind hc hf (fun h ↦ hcol ⟨hct, h⟩) r (f r)).trans ?_
      exact evalDist_fresh hc hf hraw (fun h ↦ hcol ⟨hct, h⟩) fun r _ b ↦ f r b
  · simp only [typedHashImpl_inr_run, singleHashImpl_inr_run]
    cases hr : E.route x with
    | none =>
      have hcov : ¬E.Covered c x := by
        rintro ⟨q, rfl, _⟩
        simpa [hr] using E.isSome_route_encode q
      simp only [bind_assoc, pure_bind, fill_of_not_clash hc hf, bind_map_left]
      rw [_root_.randomOracle.evalDist_run_bind_simulateQ_run_swap x _ pv
        fun p _ b ↦ f p (E.singleView c b)]
      refine evalDist_bind_congr_of_support _ _ _ fun w _ ↦ ?_
      rw [randomOracle_run_singleView hcov, bind_map_left]
    | some q =>
      obtain rfl := E.encode_eq_of_route_eq_some hr
      dsimp only
      rw [_root_.randomOracle.run_eq (spec₀ := spec) q c]
      cases hcq : c q with
      | some r =>
        simp only [map_pure, bind_assoc, pure_bind, fill_of_not_clash hc hf, bind_map_left]
        rw [_root_.randomOracle.evalDist_run_bind_simulateQ_run_swap (E.encode q) _ pv
          fun p _ b ↦ f (E.complete q r p) (E.singleView c b)]
        refine evalDist_bind_congr_of_support _ _ _ fun w hw ↦ ?_
        obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1
          (isSome_apply_encode_of_mem_support_queryAll hf hw (q := q) (by simp [hcq]))
        rw [_root_.randomOracle.run_eq, _root_.randomOracle.run_eq,
          singleView_apply_encode hc hcq, hp]
        simp
      | none =>
        have hcov : ¬E.Covered c (E.encode q) := fun h ↦ hcol ⟨q, hr, hcq, h⟩
        simp only [map_bind, map_pure, bind_assoc, pure_bind]
        calc _ = 𝒟[((D →ₒ M).randomOracle (E.encode q)).run pv >>= fun z ↦
              $ᵗ spec.Range q >>= fun r ↦ (simulateQ (D →ₒ M).randomOracle
                ((D →ₒ M).queryAll (hf.toFinset.toList.map E.encode))).run z.2 >>= fun w ↦
                  f (E.complete q r z.1) (E.singleView (c.cacheQuery q r) w.2)] := by
              refine evalDist_bind_congr_of_support _ _ _ fun z hz ↦ ?_
              refine evalDist_bind_congr_of_support _ _ _ fun r _ ↦ ?_
              rw [evalDist_fill_cacheQuery_bind hc hf hcov r,
                QueryImpl.withCaching_run_some _ (QueryImpl.withCaching_run_caches _ _ _ _ hz),
                pure_bind]
          _ = 𝒟[$ᵗ spec.Range q >>= fun r ↦
              ((D →ₒ M).randomOracle (E.encode q)).run pv >>= fun z ↦
                (simulateQ (D →ₒ M).randomOracle
                  ((D →ₒ M).queryAll (hf.toFinset.toList.map E.encode))).run z.2 >>= fun w ↦
                    f (E.complete q r z.1) (E.singleView (c.cacheQuery q r) w.2)] :=
              OracleComp.evalDist_bind_bind_swap _ _ _
          _ = _ := evalDist_fresh hc hf hraw hcov fun _ v b ↦ f v b

variable (E)

/-- **The fill intertwines the patched typed world with the single-oracle world** on the states
satisfying `StateInv`. -/
theorem intertwinesOn_fill_patchedImpl_singleImpl :
    QueryImpl.IntertwinesOn E.StateInv E.fill E.patchedImpl E.singleImpl := by
  rintro u ⟨c, pv⟩ ⟨hf, hraw⟩ γ _ f
  rcases u with n | u
  · simp only [patchedImpl, singleImpl, unifFwdImpl, QueryImpl.add_apply_inl,
      QueryImpl.liftTarget_apply_run, bind_map_left]
    exact OracleComp.evalDist_bind_bind_swap _ _ _
  · simp only [patchedImpl, singleImpl, QueryImpl.add_apply_inr, patchedHashImpl, StateT.run_mk]
    by_cases hb : E.Clash c ∨ E.Collides c u
    · have hfc : ∀ a b, E.fill (E.mark c u a, b) = pure b :=
        fun a _ ↦ fill_of_clash (clash_mark hb a)
      simp only [hb, ↓reduceIte, bind_assoc, pure_bind, hfc]
      rfl
    · simp only [hb, ↓reduceIte]
      obtain ⟨hc, hcol⟩ := not_or.1 hb
      exact evalDist_typedHashImpl_run_bind_fill hc hf (hraw hc) u hcol f

/-- The patched typed world preserves `StateInv`. -/
theorem preservesInv_patchedImpl_stateInv : QueryImpl.PreservesInv E.patchedImpl E.StateInv := by
  rintro (n | u) ⟨c, pv⟩ ⟨hf, hraw⟩ z hz
  · simp only [patchedImpl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply_run,
      support_map] at hz
    obtain ⟨_, _, rfl⟩ := hz
    exact ⟨hf, hraw⟩
  · simp only [patchedImpl, QueryImpl.add_apply_inr, patchedHashImpl, StateT.run_mk] at hz
    by_cases hb : E.Clash c ∨ E.Collides c u
    · simp only [hb, ↓reduceIte, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hz
      obtain ⟨_, _, _, _, rfl⟩ := hz
      exact ⟨finite_mark hf u _, fun h ↦ absurd (clash_mark hb _) h⟩
    · simp only [hb, ↓reduceIte] at hz
      obtain ⟨hmark, htab⟩ := mem_support_typedHashImpl_run hz
      rw [StateInv, hmark]
      refine ⟨finite_mark hf u _, fun _ x hx q hq ↦ ?_⟩
      rcases htab x hx with h | rfl
      · exact isSome_mark _ (hraw (not_or.1 hb).1 x h q hq)
      · simp [mark, hq]

/-- The typed world preserves a clash. -/
theorem preservesInv_typedImpl_clash :
    QueryImpl.PreservesInv E.typedImpl fun s ↦ E.Clash s.1 := by
  rintro (n | u) ⟨c, pv⟩ hs z hz
  · simp only [typedImpl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply_run,
      support_map] at hz
    obtain ⟨_, _, rfl⟩ := hz
    exact hs
  · show E.Clash z.2.1
    rw [(mem_support_typedHashImpl_run (u := u) hz).1]
    exact hs.mono fun q ↦ isSome_mark _

/-- The typed world agrees with the patched typed world until a clash. -/
theorem agreeUntilBad_typedImpl_patchedImpl :
    QueryImpl.AgreeUntilBad E.typedImpl E.patchedImpl fun s ↦ E.Clash s.1 := by
  refine QueryImpl.AgreeUntilBad.of_run_eq_or_bad ?_
  rintro (n | u) ⟨c, pv⟩ hs
  · exact .inl rfl
  · simp only [typedImpl, patchedImpl, QueryImpl.add_apply_inr, patchedHashImpl, StateT.run_mk]
    by_cases hcol : E.Collides c u
    · refine .inr ⟨fun z hz ↦ ?_, fun z hz ↦ ?_⟩
      · rw [(mem_support_typedHashImpl_run hz).1]
        exact clash_mark (.inr hcol) _
      · simp only [hcol, or_true, ↓reduceIte, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hz
        obtain ⟨_, _, _, _, rfl⟩ := hz
        exact clash_mark (.inr hcol) _
    · exact .inl (by simp [hs, hcol])

/-- **An encoded random oracle until a clash.** Run from empty caches, an event of the output of
a computation against the single random oracle is at most the same event, or a clash of the final
typed cache, against independent typed random oracles with raw inputs routed. -/
theorem prEvent_simulateQ_singleImpl_run_le {α : Type}
    (oa : OracleComp (unifSpec + (spec + (D →ₒ M))) α) (P : α → Prop) :
    Pr{let z ← (simulateQ E.singleImpl oa).run ∅}[P z.1] ≤
      Pr{let z ← (simulateQ E.typedImpl oa).run (∅, ∅)}[P z.1 ∨ E.Clash z.2.1] :=
  (E.intertwinesOn_fill_patchedImpl_singleImpl).prEvent_simulateQ_run_le_or_bad
    E.preservesInv_patchedImpl_stateInv E.agreeUntilBad_typedImpl_patchedImpl
    E.preservesInv_typedImpl_clash oa (∅, ∅)
    ⟨by simp, fun _ x hx ↦ by simp at hx⟩ ∅ fill_empty P

/-- **An encoded random oracle until a clash, in the random oracle model.** Run from empty
caches, an event of the output of the encoding of a computation in the random oracle model of the
single oracle is at most the same event, or a clash of the final typed cache, in the typed
world. -/
theorem prEvent_simulateQ_romImpl_encodeImpl_run_le {α : Type}
    (oa : OracleComp (unifSpec + (spec + (D →ₒ M))) α) (P : α → Prop) :
    Pr{let z ← (simulateQ (D →ₒ M).romImpl (simulateQ E.encodeImpl oa)).run ∅}[P z.1] ≤
      Pr{let z ← (simulateQ E.typedImpl oa).run (∅, ∅)}[P z.1 ∨ E.Clash z.2.1] := by
  rw [simulateQ_romImpl_simulateQ_encodeImpl]
  exact E.prEvent_simulateQ_singleImpl_run_le oa P

end intertwining

end RandomOracleEncoding

end OracleComp
