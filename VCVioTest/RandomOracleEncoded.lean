/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.Encoded

/-!
# Encoded random oracle checks

Two typed oracle families share one random oracle `ℕ →ₒ Bool × Bool`: a short family with answers
in `Bool`, read as the first component of the single oracle's value, and a long family with the
whole value.

* With both families encoded at the same input, the short and the long typed answers at `0` are
  correlated in the single-oracle world (the short answer is the first component of the long one)
  and independent in the typed world. A computation comparing them returns `true` with probability
  one in the single-oracle world and also returns `false` in the typed world, so the clash term of
  `RandomOracleEncoding.prEvent_simulateQ_singleImpl_run_le` cannot be dropped; every final typed
  cache of that computation has a clash.
* With the families encoded at even and odd inputs, no clash is possible, so the single-oracle
  world is bounded by the typed world alone. A raw input routed to a short typed point is answered
  by the typed answer completed from a private value, so its first component is the typed answer.

A state map can intertwine two handlers on the states of an invariant without intertwining them
everywhere: forgetting a counter intertwines a handler that answers honestly only from the zero
state with plain forwarding, on the zero state (`QueryImpl.IntertwinesOn`).
-/

public section

open OracleComp OracleSpec MeasureTheory

namespace EncodedToy

/-- A short family with one-bit answers and a long family with two-bit answers. -/
abbrev spec : OracleSpec (ℕ ⊕ ℕ) := (ℕ →ₒ Bool) + (ℕ →ₒ Bool × Bool)

/-- The part of a single-oracle value that a typed point does not read. -/
abbrev Tail : ℕ ⊕ ℕ → Type
  | .inl _ => Bool
  | .inr _ => Unit

instance : ∀ t, SampleableType (Tail t)
  | .inl _ => inferInstanceAs (SampleableType Bool)
  | .inr _ => inferInstanceAs (SampleableType Unit)

/-- A value of the single oracle splits into the typed answer and the unread tail. -/
def split : (t : ℕ ⊕ ℕ) → (Bool × Bool) ≃ spec.Range t × Tail t
  | .inl _ => Equiv.refl _
  | .inr _ => (Equiv.prodPUnit _).symm

/-! ## Both families at the same input -/

/-- Both families encoded at the same input; a raw input is read as a long typed point. -/
noncomputable def shared : RandomOracleEncoding spec ℕ (Bool × Bool) :=
  .ofSplit (fun | .inl n => n | .inr n => n) (fun x ↦ some (.inr x))
    (by rintro x t h; cases h; rfl) (fun _ ↦ rfl) split

example (n : ℕ) (w : Bool × Bool) : shared.trunc (.inl n) w = w.1 := rfl

example (n : ℕ) (w : Bool × Bool) : shared.trunc (.inr n) w = w := rfl

/-- The common interface. -/
abbrev iface : OracleSpec (ℕ ⊕ ((ℕ ⊕ ℕ) ⊕ ℕ)) := unifSpec + (spec + (ℕ →ₒ Bool × Bool))

/-- Compare the short typed answer at `0` with the first component of the long one. -/
def compare : OracleComp iface Bool := do
  let a ← (query (spec := iface) (.inr (.inl (.inl 0))) : OracleComp iface Bool)
  let w ← (query (spec := iface) (.inr (.inl (.inr 0))) : OracleComp iface (Bool × Bool))
  pure (a == w.1)

/-- In the single-oracle world the short answer is the first component of the long one. -/
theorem compare_single_true :
    ∀ z ∈ support ((simulateQ shared.singleImpl compare).run ∅), z.1 = true := by
  intro z hz
  simp only [compare, simulateQ_bind, simulateQ_HasQuery_query, simulateQ_pure, StateT.run_bind,
    StateT.run_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨y, hy, y', hy', rfl⟩ := hz
  rw [RandomOracleEncoding.singleImpl, QueryImpl.add_apply_inr,
    RandomOracleEncoding.singleHashImpl_inl_run,
    support_map] at hy
  obtain ⟨v, hv, rfl⟩ := hy
  have hc : v.2 (shared.encode (.inr 0)) = some v.1 :=
    QueryImpl.withCaching_run_caches _ _ _ _ hv
  rw [RandomOracleEncoding.singleImpl, QueryImpl.add_apply_inr,
    RandomOracleEncoding.singleHashImpl_inl_run,
    QueryImpl.withCaching_run_some _ hc, map_pure, support_pure] at hy'
  subst hy'
  simp [shared, RandomOracleEncoding.ofSplit, split]

/-- In the typed world every final typed cache of `compare` has a clash. -/
theorem compare_typed_clash :
    ∀ z ∈ support ((simulateQ shared.typedImpl compare).run (∅, ∅)), shared.Clash z.2.1 := by
  intro z hz
  simp only [compare, simulateQ_bind, simulateQ_HasQuery_query, simulateQ_pure, StateT.run_bind,
    StateT.run_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨y, hy, y', hy', rfl⟩ := hz
  rw [RandomOracleEncoding.typedImpl, QueryImpl.add_apply_inr,
    RandomOracleEncoding.typedHashImpl_inl_run,
    support_map] at hy hy'
  obtain ⟨v, hv, rfl⟩ := hy
  obtain ⟨v', hv', rfl⟩ := hy'
  refine ⟨.inl 0, .inr 0, by simp, ?_, ?_, rfl⟩
  · simp [QueryImpl.withCaching_cache_le _ _ _ _ hv' (QueryImpl.withCaching_run_caches _ _ _ _ hv)]
  · simp [QueryImpl.withCaching_run_caches _ _ _ _ hv']

/-- In the typed world `compare` can return `false`. -/
theorem compare_typed_false :
    ∃ z ∈ support ((simulateQ shared.typedImpl compare).run (∅, ∅)), z.1 = false := by
  simp only [compare, simulateQ_bind, simulateQ_HasQuery_query, simulateQ_pure, StateT.run_bind,
    StateT.run_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
  let c₁ : spec.QueryCache := (∅ : spec.QueryCache).cacheQuery (.inl 0) true
  refine ⟨_, ⟨(true, (c₁, ∅)), ?_, ((false, false), (c₁.cacheQuery (.inr 0) (false, false), ∅)),
    ?_, rfl⟩, rfl⟩
  · rw [RandomOracleEncoding.typedImpl, QueryImpl.add_apply_inr,
    RandomOracleEncoding.typedHashImpl_inl_run,
      support_map]
    exact ⟨(true, c₁), by simp [c₁], rfl⟩
  · rw [RandomOracleEncoding.typedImpl, QueryImpl.add_apply_inr,
    RandomOracleEncoding.typedHashImpl_inl_run,
      support_map]
    refine ⟨((false, false), c₁.cacheQuery (.inr 0) (false, false)), ?_, rfl⟩
    have : c₁ (.inr 0) = none := by simp [c₁]
    simp [this]

/-- The clash term cannot be dropped: `compare` returns `true` with probability one in the
single-oracle world but not in the typed world. -/
theorem not_prEvent_single_le_prEvent_typed :
    ¬ Pr{let z ← (simulateQ shared.singleImpl compare).run ∅}[z.1 = true] ≤
      Pr{let z ← (simulateQ shared.typedImpl compare).run (∅, ∅)}[z.1 = true] := by
  intro h
  rw [prEvent_eq_one_of_forall_mem_support _ _ compare_single_true] at h
  obtain ⟨z, hz, hf⟩ := compare_typed_false
  have h1 := (prEvent_eq_one_iff _ _).1 (le_antisymm (prEvent_le_one _) h) z hz
  simp [hf] at h1

/-- The bound of the single-oracle world for `compare`, which the clash makes trivial. -/
example : Pr{let z ← (simulateQ shared.singleImpl compare).run ∅}[z.1 = true] ≤
    Pr{let z ← (simulateQ shared.typedImpl compare).run (∅, ∅)}[
      z.1 = true ∨ shared.Clash z.2.1] :=
  shared.prEvent_simulateQ_singleImpl_run_le compare fun b ↦ b = true

/-! ## The families at even and odd inputs -/

/-- The short family at even inputs and the long family at odd inputs; a raw input is read as the
typed point it encodes. -/
noncomputable def parity : RandomOracleEncoding spec ℕ (Bool × Bool) :=
  .ofSplit (fun | .inl n => 2 * n | .inr n => 2 * n + 1)
    (fun x ↦ if x % 2 = 0 then some (.inl (x / 2)) else some (.inr (x / 2)))
    (by
      rintro x t h
      split_ifs at h with hx <;> cases h <;> simp only <;> omega)
    (fun t ↦ by split_ifs <;> rfl) split

/-- Distinct typed points have distinct encodings, so no typed cache has a clash. -/
theorem parity_not_clash (c : spec.QueryCache) : ¬parity.Clash c := by
  rintro ⟨q, q', hne, -, -, he⟩
  rcases q with n | n <;> rcases q' with n' | n' <;>
    simp only [parity, RandomOracleEncoding.ofSplit] at he <;>
    first | omega | (apply hne; congr 1; omega)

/-- Without clashes the single-oracle world is bounded by the typed world alone. -/
theorem prEvent_parity_single_le {α : Type} (oa : OracleComp iface α) (P : α → Prop) :
    Pr{let z ← (simulateQ parity.singleImpl oa).run ∅}[P z.1] ≤
      Pr{let z ← (simulateQ parity.typedImpl oa).run (∅, ∅)}[P z.1] :=
  (parity.prEvent_simulateQ_singleImpl_run_le oa P).trans_eq
    (prEvent_congr _ _ _ fun z ↦ or_iff_left (parity_not_clash z.2.1))

/-- Query the short typed point at `0`, then the raw input `0`, which encodes it, and compare the
typed answer with the first component of the raw answer. -/
def routed : OracleComp iface Bool := do
  let a ← (query (spec := iface) (.inr (.inl (.inl 0))) : OracleComp iface Bool)
  let x ← (query (spec := iface) (.inr (.inr 0)) : OracleComp iface (Bool × Bool))
  pure (x.1 == a)

/-- In the typed world the raw input `0` is the short typed answer at `0` completed from a
private value, so its first component is the typed answer. -/
theorem routed_typed_true :
    ∀ z ∈ support ((simulateQ parity.typedImpl routed).run (∅, ∅)), z.1 = true := by
  intro z hz
  simp only [routed, simulateQ_bind, simulateQ_HasQuery_query, simulateQ_pure, StateT.run_bind,
    StateT.run_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨y, hy, y', hy', rfl⟩ := hz
  rw [RandomOracleEncoding.typedImpl, QueryImpl.add_apply_inr,
    RandomOracleEncoding.typedHashImpl_inl_run,
    support_map] at hy
  obtain ⟨v, hv, rfl⟩ := hy
  have hc : v.2 (.inl 0) = some v.1 := QueryImpl.withCaching_run_caches _ _ _ _ hv
  have hr : parity.route 0 = some (.inl 0) := rfl
  rw [RandomOracleEncoding.typedImpl, QueryImpl.add_apply_inr,
    RandomOracleEncoding.typedHashImpl_inr_run,
    mem_support_bind_iff] at hy'
  obtain ⟨p, -, hy'⟩ := hy'
  rw [hr] at hy'
  dsimp only at hy'
  rw [QueryImpl.withCaching_run_some _ hc, map_pure, support_pure,
    Set.mem_singleton_iff] at hy'
  subst hy'
  simp [parity, RandomOracleEncoding.ofSplit, split]

end EncodedToy

namespace IntertwinesOnToy

/-- Answers a uniform query honestly from the zero state, and with `0` from any other state. -/
def gated : QueryImpl unifSpec (StateT ℕ ProbComp) :=
  fun n ↦ StateT.mk fun k ↦
    if k = 0 then (fun u ↦ (u, k)) <$> (unifSpec.query n : ProbComp (Fin (n + 1)))
    else pure (0, k)

/-- Uniform queries forwarded on the unit state. -/
abbrev forward : QueryImpl unifSpec (StateT Unit ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT Unit ProbComp)

/-- Forgetting the counter intertwines `gated` with forwarding on the zero state. -/
theorem intertwinesOn_gated :
    QueryImpl.IntertwinesOn (· = 0) (fun _ ↦ (pure () : ProbComp Unit)) gated forward := by
  rintro n k rfl γ _ f
  simp [gated]

/-- `gated` keeps the zero state. -/
theorem preservesInv_gated : QueryImpl.PreservesInv gated (· = 0) := by
  rintro n k rfl z hz
  simp only [gated, StateT.run_mk, ↓reduceIte, support_map, Set.mem_image] at hz
  obtain ⟨_, _, rfl⟩ := hz
  rfl

/-- From the zero state, every run of `gated` has the distribution of forwarding. -/
example {α γ : Type} [MeasurableSpace γ] (oa : ProbComp α) (f : α → Unit → ProbComp γ) :
    𝒟[(simulateQ gated oa).run 0 >>= fun z ↦ (pure () : ProbComp Unit) >>= f z.1] =
      𝒟[(pure () : ProbComp Unit) >>= fun s ↦ (simulateQ forward oa).run s >>= fun z ↦
        f z.1 z.2] :=
  intertwinesOn_gated.evalDist_simulateQ_run preservesInv_gated oa 0 rfl f

/-- `gated` and forwarding are not intertwined from a nonzero state. -/
example : ¬QueryImpl.Intertwines (fun _ : ℕ ↦ (pure () : ProbComp Unit)) gated forward := by
  intro h
  have h1 := congrArg (fun μ : Measure (Fin 2) ↦ μ {1}) (h 1 1 (γ := Fin 2) fun u _ ↦ pure u)
  have h2 : (0 : ENNReal) = 2⁻¹ := by simpa [gated] using h1
  exact ENNReal.inv_ne_zero.2 (by simp) h2.symm

end IntertwinesOnToy
