/-
Copyright (c) 2026 Tom Wambsgans, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans, Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.WriterCost
public import VCVio.OracleComp.Support

/-!
# Writer cost rules under lawful attachment

One-way support elimination suffices for bind, pure, tell and lift cost rules. These rules
require lawful attachment and do not require support introduction or `ExactMonadAttach`.
The payload and natural-number cost types are small; the runtime universe is independent.
-/

public section
universe z

namespace AddWriterT.LawfulAttach
variable {m : Type → Type z} [Monad m] [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m]

/-- A reachable writer bind result comes from reachable results of its two computations. -/
theorem mem_support_run_bind {γ δ : Type} {oa : AddWriterT ℕ m γ}
    {f : γ → AddWriterT ℕ m δ} {z : δ × Multiplicative ℕ} (hz : z ∈ support (oa >>= f).run) :
    ∃ x ∈ support oa.run, ∃ y ∈ support (f x.1).run, z = (y.1, x.2 * y.2) := by
  rw [WriterT.run_bind] at hz
  obtain ⟨⟨a, wa⟩, hx, hy⟩ := LawfulMonadAttach.canReturn_bind_imp' hz
  obtain ⟨⟨b, wb⟩, hb, hzb⟩ := LawfulMonadAttach.canReturn_map_imp' hy
  exact ⟨(a, wa), hx, (b, wb), hb, hzb.symm⟩

/-- Reachable upper query bounds add across bind under lawful attachment. -/
theorem queryBoundedAboveBy_bind {γ δ : Type} {oa : AddWriterT ℕ m γ}
    {f : γ → AddWriterT ℕ m δ} {n₁ n₂ : ℕ} (h₁ : AddWriterT.QueryBoundedAboveBy oa n₁)
    (h₂ : ∀ a, AddWriterT.QueryBoundedAboveBy (f a) n₂) :
    AddWriterT.QueryBoundedAboveBy (oa >>= f) (n₁ + n₂) := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_support_run_bind hz
  simpa using Nat.add_le_add (h₁ x hx) (h₂ x.1 y hy)

/-- Reachable lower query bounds add across bind under lawful attachment. -/
theorem queryBoundedBelowBy_bind {γ δ : Type} {oa : AddWriterT ℕ m γ}
    {f : γ → AddWriterT ℕ m δ} {n₁ n₂ : ℕ} (h₁ : AddWriterT.QueryBoundedBelowBy oa n₁)
    (h₂ : ∀ a, AddWriterT.QueryBoundedBelowBy (f a) n₂) :
    AddWriterT.QueryBoundedBelowBy (oa >>= f) (n₁ + n₂) := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_support_run_bind hz
  simpa using Nat.add_le_add (h₁ x hx) (h₂ x.1 y hy)

/-- Exact costs on reachable results add across bind under lawful attachment. -/
theorem queryCostExactly_bind {γ δ : Type} {oa : AddWriterT ℕ m γ}
    {f : γ → AddWriterT ℕ m δ} {n₁ n₂ : ℕ} (h₁ : AddWriterT.QueryCostExactly oa n₁)
    (h₂ : ∀ a, AddWriterT.QueryCostExactly (f a) n₂) :
    AddWriterT.QueryCostExactly (oa >>= f) (n₁ + n₂) :=
  ⟨queryBoundedAboveBy_bind h₁.toAbove (fun a => (h₂ a).toAbove),
    queryBoundedBelowBy_bind h₁.toBelow (fun a => (h₂ a).toBelow)⟩

/-- Returning a value has zero cost on every reachable result. -/
theorem queryCostExactly_pure {γ : Type} (x : γ) :
    AddWriterT.QueryCostExactly (pure x : AddWriterT ℕ m γ) 0 := by
  have h : ∀ z ∈ support (pure x : AddWriterT ℕ m γ).run, Multiplicative.toAdd z.2 = 0 := by
    intro z hz
    rw [WriterT.run_pure] at hz
    rw [← LawfulMonadAttach.eq_of_canReturn_pure hz]
    rfl
  exact ⟨fun z hz => (h z hz).le, fun z hz => (h z hz).ge⟩

/-- Telling a natural-number cost records that cost on every reachable result. -/
theorem queryCostExactly_addTell (w : ℕ) :
    AddWriterT.QueryCostExactly (AddWriterT.addTell (M := m) w) w := by
  have h : ∀ z ∈ support (AddWriterT.addTell (M := m) w).run, Multiplicative.toAdd z.2 = w := by
    intro z hz
    rw [AddWriterT.run_addTell] at hz
    rw [← LawfulMonadAttach.eq_of_canReturn_pure hz]
    rfl
  exact ⟨fun z hz => (h z hz).le, fun z hz => (h z hz).ge⟩

/-- Lifting a base computation contributes zero writer cost on every reachable result. -/
theorem queryCostExactly_monadLift {γ : Type} (x : m γ) :
    AddWriterT.QueryCostExactly (monadLift x : AddWriterT ℕ m γ) 0 := by
  have h : ∀ z ∈ support (monadLift x : AddWriterT ℕ m γ).run, Multiplicative.toAdd z.2 = 0 := by
    intro z hz
    rw [WriterT.run_monadLift] at hz
    obtain ⟨a, -, rfl⟩ := LawfulMonadAttach.canReturn_map_imp' hz
    rfl
  exact ⟨fun z hz => (h z hz).le, fun z hz => (h z hz).ge⟩


end AddWriterT.LawfulAttach
