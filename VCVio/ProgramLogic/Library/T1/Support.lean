/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.Monad.Support
public import VCVio.OracleComp.SimSemantics.Append.Core
public import VCVio.OracleComp.SimSemantics.StateT.Basic
public import ToMathlib.Control.WriterT

/-!
# Support calculus for simulated runs

Reachability facts about the run of a simulated program, `(simulateQ impl oa).run s`, for a
handler `impl` into `StateT σ m` or `WriterT ω m` over an arbitrary base monad `m` with an exact
support (`OracleComp spec'`, `ProbComp`, and any other `ExactMonadAttach` monad).

* *One-step rules*: membership in the support of the run of a bind, `pure`, map or query, in the
  existential form that `obtain` destructures; `run'` and `WriterT` variants, where the logs of
  the two halves of a bind are multiplied or appended.
* *Whole-run principles*, which replace an induction on the program: a per-query fact about
  `(impl t).run s` lifts to the run of every program. `inv_rel_of_mem_support_simulateQ_run` is
  the general form, for a state invariant `Inv` together with a reflexive, transitive relation
  `R` between the initial and the final state; `inv_of_mem_support_simulateQ_run`,
  `rel_of_mem_support_simulateQ_run` and `le_of_mem_support_simulateQ_run` specialize it, and
  `inv_of_mem_support_simulateQ_add_run` splits the hypothesis over a sum handler.
* *Projections*: a forward simulation of `impl₁` by `impl₂` along a state map `proj`, stated
  per query on supports, transfers every reachable value and projected state to whole runs
  (`mem_support_simulateQ_run_of_proj`). It needs no equation between the runs, unlike
  `OracleComp.map_run_simulateQ_eq_of_query_map_eq`, and the handlers may have different base
  monads; `mem_support_simulateQ_run_of_map_eq` starts from that lemma's per-query equation.
* *Writer logs*: a per-query invariant of the accumulated log, or a predicate on the written logs
  closed under the log operation, holds for the log of every run.
-/

public section

open OracleSpec

universe u u₁ u₂ v v₂ w

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec ι} {m : Type w → Type v} [Monad m] [LawfulMonad m]
  [MonadAttach m] [ExactMonadAttach m] {σ α β : Type w}

/-! ## One-step rules for `StateT` runs -/

section stateT

variable (impl : QueryImpl spec (StateT σ m))

/-- A run of a simulated bind reaches `z` exactly through a reachable value and state of the
head, from which the continuation reaches `z`. -/
theorem mem_support_simulateQ_run_bind_iff (oa : OracleComp spec α) (f : α → OracleComp spec β)
    (s : σ) (z : β × σ) :
    z ∈ support ((simulateQ impl (oa >>= f)).run s) ↔
      ∃ a s', (a, s') ∈ support ((simulateQ impl oa).run s) ∧
        z ∈ support ((simulateQ impl (f a)).run s') := by
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff, Prod.exists]

/-- A run of a simulated `pure a` from `s` reaches only `(a, s)`. -/
theorem mem_support_simulateQ_run_pure_iff (a : α) (s : σ) (z : α × σ) :
    z ∈ support ((simulateQ impl (pure a : OracleComp spec α)).run s) ↔ z = (a, s) := by
  simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff]

/-- A run of a simulated map reaches the images of the reachable values, with their states. -/
theorem mem_support_simulateQ_run_map_iff (f : α → β) (oa : OracleComp spec α) (s : σ)
    (z : β × σ) :
    z ∈ support ((simulateQ impl (f <$> oa)).run s) ↔
      ∃ a s', (a, s') ∈ support ((simulateQ impl oa).run s) ∧ z = (f a, s') := by
  simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image, Prod.exists]
  exact exists₂_congr fun _ _ ↦ and_congr_right fun _ ↦ eq_comm

/-- A run of a query followed by a continuation reaches `z` exactly through an answer and state
of the handler call, from which the continuation reaches `z`. -/
theorem mem_support_simulateQ_run_query_bind_iff (t : spec.Domain)
    (k : spec.Range t → OracleComp spec α) (s : σ) (z : α × σ) :
    z ∈ support ((simulateQ impl (liftM (spec.query t) >>= k)).run s) ↔
      ∃ u s', (u, s') ∈ support ((impl t).run s) ∧
        z ∈ support ((simulateQ impl (k u)).run s') := by
  rw [mem_support_simulateQ_run_bind_iff, simulateQ_spec_query]

/-- A value is reachable by `run'` exactly when it is reachable by `run` with some final state. -/
theorem mem_support_simulateQ_run'_iff (oa : OracleComp spec α) (s : σ) (a : α) :
    a ∈ support ((simulateQ impl oa).run' s) ↔
      ∃ s', (a, s') ∈ support ((simulateQ impl oa).run s) := by
  simp only [StateT.run'_eq, support_map, Set.mem_image, Prod.exists, exists_and_right,
    exists_eq_right]

/-- The `run'` form of `mem_support_simulateQ_run_bind_iff`. -/
theorem mem_support_simulateQ_run'_bind_iff (oa : OracleComp spec α)
    (f : α → OracleComp spec β) (s : σ) (b : β) :
    b ∈ support ((simulateQ impl (oa >>= f)).run' s) ↔
      ∃ a s', (a, s') ∈ support ((simulateQ impl oa).run s) ∧
        b ∈ support ((simulateQ impl (f a)).run' s') := by
  simp only [mem_support_simulateQ_run'_iff, mem_support_simulateQ_run_bind_iff]
  exact ⟨fun ⟨s'', a, s', h, h'⟩ ↦ ⟨a, s', h, s'', h'⟩,
    fun ⟨a, s', h, s'', h'⟩ ↦ ⟨s'', a, s', h, h'⟩⟩

/-- Every value reachable by a simulated run is a possible output of the program itself. -/
theorem fst_mem_support_of_mem_support_simulateQ_run {oa : OracleComp spec α} {s : σ}
    {z : α × σ} (hz : z ∈ support ((simulateQ impl oa).run s)) : z.1 ∈ support oa :=
  support_simulateQ_run'_subset impl oa s ((mem_support_simulateQ_run'_iff impl oa s z.1).2
    ⟨z.2, hz⟩)

end stateT

/-! ## Whole-run principles for `StateT` handlers -/

section invariant

variable {impl : QueryImpl spec (StateT σ m)}

/-- A state invariant `Inv` and a reflexive, transitive relation `R` from the initial state that
every handler call preserves from states satisfying `Inv` hold at every reachable final state of
the run of any simulated program. -/
theorem inv_rel_of_mem_support_simulateQ_run {Inv : σ → Prop} (R : σ → σ → Prop)
    (hrefl : ∀ s, R s s) (htrans : ∀ s₁ s₂ s₃, R s₁ s₂ → R s₂ s₃ → R s₁ s₃)
    (hstep : ∀ t s, Inv s → ∀ z ∈ support ((impl t).run s), Inv z.2 ∧ R s z.2)
    {oa : OracleComp spec α} {s : σ} {z : α × σ} (hs : Inv s)
    (hz : z ∈ support ((simulateQ impl oa).run s)) : Inv z.2 ∧ R s z.2 := by
  induction oa using OracleComp.inductionOn generalizing s z with
  | pure a =>
    rw [mem_support_simulateQ_run_pure_iff] at hz
    exact hz ▸ ⟨hs, hrefl s⟩
  | query_bind t k ih =>
    obtain ⟨u, s', hu, hz⟩ := (mem_support_simulateQ_run_query_bind_iff impl t k s z).1 hz
    obtain ⟨hs', hr⟩ := hstep t s hs (u, s') hu
    obtain ⟨hz', hr'⟩ := ih u hs' hz
    exact ⟨hz', htrans _ _ _ hr hr'⟩

/-- A state invariant preserved by every handler call holds at every reachable final state of
the run of any simulated program started in it. -/
theorem inv_of_mem_support_simulateQ_run {Inv : σ → Prop}
    (hstep : ∀ t s, Inv s → ∀ z ∈ support ((impl t).run s), Inv z.2)
    {oa : OracleComp spec α} {s : σ} {z : α × σ} (hs : Inv s)
    (hz : z ∈ support ((simulateQ impl oa).run s)) : Inv z.2 :=
  (inv_rel_of_mem_support_simulateQ_run (fun _ _ ↦ True) (fun _ ↦ trivial)
    (fun _ _ _ _ _ ↦ trivial) (fun t s hs z hz ↦ ⟨hstep t s hs z hz, trivial⟩) hs hz).1

/-- A reflexive, transitive relation between the initial and the final state of every handler
call relates the initial and every reachable final state of the run of any simulated program. -/
theorem rel_of_mem_support_simulateQ_run (R : σ → σ → Prop) (hrefl : ∀ s, R s s)
    (htrans : ∀ s₁ s₂ s₃, R s₁ s₂ → R s₂ s₃ → R s₁ s₃)
    (hstep : ∀ t s, ∀ z ∈ support ((impl t).run s), R s z.2)
    {oa : OracleComp spec α} {s : σ} {z : α × σ}
    (hz : z ∈ support ((simulateQ impl oa).run s)) : R s z.2 :=
  (inv_rel_of_mem_support_simulateQ_run (Inv := fun _ ↦ True) R hrefl htrans
    (fun t s _ z hz ↦ ⟨trivial, hstep t s z hz⟩) trivial hz).2

/-- Monotone handlers give monotone runs: if every handler call can only increase the state, so
can the run of any simulated program. -/
theorem le_of_mem_support_simulateQ_run [Preorder σ]
    (hstep : ∀ t s, ∀ z ∈ support ((impl t).run s), s ≤ z.2)
    {oa : OracleComp spec α} {s : σ} {z : α × σ}
    (hz : z ∈ support ((simulateQ impl oa).run s)) : s ≤ z.2 :=
  rel_of_mem_support_simulateQ_run (· ≤ ·) le_refl (fun _ _ _ ↦ le_trans) hstep hz

/-- `inv_of_mem_support_simulateQ_run` for a sum handler: an invariant preserved by both
summands is preserved by the run of any program under their sum. -/
theorem inv_of_mem_support_simulateQ_add_run {ι₁ : Type u₁} {ι₂ : Type u₂}
    {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {impl₁ : QueryImpl spec₁ (StateT σ m)}
    {impl₂ : QueryImpl spec₂ (StateT σ m)} {Inv : σ → Prop}
    (hstep₁ : ∀ t s, Inv s → ∀ z ∈ support ((impl₁ t).run s), Inv z.2)
    (hstep₂ : ∀ t s, Inv s → ∀ z ∈ support ((impl₂ t).run s), Inv z.2)
    {oa : OracleComp (spec₁ + spec₂) α} {s : σ} {z : α × σ} (hs : Inv s)
    (hz : z ∈ support ((simulateQ (impl₁ + impl₂) oa).run s)) : Inv z.2 :=
  inv_of_mem_support_simulateQ_run (fun t ↦ match t with | .inl t => hstep₁ t | .inr t => hstep₂ t)
    hs hz

end invariant

/-! ## Projections -/

section proj

variable {m₂ : Type w → Type v₂} [Monad m₂] [LawfulMonad m₂] [MonadAttach m₂] [ExactMonadAttach m₂]
  {σ₁ σ₂ : Type w} {impl₁ : QueryImpl spec (StateT σ₁ m)} {impl₂ : QueryImpl spec (StateT σ₂ m₂)}

/-- Invariant-gated forward simulation: if, from states satisfying `Inv`, every step of `impl₁`
keeps `Inv` and is matched by a step of `impl₂` from the projected state, then so is every run. -/
theorem mem_support_simulateQ_run_of_proj_of_inv (proj : σ₁ → σ₂) {Inv : σ₁ → Prop}
    (hstep : ∀ t s, Inv s → ∀ z ∈ support ((impl₁ t).run s),
      Inv z.2 ∧ (z.1, proj z.2) ∈ support ((impl₂ t).run (proj s)))
    {oa : OracleComp spec α} {s : σ₁} {z : α × σ₁} (hs : Inv s)
    (hz : z ∈ support ((simulateQ impl₁ oa).run s)) :
    Inv z.2 ∧ (z.1, proj z.2) ∈ support ((simulateQ impl₂ oa).run (proj s)) := by
  induction oa using OracleComp.inductionOn generalizing s z with
  | pure a =>
    rw [mem_support_simulateQ_run_pure_iff] at hz
    subst hz
    exact ⟨hs, (mem_support_simulateQ_run_pure_iff impl₂ a (proj s) _).2 rfl⟩
  | query_bind t k ih =>
    obtain ⟨u, s', hu, hz⟩ := (mem_support_simulateQ_run_query_bind_iff impl₁ t k s z).1 hz
    obtain ⟨hs', hu'⟩ := hstep t s hs (u, s') hu
    obtain ⟨hz', hz''⟩ := ih u hs' hz
    exact ⟨hz', (mem_support_simulateQ_run_query_bind_iff impl₂ t k (proj s) _).2
      ⟨u, proj s', hu', hz''⟩⟩

/-- Forward simulation along a state projection: if every step of `impl₁` is matched by a step
of `impl₂` from the projected state, so is every run of every simulated program. -/
theorem mem_support_simulateQ_run_of_proj (proj : σ₁ → σ₂)
    (hstep : ∀ t s, ∀ z ∈ support ((impl₁ t).run s),
      (z.1, proj z.2) ∈ support ((impl₂ t).run (proj s)))
    {oa : OracleComp spec α} {s : σ₁} {z : α × σ₁}
    (hz : z ∈ support ((simulateQ impl₁ oa).run s)) :
    (z.1, proj z.2) ∈ support ((simulateQ impl₂ oa).run (proj s)) :=
  (mem_support_simulateQ_run_of_proj_of_inv proj (Inv := fun _ ↦ True)
    (fun t s _ z hz ↦ ⟨trivial, hstep t s z hz⟩) trivial hz).2

/-- The `run'` form of `mem_support_simulateQ_run_of_proj`: every output reachable under
`impl₁` is reachable under `impl₂` from the projected state. -/
theorem mem_support_simulateQ_run'_of_proj (proj : σ₁ → σ₂)
    (hstep : ∀ t s, ∀ z ∈ support ((impl₁ t).run s),
      (z.1, proj z.2) ∈ support ((impl₂ t).run (proj s)))
    {oa : OracleComp spec α} {s : σ₁} {a : α}
    (ha : a ∈ support ((simulateQ impl₁ oa).run' s)) :
    a ∈ support ((simulateQ impl₂ oa).run' (proj s)) := by
  obtain ⟨s', hs'⟩ := (mem_support_simulateQ_run'_iff impl₁ oa s a).1 ha
  exact (mem_support_simulateQ_run'_iff impl₂ oa (proj s) a).2
    ⟨proj s', mem_support_simulateQ_run_of_proj proj hstep hs'⟩

/-- Forward simulation from the state-projection equation of
`OracleComp.map_run_simulateQ_eq_of_query_map_eq`: if mapping the state of every step of
`impl₁` by `proj` gives the step of `impl₂` from the projected state, every run is matched. -/
theorem mem_support_simulateQ_run_of_map_eq {impl₁ : QueryImpl spec (StateT σ₁ m)}
    {impl₂ : QueryImpl spec (StateT σ₂ m)} (proj : σ₁ → σ₂)
    (hstep : ∀ t s, Prod.map id proj <$> (impl₁ t).run s = (impl₂ t).run (proj s))
    {oa : OracleComp spec α} {s : σ₁} {z : α × σ₁}
    (hz : z ∈ support ((simulateQ impl₁ oa).run s)) :
    (z.1, proj z.2) ∈ support ((simulateQ impl₂ oa).run (proj s)) :=
  mem_support_simulateQ_run_of_proj proj (fun t s z hz ↦ by
    rw [← hstep, support_map]
    exact ⟨z, hz, rfl⟩) hz

end proj

/-! ## `WriterT` runs -/

section writerT

variable {ω : Type w}

section monoid

variable [Monoid ω] {impl : QueryImpl spec (WriterT ω m)}

/-- A run of a simulated bind under a monoid-log handler reaches `z` exactly through runs of the
two halves whose logs multiply to the log of `z`. -/
theorem mem_support_simulateQ_writerT_run_bind_iff (impl : QueryImpl spec (WriterT ω m))
    (oa : OracleComp spec α) (f : α → OracleComp spec β) (z : β × ω) :
    z ∈ support (simulateQ impl (oa >>= f)).run ↔
      ∃ a w₁ b w₂, (a, w₁) ∈ support (simulateQ impl oa).run ∧
        (b, w₂) ∈ support (simulateQ impl (f a)).run ∧ z = (b, w₁ * w₂) := by
  simp only [simulateQ_bind, WriterT.run_bind, mem_support_bind_iff, support_map, Set.mem_image,
    Prod.exists]
  exact ⟨fun ⟨a, w₁, h₁, b, w₂, h₂, hz⟩ ↦ ⟨a, w₁, b, w₂, h₁, h₂, hz.symm⟩,
    fun ⟨a, w₁, b, w₂, h₁, h₂, hz⟩ ↦ ⟨a, w₁, h₁, b, w₂, h₂, hz.symm⟩⟩

/-- An invariant of the accumulated log that every handler call preserves holds after the run of
any simulated program: the incoming log `w` times the written log satisfies it. -/
theorem inv_of_mem_support_simulateQ_writerT_run {Inv : ω → Prop}
    (hstep : ∀ t w, Inv w → ∀ z ∈ support (impl t).run, Inv (w * z.2))
    {oa : OracleComp spec α} {w : ω} {z : α × ω} (hw : Inv w)
    (hz : z ∈ support (simulateQ impl oa).run) : Inv (w * z.2) := by
  induction oa using OracleComp.inductionOn generalizing w z with
  | pure a =>
    simp only [simulateQ_pure, WriterT.run_pure, mem_support_pure_iff] at hz
    rwa [hz, mul_one]
  | query_bind t k ih =>
    obtain ⟨u, w₁, b, w₂, hu, hb, rfl⟩ :=
      (mem_support_simulateQ_writerT_run_bind_iff impl _ k z).1 hz
    rw [simulateQ_spec_query] at hu
    simpa only [mul_assoc] using ih u (hstep t w hw (u, w₁) hu) hb

/-- A predicate on logs that holds at `1`, is closed under multiplication, and holds for the log
written by every handler call holds for the log written by the run of any simulated program. -/
theorem prop_of_mem_support_simulateQ_writerT_run {P : ω → Prop} (h₁ : P 1)
    (hmul : ∀ a b, P a → P b → P (a * b)) (hstep : ∀ t, ∀ z ∈ support (impl t).run, P z.2)
    {oa : OracleComp spec α} {z : α × ω} (hz : z ∈ support (simulateQ impl oa).run) : P z.2 := by
  simpa only [one_mul] using inv_of_mem_support_simulateQ_writerT_run
    (fun t w hw z hz ↦ hmul w z.2 hw (hstep t z hz)) h₁ hz

end monoid

section append

variable [EmptyCollection ω] [Append ω] [LawfulAppend ω] {impl : QueryImpl spec (WriterT ω m)}

/-- A run of a simulated bind under an append-log handler reaches `z` exactly through runs of
the two halves whose logs concatenate to the log of `z`. -/
theorem mem_support_simulateQ_writerT_run_bind_iff_append (impl : QueryImpl spec (WriterT ω m))
    (oa : OracleComp spec α) (f : α → OracleComp spec β) (z : β × ω) :
    z ∈ support (simulateQ impl (oa >>= f)).run ↔
      ∃ a w₁ b w₂, (a, w₁) ∈ support (simulateQ impl oa).run ∧
        (b, w₂) ∈ support (simulateQ impl (f a)).run ∧ z = (b, w₁ ++ w₂) := by
  simp only [simulateQ_bind, WriterT.run_bind, mem_support_bind_iff, support_map, Set.mem_image,
    Prod.exists]
  exact ⟨fun ⟨a, w₁, h₁, b, w₂, h₂, hz⟩ ↦ ⟨a, w₁, b, w₂, h₁, h₂, hz.symm⟩,
    fun ⟨a, w₁, b, w₂, h₁, h₂, hz⟩ ↦ ⟨a, w₁, h₁, b, w₂, h₂, hz.symm⟩⟩

/-- An invariant of the accumulated append log that every handler call preserves holds after the
run of any simulated program: the incoming log `w` followed by the written log satisfies it. -/
theorem inv_of_mem_support_simulateQ_writerT_run_append {Inv : ω → Prop}
    (hstep : ∀ t w, Inv w → ∀ z ∈ support (impl t).run, Inv (w ++ z.2))
    {oa : OracleComp spec α} {w : ω} {z : α × ω} (hw : Inv w)
    (hz : z ∈ support (simulateQ impl oa).run) : Inv (w ++ z.2) := by
  induction oa using OracleComp.inductionOn generalizing w z with
  | pure a =>
    simp only [simulateQ_pure, WriterT.run_pure, mem_support_pure_iff] at hz
    rwa [hz, LawfulAppend.append_empty]
  | query_bind t k ih =>
    obtain ⟨u, w₁, b, w₂, hu, hb, rfl⟩ :=
      (mem_support_simulateQ_writerT_run_bind_iff_append impl _ k z).1 hz
    rw [simulateQ_spec_query] at hu
    simpa only [LawfulAppend.append_assoc] using ih u (hstep t w hw (u, w₁) hu) hb

/-- A predicate on logs that holds at `∅`, is closed under `++`, and holds for the log written by
every handler call holds for the log written by the run of any simulated program. -/
theorem prop_of_mem_support_simulateQ_writerT_run_append {P : ω → Prop} (h₀ : P ∅)
    (happend : ∀ a b, P a → P b → P (a ++ b)) (hstep : ∀ t, ∀ z ∈ support (impl t).run, P z.2)
    {oa : OracleComp spec α} {z : α × ω} (hz : z ∈ support (simulateQ impl oa).run) : P z.2 := by
  simpa only [LawfulAppend.empty_append] using inv_of_mem_support_simulateQ_writerT_run_append
    (fun t w hw z hz ↦ happend w z.2 hw (hstep t z hz)) h₀ hz

end append

end writerT

end OracleComp
