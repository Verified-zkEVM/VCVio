/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.EvalDist.Monad.Support
public import VCVio.EvalDist.Defs.Measure
public import VCVio.EvalDist.ProbabilityNotation
public import ToMathlib.Data.ENNReal.Gauss

/-!
# Support of computations with `bind`

The monad laws `grind` normalizes with, and the support of a bind whose continuation ignores its
input.
-/

@[expose] public section

universe u v w

variable {α β γ : Type u} {m : Type u → Type v}

/- The monad/functor laws are confluent (terminating) rewrites. Tagging them for `grind` lets it
normalize a computation's structure (`mx >>= pure = mx`, reassociation, `f <$> pure a = pure (f a)`)
*before* it expands events and measures — turning what would otherwise be a `grind` explosion on a
structured-computation equality into a quick solve. `pure_bind` is not listed: core already ships
it in the default set (`attribute [grind <=] pure_bind` in `Init.Control.Lawful`), and re-tagging
it would add a redundant E-match entry. (The analogous `bind_pure_comp`/`map_eq_bind` laws are
deliberately omitted: their function argument sits under a binder that `grind`'s pattern compiler
cannot index; so do `pure_seq`/`seq_pure`, whose `Seq.seq` thunk argument makes even their LHS an
invalid pattern. `Functor.map_map` is binder-free and joins the set.) -/
attribute [grind =] bind_pure bind_assoc map_pure Functor.map_map

section support

variable [Monad m] [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]

lemma support_bind_const (mx : m α) (my : m β) :
    support (mx >>= fun _ => my) = {y ∈ support my | (support mx).Nonempty} := by
  grind [= Set.Nonempty]

lemma finSupport_bind_const [HasEvalFinset m]
    [DecidableEq β] [DecidableEq α] (mx : m α) (my : m β) :
    finSupport (mx >>= fun _ => my) = if (finSupport mx).Nonempty then finSupport my else ∅ := by
  ext x
  simp only [finSupport_bind, Finset.mem_biUnion]
  split_ifs <;> simp_all [Finset.nonempty_def]

end support
