/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Monad.Basic

/-!
# Lemmas for Probability Over Finite Spaces

This file houses lemmas about computations with `MonadLiftT m SPMF` semantics when
`mx : m α` is defined via a binding/mapping operation over a finite type.
In particular it provides `Finset.sum` versions of many `tsum` related probability lemmas.
-/

@[expose] public section

universe u v w

variable {α β γ : Type u} {m : Type u → Type v} [Monad m]

open ENNReal

lemma probOutput_bind_eq_sum_fintype [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (mx : m α) (my : α → m β) [Fintype α] (y : β) :
    Pr[= y | mx >>= my] = ∑ x : α, Pr[= x | mx] * Pr[= y | my x] :=
  (probOutput_bind_eq_tsum mx my y).trans (tsum_fintype _)
