/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.EvalDist.Defs.Semantics.Core
public import VCVio.EvalDist.Defs.Basic

/-!
# Bundled discrete probability compatibility

`SPMFSemantics` and `PMFSemantics` observe an internal monad through discrete distributions.
The module also exports the generic observation bundles and their native measure semantics.
-/

@[expose] public section

open MeasureTheory

universe u v w x

/-- Bundled subprobabilistic semantics for a monad `m`.

This is the specialization of `SemanticsVia` where the external observation target is `SPMF`.
Computations in `m` are therefore interpreted as subprobability distributions on outputs, possibly
with failure mass. -/
structure SPMFSemantics (m : Type u → Type v) [Monad m] extends SemanticsVia m SPMF

/-- The internal semantic monad of an `SPMFSemantics` carries the inherited monad structure. -/
instance {m : Type u → Type v} [Monad m] (sem : SPMFSemantics m) : Monad sem.Sem :=
  sem.toSemanticsVia.instMonadSem

namespace SPMFSemantics

variable {m : Type u → Type v} [Monad m] {α : Type u}

/-- The observation map of an `SPMFSemantics`, specialized to `SPMF`. -/
def observeSPMF (sem : SPMFSemantics m) : {α : Type u} → sem.Sem α → SPMF α :=
  sem.observe

/-- The subdistribution denoted by `mx` under the bundled semantics `sem`.

This first moves `mx` into the internal semantic monad via `interpret`, and then collapses the
internal structure to the externally visible `SPMF` via `observeSPMF`. -/
def evalSPMF (sem : SPMFSemantics m) (mx : m α) : SPMF α :=
  sem.toSemanticsVia.denote mx

/-- The probability that `mx` fails to return a value under `sem`.

Since `SPMFSemantics` is subprobabilistic, failure is represented by the missing mass of the
resulting `SPMF`, equivalently the probability of `none` in the underlying `Option`-valued PMF. -/
def probFailure (sem : SPMFSemantics m) (mx : m α) : ENNReal :=
  (sem.evalSPMF mx).run none

/-- Failure probability under an `SPMFSemantics` is always at most `1`. -/
@[simp]
lemma probFailure_le_one (sem : SPMFSemantics m) (mx : m α) : sem.probFailure mx ≤ 1 :=
  (sem.evalSPMF mx).coe_le_one none

/-- Package an ordinary `MonadLiftT m SPMF` instance as a bundled `SPMFSemantics`.

This is the bridge back to the case where the surface monad itself already carries its
subprobabilistic denotation. In that case the internal semantic monad is just `m` itself, the
interpreter is the identity monad morphism, and observation is `liftM`. -/
protected def ofMonadLift (m : Type u → Type v) [Monad m] [MonadLiftT m SPMF] :
    SPMFSemantics m where
  Sem := m
  instMonadSem := inferInstance
  interpret := MonadHom.id m
  observe := fun mx => liftM mx

@[simp]
lemma ofMonadLift_evalSPMF (mx : m α) [MonadLiftT m SPMF] :
    (SPMFSemantics.ofMonadLift m).evalSPMF mx = liftM mx := rfl

@[simp]
lemma ofMonadLift_probFailure (mx : m α) [MonadLiftT m SPMF] :
    (SPMFSemantics.ofMonadLift m).probFailure mx = Pr[⊥ | mx] :=
  (probFailure_def mx).symm

end SPMFSemantics

/-- Bundled total probabilistic semantics for a monad `m`.

This is the specialization of `SemanticsVia` where the external observation target is `PMF`.
There is therefore no failure mass in the resulting denotation. -/
structure PMFSemantics (m : Type u → Type v) [Monad m] extends SemanticsVia m PMF

/-- The internal semantic monad of a `PMFSemantics` carries the inherited monad structure. -/
instance {m : Type u → Type v} [Monad m] (sem : PMFSemantics m) : Monad sem.Sem :=
  sem.toSemanticsVia.instMonadSem

namespace PMFSemantics

variable {m : Type u → Type v} [Monad m] {α : Type u}

/-- The observation map of a `PMFSemantics`, specialized to `PMF`. -/
def observePMF (sem : PMFSemantics m) : {α : Type u} → sem.Sem α → PMF α :=
  sem.observe

/-- The total distribution denoted by `mx` under the bundled semantics `sem`. -/
def evalSPMF (sem : PMFSemantics m) (mx : m α) : PMF α :=
  sem.toSemanticsVia.denote mx

/-- Forget that a total semantics is total, yielding the underlying subprobabilistic semantics.

This simply postcomposes observation with the canonical embedding `PMF α → SPMF α`. The
resulting `SPMFSemantics` has zero failure probability, but it can now be consumed by APIs
that are stated in terms of subprobabilistic semantics. -/
noncomputable def toSPMFSemantics (sem : PMFSemantics m) : SPMFSemantics m where
  Sem := sem.Sem
  instMonadSem := sem.instMonadSem
  interpret := sem.interpret
  observe := fun mx => liftM (sem.observePMF mx)

/-- Package an ordinary `MonadLiftT m PMF` instance as a bundled `PMFSemantics`.

As with `SPMFSemantics.ofMonadLift`, this recovers the familiar case where the surface monad
already comes with a total probabilistic denotation. -/
protected def ofMonadLift (m : Type u → Type v) [Monad m] [MonadLiftT m PMF] :
    PMFSemantics m where
  Sem := m
  instMonadSem := inferInstance
  interpret := MonadHom.id m
  observe := fun mx => liftM mx

@[simp]
lemma ofMonadLift_evalSPMF (mx : m α) [MonadLiftT m PMF] :
    (PMFSemantics.ofMonadLift m).evalSPMF mx = liftM mx := rfl

end PMFSemantics
