/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.ResumptionKernel
public import PolyFun.ITree.DomainLaws

/-!
# Joint stateful kernel semantics for interaction trees

The existing continuous kernel algebra interprets visible service calls. Silent
steps use the shared ITree domain interpretation. The result agrees with the
resumption kernel through the canonical embedding and is invariant under weak
bisimulation. Private states and results may carry arbitrary measurable spaces
and independent universes; countable separated answers select continuations.
-/

public section

open MeasureTheory ProbabilityTheory OmegaCompletePartialOrder PFunctor

namespace ITree

universe uA uB uS uR
variable {P : PFunctor.{uA, uB}} {S : Type uS} {α : Type uR}
  [∀ a, MeasurableSpace (P.B a)] [∀ a, Countable (P.B a)]
  [∀ a, MeasurableSingletonClass (P.B a)] [MeasurableSpace S] [MeasurableSpace α]

/-- The least joint result-and-state kernel of a client with visible and silent steps. -/
noncomputable def runKernel (K : KernelHandler P S) (tree : ITree P α) : Kernel S (α × S) :=
  denote (fun x => Kernel.deterministic (fun s => (x, s))
    (measurable_const.prodMk measurable_id)) K.continuousAlgebra tree

/-- The joint kernel is the shared continuous-algebra interpretation. -/
theorem runKernel_eq_denote (K : KernelHandler P S) (tree : ITree P α) :
    runKernel K tree = denote (fun x => Kernel.deterministic (fun s => (x, s))
      (measurable_const.prodMk measurable_id)) K.continuousAlgebra tree := by rfl

/-- Returning a value preserves the current private state. -/
@[simp] theorem runKernel_pure (K : KernelHandler P S) (x : α) (s : S) :
    runKernel K (pure x) s = Measure.dirac (x, s) := by
  simp only [runKernel, denote_pure]
  rfl

/-- Silent steps have no effect on the returned-state kernel. -/
@[simp] theorem runKernel_step (K : KernelHandler P S) (tree : ITree P α) :
    runKernel K (step tree) = runKernel K tree := by
  simp only [runKernel, denote_step]

/-- A visible operation samples its answer and successor state before continuing. -/
theorem runKernel_query (K : KernelHandler P S) (a : P.A)
    (next : P.B a → ITree P α) (s : S) :
    runKernel K (query a next) s =
      (K a s).bind (fun out => runKernel K (next out.1) out.2) := by
  rw [runKernel, denote_query, KernelHandler.continuousAlgebra_apply]
  rfl

/-- The canonical tau-free embedding preserves the complete joint kernel interpretation. -/
theorem runKernel_toITree (K : KernelHandler P S) (tree : Resumption P α) :
    runKernel K tree.toITree = Resumption.runKernel K tree := by
  rw [runKernel, denote_toITree, Resumption.runKernel_eq_denote]

/-- Silent divergence contributes no returned result or state. -/
@[simp] theorem runKernel_diverge (K : KernelHandler P S) :
    runKernel K (diverge : ITree P α) = 0 := by
  rw [runKernel, denote_diverge]
  rfl

/-- Weakly bisimilar clients have equal joint returned-state kernels. -/
theorem WeakBisim.runKernel_eq (K : KernelHandler P S) {left right : ITree P α}
    (h : WeakBisim left right) : runKernel K left = runKernel K right :=
  h.denote_eq _ _

end ITree
