# 09 — Verification Ledger: Named Anchors and Their Status

Every load-bearing declaration/file named by docs 00–08, with its verified location and merge
status. **Verified 2026-07-20** against VCVio `main` `a5f474fd`, PolyFun `main` `6a2d4bb`, and the
named PR worktrees. Implementation agents: grep these names *at these locations* before coding; if
a name has moved, update this ledger in the same PR that adapts to the move. Status legend:
**M** = merged on main; **PR#n** = exists only on the open PR's branch; **OFF** = only on
`dtumad/k-l-examples` (VCVio); **SK** = design sketch, does not exist yet.

## VCVio (`Verified-zkEVM/VCVio`)

| Anchor | Location | Status |
|---|---|---|
| `OracleComp` := `PFunctor.FreeM spec.toPFunctor`; `ofFreeM`/`toFreeM` seam | `VCVio/OracleComp/OracleComp.lean` | M |
| `simulateQ` | `VCVio/OracleComp/SimSemantics/` | M |
| `QueryImpl.Stateful I E σ`; `Stateful.run` (= `(simulateQ …).run' s₀`, drops state) | `VCVio/OracleComp/SimSemantics/StateT/StateSeparating.lean` | M |
| `QueryImpl.Stateful.Frame σ σ₁ σ₂` (`:64`); field `separated : PFunctor.Lens.State.IsSeparated` (`:74`) | same file | M |
| `linkWith` (`:222`), `parSumWith` (`:462`) | same file | M |
| `advantage`/`advantage₀`/`boolDistAdvantage`; hybrid/IUB layers | `VCVio/StateSeparating/{Advantage,Hybrid,IdenticalUntilBad,DistEquiv,IndistAt,CellRef}.lean` | M |
| `countingOracle` | `VCVio/OracleComp/QueryTracking/CountingOracle.lean` | M |
| `loggingOracle`, `IsQueryBound` | `QueryTracking/{LoggingOracle,QueryBound}.lean` | M |
| `cachingOracle`, random-oracle layer | `QueryTracking/{CachingOracle,RandomOracle/}` | M |
| Loom carriers: unary WP (`HoareTriple`, `Loom/*`), relational `CouplingPost`, quantitative `ℝ≥0∞`, scoped-qualitative discipline | `VCVio/ProgramLogic/{Unary,Relational}/…` | M |
| `SeededFork` | `VCVio/ProgramLogic/SeededFork.lean` | M |
| `Semantics`, `SPMFSemantics`, `ObservedCompEmulates`, `AsympObservedCompEmulates` | `VCVio/Interaction/UC/Computational.lean` | M |
| `ProtocolBoundary`, `Protocol`, `Functionality`, `Adversary`, `Environment`, `Simulator`, `dummyAdversary`, `EXEC`, `Execution(.ofSemantics)`, `UCSecure`, `observedCompEmulates_toUCSecure_id`, `HasDummyAdversaryFactor` | `VCVio/Interaction/UC/Standard.lean` | M |
| `processSemantics`, `processSemanticsOracle` | `VCVio/Interaction/UC/Runtime.lean` | M |
| `RuntimeEvent`, `AsyncRuntimeState`, `ProcessScheduler`/`EnvScheduler`, `runStepsAsync`, `processSemanticsAsync(±ProbComp)`, `trivialEnvScheduler`, `processSemantics_eq_processSemanticsAsync_trivial`, `MomentaryCorruption.Alphabet` | `VCVio/Interaction/UC/{AsyncRuntime,AsyncSecurity}.lean` | M |
| Universe-0 constraint on runtime moves/state/env alphabet | `AsyncRuntime.lean` module docstring | M (constraint) |
| Deferred-sampling + relational-coupling engine | VCVio PR #465 (merged `e413cf7b`) | M |
| Replay forking from PolyFun contexts | VCVio PR #488 (merged `a5f474fd`) | M |
| `WireK.wireKStep`, `RunLimit` (`runKT`/`runChain`/`runLimit`), `Coinductive/Machine` (`Implements`, `IsSimulation`), `TwoPhaseGame` | k-l-examples branch | **OFF** (G-0b) |
| `runExp`, `runExp_eq_runThrough`, `Semantics.ofBehavior`, `RelDisplayed`, `OwnershipFrame`, `SchedulingDiscipline`, `Topology` | docs 02–06 | **SK** |

## PolyFun (`Verified-zkEVM/PolyFun`) — merged on main

| Anchor | Location |
|---|---|
| `FreeM` (+ cslib re-export), `FreeM.append`, `FreeM.liftM` | `PolyFun/PFunctor/Free/{Basic,Universal,Path}.lean`, `Handler.lean` |
| Displayed free + decorations + displayed cursors | `PolyFun/PFunctor/Free/Displayed.lean`, `Free/Displayed/{Decoration,Cursor,Append,StateChain}.lean` |
| Cursors, occurrence lookup, fork | `PolyFun/PFunctor/Free/Cursor/{…,Occurrence,Fork}.lean` |
| Substitution monoids; free-as-monoid | `PolyFun/PFunctor/SubstMonoid.lean`, `Free/Polynomial.lean` |
| Internal hom + eval/curry (A1) | `PolyFun/PFunctor/InternalHom.lean`, `CartesianClosed.lean` |
| Vertical/cartesian factorization (A3) | `PolyFun/PFunctor/Lens/{Cartesian,Factorization}.lean` |
| Comonoids, retrofunctors `Comonoid.Hom`, comonoid categories | `PolyFun/PFunctor/Comonoid.lean`, `Comonoid/Category.lean` |
| Cofree comonoid; universal property; finite projections `CofreeP.extend_comp_projectionN` | `PolyFun/PFunctor/Cofree/{Polynomial,Universal,FiniteProjection}.lean` |
| `DynSystem` (= lens `selfMonomial S ⇆ p`), behavior, simulation | `PolyFun/PFunctor/Dynamical/{Basic,Trajectory,Behavior,Simulation,Bisimulation}.lean` |
| Cofree mate; `DynSystem.cofreeMate_comp_projectionN` | `Dynamical/CofreeMate.lean`, `Dynamical/CofreeMate/FiniteProjection.lean` |
| `Responder`, `equivStateHandler`; `DynSystem.game`/`closedGame` | `Dynamical/Responder.lean`, `Dynamical/Game.lean` |
| `IOMachine.seqComp`, `runWithInput_seqComp` — **removal pending (#83)**; successor: `DynComputation` seqcomp (#79) | `Dynamical/IOMachine.lean` |
| `TypeTree` (+ `done`/`node` `match_pattern` invariant), decorations, samplers, `Sampler.interleave` | `PolyFun/Interaction/Basic/…` |
| Concurrent processes/machines/frontiers/traces | `PolyFun/Interaction/Concurrent/…` |
| `PortBoundary(.Hom/.swap/.tensor)`, `OpenTheory` + ladder (`IsLawful`→`IsMonoidal`→`IsTraced`→`IsCompactClosed`→`HasPlugWireFactor`), `HasUnit`/`HasIdWire` | `PolyFun/Interaction/UC/{Interface,OpenTheory}.lean` |
| `OpenProcess`, `OpenProcessActivationEquiv` | `Interaction/UC/{OpenProcess,…}.lean` |
| Process model `openTheory` (tier: `IsLawful` only; `openTheory_par_assoc_activation_equiv` etc.) | `Interaction/UC/OpenProcessModel.lean` |
| `Observation(.eq)`, `Emulates`, `UCSecure`; `par_compose`(~457)/`wire_compose`(~494)/`plug_compose`(~526) under `[HasPlugWireFactor]`; `plug_right_of_observes_plug_comm`/`plug_compose_of_observes_plug_comm` (plug leg only, per-model `hcomm`) | `Interaction/UC/Emulates.lean` |
| Free models `Expr.theory`, `Interp.theory` (full ladder) | `Interaction/UC/OpenSyntax/{Expr,Interp}.lean`, `OpenTheory.lean` |
| `MachineId`, `EnvAction`, `CorruptionModel`, `MomentaryCorruption`, `Leakage` | `Interaction/UC/…` |
| `IPFunctor I`, indexed `FreeM`/`FreeM₂` | `PolyFun/IPFunctor/{Basic,Free/…}.lean` |
| ITrees: M-type carrier, strong bisim = `Eq`, weak bisim, cross-signature sim, lawful iter | `PolyFun/ITree/…` |

## PolyFun — open-PR anchors (worktree-verified)

| Anchor | Location (branch) | PR |
|---|---|---|
| `FreeP.runOn`, `FreeP.xi`, `runOn_eq_xi` | `PFunctor/PatternRunsOnMatter/{Universal,Module}.lean` (`feat/pattern-runs-on-matter-*`) | #71 |
| `runOn_unit`, `runOn_assoc`, naturality; `CofreeP.laxUnit/laxTensor` | `PatternRunsOnMatter/Module.lean` + `Cofree/LaxMonoidal.lean` | #71 |
| `FreeP.runThrough`, `FreeP.runAgainst`, `runAgainstMonoid`, `DynSystem.runPattern`, `runPattern_game`, `runBehaviorThrough_eq_of_{obsEq,isSimulation,isStrongSimulation}` | `PatternRunsOnMatter/{Operational,Dynamical,Applications}.lean` | #72 |
| `Display` (+ Chart/Coalgebra/Indexed/Free/Handler/Lens/Category) | `PFunctor/Display/…` (`agent/aberle-g*`) | #88–#92 |
| `ParallelChoice`, `PFunctor.parallelSum` (`P ∥ Q`), `≃ₚ (P+Q)+(P⊗Q)` | `PFunctor/Parallel.lean` | #93 |
| `Display.parallelSumComponents`/`parallelSum` (separable) | `PFunctor/Display/Parallel.lean` | #93 |
| `FreeM.parallel` (lockstep), `parallelAfterLeftReturn`; **interchange counterexample** (regression suite) | `PFunctor/Free/Parallel.lean` + tests | #94 |
| `Responder.parallel/sum`, parallel coalgebras/behaviors, `VerifiedPresentation`, `respondDisplayed`, coherence | `Dynamical/Responder/{Parallel/…,VerifiedPresentation,Behavior}.lean` | #95–#97 |
| `Wiring`, `Wiring.evalParallel` (+ race-freedom disclaimer), Abe26 Thm 3.1/5.3 | `PFunctor/Wiring.lean`, `Wiring/Parallel.lean` | #98 (+g2) |
| `IPFunctor/M.lean` (indexed M-types), `Display/M.lean` | g-series | #g4/#88+ |
| Displayed restriction along cursors | merged (`#58`) | M |
| `DynComputation` exact seqcomp / variance / bounds / termination; resumption coinduction/truncation; IOMachine removal | `issue32/*` branches | #76–#83 |
| Dependent `TypeTree` chain append | `feat/dependent-chain-append` | #66 (draft) |

## Correction history

- 2026-07-20 (this review): added the `_of_observes_plug_comm` escape-hatch nuance (docs 01/02);
  moved `TwoPhaseGame` to OFF status (docs 01); fixed `runExp` sketch to match `Stateful.run`'s
  actual signature (doc 03); named `Frame`/`IsSeparated` exactly (doc 05); annotated `IOMachine`
  removal (#83) wherever `seqComp` is cited (docs 01/09).
