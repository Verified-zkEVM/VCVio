/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio
public import Examples
public import HashSig
public import LatticeCrypto
public import VCVio.ProgramLogic.Library.Derive
import all Examples.BR93
import all Examples.CommitmentScheme.Binding
import all Examples.CommitmentScheme.Hiding.CountBounds
import all Examples.CommitmentScheme.Hiding.Defs
import all Examples.CommitmentScheme.Hiding.LoggingBounds.Average
import all Examples.CommitmentScheme.Hiding.LoggingBounds.QuerySalt
import all Examples.ElGamal.ComputationalComplexity
import all Examples.ElGamal.HandlerExecution
import all Examples.ElGamal.ReductionCost
import all Examples.ElGamal.SSP
import all Examples.MerkleCheckpoints
import all Examples.OneTimePad.HeapBasic
import all Examples.OneTimePad.HeapPar
import all Examples.OneTimePad.LeakageFree
import all Examples.PRFTagReader.Asymptotic
import all Examples.PRFTagReader.Auth
import all Examples.PRFTagReader.BadEvent
import all Examples.PRFTagReader.CacheRepresentation
import all Examples.PRFTagReader.Collision
import all Examples.PRFTagReader.Collision.ForgeStep
import all Examples.PRFTagReader.Defs
import all Examples.PRFTagReader.DirectCoupling.Compose
import all Examples.PRFTagReader.MultipleBadCollision
import all Examples.PRFTagReader.MultipleToHybrid.EagerSetup
import all Examples.PRFTagReader.MultipleToHybrid.Setup
import all Examples.PRFTagReader.Network
import all Examples.PRFTagReader.Network.Kernel
import all Examples.PRFTagReader.NetworkUnlinkability
import all Examples.PRFTagReader.PRFReductions
import all Examples.PRFTagReader.PRFReductions.IdealHandlers
import all Examples.PRFTagReader.PRFReductions.Reductions
import all Examples.PRFTagReader.PRFReductions.Structural
import all Examples.PRFTagReader.ReductionBudgets
import all Examples.PRFTagReader.Table
import all Examples.PRFTagReader.UnlinkReduction
import all Examples.PRGfromPRF
import all Examples.ProgramLogic.ProofMode
import all Examples.ProgramLogic.RandomOracleRouting
import all Examples.ProgramLogic.RandomOracleWiring
import all Examples.ProgramLogic.UnaryStep
import all HashSig.SLHDSA.Fors
import all HashSig.SLHDSA.GeneralScheme
import all HashSig.SLHDSA.Hypertree
import all HashSig.SLHDSA.HypertreeGeneral
import all HashSig.SLHDSA.Oracle
import all HashSig.SLHDSA.Primitives
import all HashSig.SLHDSA.RandomOracle
import all HashSig.SLHDSA.Scheme
import all HashSig.SLHDSA.Security.TraceTargets
import all HashSig.SLHDSA.Wots
import all HashSig.SLHDSA.Xmss
import all LatticeCrypto.HardnessAssumptions.ShortIntegerSolution
import all LatticeCrypto.MLDSA.SecurityNMA
import all VCVio.CryptoFoundations.AKE.UAKE.Defs
import all VCVio.CryptoFoundations.AsymmEncAlg.INDCCA
import all VCVio.CryptoFoundations.AsymmEncAlg.INDCPA.Oracle
import all VCVio.CryptoFoundations.Asymptotics.OracleClosure
import all VCVio.CryptoFoundations.FiatShamir.Sigma
import all VCVio.CryptoFoundations.FiatShamir.Sigma.CmaToNma
import all VCVio.CryptoFoundations.FiatShamir.Sigma.Fork
import all VCVio.CryptoFoundations.FiatShamir.Sigma.KnowledgeExtraction
import all VCVio.CryptoFoundations.FiatShamir.Sigma.Reductions
import all VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.Bridge
import all VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.Chain.ForkBounds
import all VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.Chain.Reduction
import all VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.Chain.Simulation
import all VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.Compatibility
import all VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.Games
import all VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.Hops
import all VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.Spec
import all VCVio.CryptoFoundations.FiatShamir.WithAbort
import all VCVio.CryptoFoundations.FiatShamir.WithAbort.Cost
import all VCVio.CryptoFoundations.FiatShamir.WithAbort.ExpectedCost
import all VCVio.CryptoFoundations.Fischlin.Completeness
import all VCVio.CryptoFoundations.Fischlin.CostAccounting
import all VCVio.CryptoFoundations.Fischlin.Defs
import all VCVio.CryptoFoundations.Fischlin.ExpectedCost
import all VCVio.CryptoFoundations.Fischlin.ExpectedSigningCost
import all VCVio.CryptoFoundations.Fischlin.ExtractionGuarantee
import all VCVio.CryptoFoundations.Fischlin.KnowledgeSoundness.Extraction
import all VCVio.CryptoFoundations.Fischlin.KnowledgeSoundness.Induction
import all VCVio.CryptoFoundations.Fischlin.KnowledgeSoundness.Potential
import all VCVio.CryptoFoundations.FujisakiOkamoto.Composed
import all VCVio.CryptoFoundations.FujisakiOkamoto.Defs
import all VCVio.CryptoFoundations.FujisakiOkamoto.TTransform
import all VCVio.CryptoFoundations.FujisakiOkamoto.UTransform
import all VCVio.CryptoFoundations.GPVHashAndSign.AppendQuery
import all VCVio.CryptoFoundations.GPVHashAndSign.Basic
import all VCVio.CryptoFoundations.GPVHashAndSign.CollisionTelescope
import all VCVio.CryptoFoundations.GPVHashAndSign.CombinedHandler
import all VCVio.CryptoFoundations.GPVHashAndSign.EmbedIndex
import all VCVio.CryptoFoundations.GPVHashAndSign.Factorization
import all VCVio.CryptoFoundations.GPVHashAndSign.FlagHandlers
import all VCVio.CryptoFoundations.GPVHashAndSign.GameIdentification
import all VCVio.CryptoFoundations.GPVHashAndSign.GameRuns
import all VCVio.CryptoFoundations.GPVHashAndSign.TapeFactorization
import all VCVio.CryptoFoundations.GPVHashAndSign.TrapCount
import all VCVio.CryptoFoundations.GPVHashAndSign.TrapProjection
import all VCVio.CryptoFoundations.GPVHashAndSign.VerificationBridge
import all VCVio.CryptoFoundations.HardnessAssumptions.CollisionResistance
import all VCVio.CryptoFoundations.HardnessAssumptions.KeyedHash.ITSR
import all VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.Collection
import all VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.FinalValidity
import all VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.OpenPREFromTCRDSPR
import all VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTDSPR
import all VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTDSPRFinalValidity
import all VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTOpenPREFinalValidity
import all VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTPRE
import all VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTPREFinalValidity
import all VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTRTCR
import all VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCR
import all VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCRFinalValidity
import all VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTUD
import all VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTUDFinalValidity
import all VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.ToFinalValidity.Core
import all VCVio.CryptoFoundations.KeyEncapMech
import all VCVio.CryptoFoundations.MacAlg
import all VCVio.CryptoFoundations.MerkleTree.Addressed.Monadic
import all VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Monadic
import all VCVio.CryptoFoundations.MerkleTree.HashForest.Binary
import all VCVio.CryptoFoundations.MerkleTree.HashForest.Defs
import all VCVio.CryptoFoundations.MerkleTree.Hashing.Defs
import all VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.Addressed
import all VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.Defs
import all VCVio.CryptoFoundations.MerkleTree.Inductive.Defs
import all VCVio.CryptoFoundations.PRF
import all VCVio.CryptoFoundations.SignatureAlg
import all VCVio.CryptoFoundations.SymmEncAlg.Deterministic

/-!
# Coverage and usefulness of `derive_handler_specs` on the scheme handlers

**Coverage.** Every constant declared under `VCVio.CryptoFoundations`, `Examples`, `HashSig` or
`LatticeCrypto` whose type ends in `QueryImpl spec m` is run through the derivation of
`derive_handler_specs` without keeping its lemmas. The modules that mention `QueryImpl` are
imported with `import all`, so private and unexposed handlers are seen as in their own module,
where the command is meant to be run. Per handler the report gives the branches derived over the
branches found, the lemmas, the time, the failure classes of the skipped branches, and the
branches whose equation is stuck on a handler combinator (a sum or a composition applied to the
query).

**Usefulness.** The hand-written one-step equations `(h ps q).run s = _` and `h ps q = _` of the
route census (`route = handler`, without the declarations reserved for the experiment's
measurements) are restated by their types and closed, if possible, by one-line tactics over the
derived lemmas of the handlers in the statement (`derived`), and over the handler definitions
themselves (`base`): `simp only [D]`, `simp [D]`, and after `intros`, `simp [D, *]`,
`simp_all [D]` and `split <;> simp_all [D]`. Whether `intros; rfl` closes the equation is
reported beside, since such hits owe nothing to the derived lemmas.
-/

public section

open Lean Meta Elab Term OracleComp.ProgramLogic.HandlerSpecs

/-- The handler constants of the scheme libraries, with their modules. -/
meta def schemeHandlers : MetaM (Array (Name × Name)) := do
  let env ← getEnv
  let roots := [`VCVio.CryptoFoundations, `Examples, `HashSig, `LatticeCrypto]
  let mut out := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless roots.any (·.isPrefixOf mod) do continue
    if (privateToUserName n).isInternalDetail || ci.isTheorem ||
        ci matches .ctorInfo _ | .recInfo _ | .inductInfo _ then
      continue
    if ← forallTelescope ci.type fun _ b => return b.isAppOfArity ``QueryImpl 3 then
      out := out.push (n, mod)
  return out.qsort (·.1.toString < ·.1.toString)

/-- Whether the right side of a generated equation still applies a sum or a composition of
handlers to a query. -/
meta def stuck (s : Spec) : MetaM Bool :=
  forallTelescope s.type fun _ b => do
    let_expr Eq _ _ rhs := b | return false
    return (rhs.find? fun e => (e.isAppOfArity ``HAdd.hAdd 7 &&
      (e.getArg! 3).isAppOf ``QueryImpl.instHAddSumHAddOracleSpec) ||
      e.isAppOf ``QueryImpl.compose).isSome

run_meta do
  let hs ← schemeHandlers
  let mut ok : Nat := 0
  let mut clean : Nat := 0
  let mut hist : Std.HashMap String Nat := {}
  let mut lines : Array String := #[]
  let mut totalMs : Nat := 0
  let mut maxMs : Nat := 0
  let mut lemmas : Nat := 0
  for (h, mod) in hs do
    let rep ← withCurrHeartbeats <| try withoutModifyingEnv (derive h)
      catch ex => pure { handler := h, failures := #[("-", "error", ex.toMessageData)] }
    let nStuck := (← rep.specs.filterM stuck).size
    if rep.derived > 0 then ok := ok + 1
    if rep.derived > 0 && nStuck == 0 && rep.derived == rep.branches then clean := clean + 1
    totalMs := totalMs + rep.ms
    maxMs := max maxMs rep.ms
    lemmas := lemmas + rep.specs.size
    let classes := rep.failures.map (·.2.1) |>.toList.eraseDups
    let cls := if rep.derived > 0 then "ok" else classes.headD "none"
    hist := hist.insert cls (hist.getD cls 0 + 1)
    lines := lines.push s!"{h} [{mod}] {rep.derived}/{rep.branches} lemmas={rep.specs.size} \
      stuck={nStuck} {rep.ms}ms {classes}"
  logInfo m!"{ok}/{hs.size} handlers with ≥ 1 branch derived, {clean} with every branch derived \
    and none stuck; {lemmas} lemmas; {totalMs} ms in all, at most {maxMs} ms per handler\n\
    {hist.toList}\n{"\n".intercalate lines.toList}"

/-- The handler of a one-step equation `∀ xs, (h ps q).run s = _` or `∀ xs, h ps q = _`. -/
meta def stepHandler? (type : Expr) : MetaM (Option Name) :=
  forallTelescope type fun _ b => do
    let_expr Eq _ lhs _ := b | return none
    let app := if lhs.isAppOfArity ``StateT.run 5 then lhs.getArg! 3 else lhs
    let .const h _ := app.getAppFn | return none
    if ← forallTelescope (← getConstInfo h).type fun ps b =>
        return b.isAppOfArity ``QueryImpl 3 && app.getAppNumArgs == ps.size + 1 then
      return some h
    return none

/-- Whether `tac` closes `type`, on a fresh heartbeat budget and leaving no messages. -/
meta def closes (type : Expr) (tac : TSyntax `tactic) : TermElabM Bool := do
  let mvar ← mkFreshExprMVar type
  let msgs ← Core.getMessageLog
  let ok ← tryCatchRuntimeEx (withCurrHeartbeats do
      let gs ← Tactic.run mvar.mvarId! (Tactic.evalTactic tac)
      return gs.isEmpty && !(← instantiateMVars mvar).hasSorry &&
        !(← Core.getMessageLog).hasErrors)
    fun _ => return false
  Core.setMessageLog msgs
  return ok

/-- The first one-line tactic over the lemmas or definitions `ns` that closes `type`. -/
meta def ladder (type : Expr) (ns : Array Name) : TermElabM String := do
  let ls ← ns.mapM fun d => `(Lean.Parser.Tactic.simpLemma| $(mkIdent d):ident)
  let star ← `(Lean.Parser.Tactic.simpStar| *)
  let a : Array (TSyntax [``Lean.Parser.Tactic.simpStar, ``Lean.Parser.Tactic.simpErase,
    ``Lean.Parser.Tactic.simpLemma]) := ls.map (⟨·.raw⟩)
  let a' : Array (TSyntax [``Lean.Parser.Tactic.simpErase, ``Lean.Parser.Tactic.simpLemma]) :=
    ls.map (⟨·.raw⟩)
  let aStar := a.push ⟨star.raw⟩
  for (nm, tac) in #[("simp only", ← `(tactic| simp only [$a,*])),
      ("simp", ← `(tactic| simp [$a,*])),
      ("simp *", ← `(tactic| (intros; simp [$aStar,*]))),
      ("simp_all", ← `(tactic| (intros; simp_all [$a',*]))),
      ("split", ← `(tactic| (intros; split <;> simp_all [$a',*])))] do
    if ← closes type tac then return nm
  return "FAIL"

/-- The hand-written one-step equations of the census, with their lengths in lines. -/
meta def handWritten : Array (Name × Nat) := #[
  (`GPVHashAndSign.reductionImpl_run_inl_inl, 6),
  (`TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.openOracle_run, 5),
  (`GPVHashAndSign.progGameRunImplTape_run_read_eq_progGameRunImplNoRec, 12),
  (`TweakableHash.SM_DT_UD_challengeOracle_run_of_fresh_ideal, 8),
  (`GPVHashAndSign.embedTrapIdxSigImpl_run_inl_inr, 31),
  (`GPVHashAndSign.gpvRealImplFlagFresh_run_inl, 7),
  (`TweakableHash.SM_DT_DSPR_challengeOracle_run_of_full, 5),
  (`GPVHashAndSign.progGameRunImplTape_run_read, 11),
  (`TweakableHash.SM_DT_DSPR_challengeOracle_run_of_reused, 7),
  (`GPVHashAndSign.gpvRealImpl_run_unif, 8),
  (`PRFTagReader.unlinkToMultiplePRFTagImpl_run_of_lt, 15),
  (`GPVHashAndSign.gpvRealImplTape_run_sign_cons, 12),
  (`PRFTagReader.unlinkToSinglePRFTagImpl_run_of_lt, 17),
  (`GPVHashAndSign.gpvImplTape_run_read_hit_eq, 19),
  (`TweakableHash.SM_DT_DSPR_challengeOracle_run_of_fresh, 7),
  (`GPVHashAndSign.reductionImpl_run_inl_inr, 19),
  (`AsymmEncAlg.IND_CPA_hybridChallengeOracleLR_counted_run_some, 8),
  (`TweakableHash.SM_DT_PRE_challengeOracle_run_of_collection_clash, 7),
  (`GPVHashAndSign.gpvRealImpl_run_sign, 35),
  (`GPVHashAndSign.progGameRunImplTapeFlag_run_inl, 7),
  (`GPVHashAndSign.progGameRunImplNoRec_run_read, 16),
  (`TweakableHash.SM_DT_PRE_SourceFinalValidity.challengeOracle_run, 6),
  (`GPVHashAndSign.progGameRunImplCombinedTrapCount_run_inl_inl, 6),
  (`GPVHashAndSign.gpvRealImplTape_run_read_eq_gpvRealImpl, 11),
  (`GPVHashAndSign.embedTrapFreshIdxSigImpl_run_inr, 17),
  (`GPVHashAndSign.progGameRunImplCombinedTrapCount_run_inl_inr, 15),
  (`GPVHashAndSign.embedTrapFreshIdxSigImpl_run_inl_inr, 24),
  (`GPVHashAndSign.progGameRunImplNoRecFlag_run_inr, 9),
  (`TweakableHash.SM_DT_UD_SourceFinalValidity.challengeOracle_run, 6),
  (`TweakableHash.SM_DT_TCR_challengeOracle_run_of_fresh, 7),
  (`PRFTagReader.unlinkToMultiplePRFReaderImpl_run, 13),
  (`GPVHashAndSign.gpvRealImplFresh_run_inl, 7),
  (`GPVHashAndSign.gpvRealImplFresh_run_inr, 9),
  (`GPVHashAndSign.progGameRunImplCombined_run_inl_inl, 6),
  (`GPVHashAndSign.embedAtIndexImpl_run_inl_inr, 25),
  (`PRFTagReader.unlinkToSinglePRFTagImpl_run_of_not_lt, 8),
  (`GPVHashAndSign.embedTrapIdxSigImpl_run_inr, 17),
  (`GPVHashAndSign.progGameRunImplTape_run_unif_eq_progGameRunImplNoRec, 9),
  (`GPVHashAndSign.embedTrapIdxImpl_run_inl_inl, 5),
  (`TweakableHash.SM_DT_DSPR_challengeOracle_run_of_collection_clash, 7),
  (`GPVHashAndSign.gpvRealImplTapeFlag_run_inl, 7),
  (`TweakableHash.SM_DT_UD_challengeOracle_run_of_fresh_real, 10),
  (`TweakableHash.ToFinalValidity.fused_run, 10),
  (`GPVHashAndSign.progGameRunImplCombinedTrapCount_run_inr, 14),
  (`TweakableHash.SM_DT_UD_challengeOracle_run_of_full, 5),
  (`GPVHashAndSign.embedTrapImpl_run_step_indep_of_target, 28),
  (`FiatShamir.Fork.roImpl_run_none, 8),
  (`GPVHashAndSign.progGameRunImplNoRecFlagFresh_run_inr, 9),
  (`TweakableHash.SM_DT_RTCR_challengeOracle_run_of_fresh, 11),
  (`GPVHashAndSign.reductionImpl_run_inr, 12),
  (`GPVHashAndSign.embedTrapFreshImpl_run_inl_inl, 5),
  (`KeyedHash.ITSRTargetOracle_run, 5),
  (`TweakableHash.SM_DT_PRE_challengeOracle_run_of_full, 5),
  (`PRFTagReader.unlinkToMultiplePRFTagImpl_run_of_not_lt, 8),
  (`GPVHashAndSign.progGameRunImplNoRecFlag_run_inl, 7),
  (`GPVHashAndSign.progGameRunImplCombinedTrap_run_inr, 13),
  (`GPVHashAndSign.embedTrapImpl_run_inl_inl, 6),
  (`GPVHashAndSign.embedTrapIdxSigImpl_run_inl_inl, 6),
  (`hidingImpl_agree, 19),
  (`GPVHashAndSign.gpvImplTape_run_unif_eq, 13),
  (`GPVHashAndSign.gpvRealImplFlagFresh_run_inr, 9),
  (`GPVHashAndSign.progGameRunImplTape_run_unif, 5),
  (`GPVHashAndSign.progGameRunImplNoRec_run_inl_inr, 16),
  (`GPVHashAndSign.embedTrapIdxSigImpl_run_step_eq_embedTrapFreshIdxSig, 21),
  (`PRFTagReader.unlinkToSinglePRFReaderImpl_run, 14),
  (`GPVHashAndSign.progGameRunImplNoRec_run_inl_inl, 5),
  (`TweakableHash.SM_DT_UD_challengeOracle_run_of_reused, 6),
  (`FiatShamir.Fork.unifForward_run, 7),
  (`GPVHashAndSign.embedAtIndexImpl_run_inl_inl, 6),
  (`TweakableHash.SM_DT_TCR_challengeOracle_run_of_reused, 7),
  (`TweakableHash.SM_DT_UD_challengeOracle_run_of_collection_clash, 7),
  (`GPVHashAndSign.progGameRunImplNoRec_run_unif, 5),
  (`GPVHashAndSign.progGameRunImplTape_run_sign_cons, 10),
  (`GPVHashAndSign.embedTrapIdxImpl_run_step_eq_embedTrapFreshIdx, 20),
  (`GPVHashAndSign.embedTrapIdxImpl_run_inr, 17),
  (`TweakableHash.SM_DT_PRE_challengeOracle_run_of_fresh, 8),
  (`TweakableHash.SourceFinalValidity.collectionOracle_run, 8),
  (`GPVHashAndSign.embedTrapFreshImpl_run_inr, 14),
  (`GPVHashAndSign.gpvRealImplTapeFlag_run_inr, 10),
  (`GPVHashAndSign.gpvRealImplTape_run_read, 7),
  (`GPVHashAndSign.embedTrapFreshIdxSigImpl_run_inl_inl, 5),
  (`GPVHashAndSign.gpvRealImplFlag_run_inl, 7),
  (`GPVHashAndSign.progGameRunImplCombinedTrap_run_inl_inr, 13),
  (`GPVHashAndSign.embedTrapFreshIdxImpl_run_inl_inl, 5),
  (`TweakableHash.collectionOracle_run_of_challenge_clash, 8),
  (`TweakableHash.SM_DT_PRE_challengeOracle_run_of_reused, 7),
  (`TweakableHash.collectionOracle_run_of_fresh, 7),
  (`AsymmEncAlg.IND_CPA_hybridChallengeOracleLR_counted_run_none, 10),
  (`GPVHashAndSign.embedTrapIdxImpl_run_inl_inr, 29),
  (`TweakableHash.SM_DT_TCR_challengeOracle_run_of_collection_clash, 7),
  (`TweakableHash.SM_DT_TCR_SourceFinalValidity.challengeOracle_run, 5),
  (`AsymmEncAlg.IND_CPA_hybridLR_counted_run_eq_of_le, 15),
  (`TweakableHash.SM_DT_TCR_challengeOracle_run_of_full, 5),
  (`GPVHashAndSign.progGameRunImplCombined_run_inr, 11),
  (`GPVHashAndSign.progGameRunImplTapeFlag_run_inr, 9),
  (`GPVHashAndSign.progGameRunImplNoRec_run_sign, 20),
  (`GPVHashAndSign.progGameRunImplCombinedTrap_run_inl_inl, 6),
  (`TweakableHash.SM_DT_DSPR_SourceFinalValidity.challengeOracle_run, 5),
  (`TweakableHash.SM_DT_RTCR_challengeOracle_run_of_reused, 8),
  (`GPVHashAndSign.gpvRealImplFlag_run_inr, 11),
  (`GPVHashAndSign.embedTrapFreshImpl_run_inl_inr, 21),
  (`GPVHashAndSign.progGameRunImplNoRecFlagFresh_run_inl, 7),
  (`GPVHashAndSign.embedTrapImpl_run_inr, 14),
  (`GPVHashAndSign.gpvRealImplTape_run_unif_eq_gpvRealImpl, 11),
  (`GPVHashAndSign.gpvRealImplTape_run_unif, 5),
  (`GPVHashAndSign.gpvRealImplFlagFresh_run_inl_trapdoorSwap, 12),
  (`GPVHashAndSign.embedTrapImpl_run_inl_inr, 25),
  (`GPVHashAndSign.embedAtIndexImpl_run_inr, 13),
  (`GPVHashAndSign.embedTrapImpl_run_step_eq_embedTrapFresh, 24),
  (`GPVHashAndSign.embedTrapFreshIdxImpl_run_inl_inr, 22),
  (`TweakableHash.SM_DT_RTCR_challengeOracle_run_of_full, 4),
  (`GPVHashAndSign.gpvRealImpl_run_read, 9),
  (`FiatShamir.Fork.roImpl_run_some, 6),
  (`TweakableHash.SM_DT_UD_challengeOracle_run_of_refused, 12),
  (`GPVHashAndSign.progGameRunImplCombined_run_inl_inr, 12)
]

run_cmd Command.liftTermElabM do
  let mut out := #[]
  let mut hits : Nat := 0
  let mut baseHits : Nat := 0
  let mut hitLines : Nat := 0
  let mut nonRfl : Nat := 0
  let mut handlers : Array Name := #[]
  for (t, len) in handWritten do
    let some ci := (← getEnv).find? t | out := out.push s!"{t} missing"; continue
    let some h ← withCurrHeartbeats (stepHandler? ci.type) | out := out.push s!"{t} shape"; continue
    let r ← closes ci.type (← `(tactic| (intros; rfl)))
    let (d, b) ← withoutModifyingEnv <| withCurrHeartbeats do
      let mut hs := #[h]
      for c in ci.type.getUsedConstants do
        if !hs.contains c then
          if ← forallTelescope (← getConstInfo c).type fun _ b =>
              return b.isAppOfArity ``QueryImpl 3 then
            hs := hs.push c
      let mut specs := #[]
      for c in hs do specs := specs ++ (← derive c).specs.map (·.name)
      return (← ladder ci.type specs, ← ladder ci.type hs)
    if d != "FAIL" then
      hits := hits + 1
      hitLines := hitLines + len
      unless handlers.contains h do handlers := handlers.push h
      unless r do nonRfl := nonRfl + 1
    if b != "FAIL" then baseHits := baseHits + 1
    out := out.push s!"{t} {len} rfl={r} derived={d} base={b}"
  logInfo m!"derived: {hits}/{handWritten.size} closed in one line ({nonRfl} not by `rfl`; \
    {hitLines} hand-written lines, {handlers.size} handlers); base: {baseHits}/{handWritten.size}\n\
    {"\n".intercalate out.toList}"
