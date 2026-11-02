/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public meta import HashSigTest.SLHDSA.Refactor.Capture
public import VCVio.CryptoFoundations.SignatureAlg.CountedExperiment.Unforgeability
import Lean.Data.Json

/-! # Generic counted unforgeability domination

Message freshness and returned-pair freshness observe the same counted total-signature
experiment. Oracle-index and runtime-carrier universes remain independent, and the additive
policy is arbitrary. The comparison carries no query-budget or lifetime premise.
-/

open Lean Elab Command Meta SLHDSA.Refactor.R0
open OracleComp OracleSpec SignatureAlg

public meta section

namespace HashSigTest.SLHDSA.Refactor.Recovery.Generic

/-- Decode the closed counted-domination proposition with its independent ordered universes. -/
def readGoal : CommandElabM (List Name × Expr) := do
  let raw ← ofExcept (Json.parse r####"
["forall",["str",["anonymous"],"ι"],"implicit",["sort",["succ",["param",["str",
["anonymous"],"i"]]]],["forall",["str",["anonymous"],"spec"],"implicit",["app",["const",
["str",["anonymous"],"OracleSpec"],[["param",["str",["anonymous"],"i"]],["zero"]]],
["bvar",0]],["forall",["str",["anonymous"],"M"],"implicit",["sort",["succ",["zero"]]],
["forall",["str",["anonymous"],"PK"],"implicit",["sort",["succ",["zero"]]],["forall",
["str",["anonymous"],"SK"],"implicit",["sort",["succ",["zero"]]],["forall",["str",
["anonymous"],"S"],"implicit",["sort",["succ",["zero"]]],["forall",["str",["anonymous"],
"C"],"implicit",["sort",["succ",["zero"]]],["forall",["num",["str",["str",["num",["str",
["str",["str",["anonymous"],"inst"],"_@"],"GenericHeader"],646049674],"_hygCtx"],"_hyg"],
13],"instance",["app",["const",["str",["anonymous"],"AddMonoid"],[["zero"]]],["bvar",0]],
["forall",["str",["anonymous"],"policy"],"explicit",["forall",["num",["str",["str",["str",
["str",["anonymous"],"a"],"_@"],"_internal"],"_hyg"],0],"explicit",["app",["app",["app",
["const",["str",["str",["str",["anonymous"],"SignatureAlg"],"SigningView"],"Event"],
[["zero"],["param",["str",["anonymous"],"i"]]]],["bvar",7]],["bvar",6]],["bvar",5]],
["bvar",2]],["forall",["str",["anonymous"],"sigAlg"],"implicit",["app",["app",["app",
["app",["app",["app",["const",["str",["anonymous"],"SignatureAlg"],[["param",["str",
["anonymous"],"i"]]]],["app",["app",["const",["str",["anonymous"],"OracleComp"],[["param",
["str",["anonymous"],"i"]],["zero"],["zero"]]],["bvar",8]],["bvar",7]]],["app",["const",
["str",["str",["str",["anonymous"],"PFunctor"],"FreeM"],"instMonad"],[["param",["str",
["anonymous"],"i"]],["zero"],["zero"]]],["app",["app",["const",["str",["str",
["anonymous"],"OracleSpec"],"toPFunctor"],[["param",["str",["anonymous"],"i"]],["zero"]]],
["bvar",8]],["bvar",7]]]],["bvar",6]],["bvar",5]],["bvar",4]],["bvar",3]],["forall",
["str",["anonymous"],"runtime"],"explicit",["app",["app",["const",["str",["anonymous"],
"ProbCompRuntime"],[["param",["str",["anonymous"],"i"]],["param",["str",["anonymous"],
"r"]]]],["app",["app",["const",["str",["anonymous"],"OracleComp"],[["param",["str",
["anonymous"],"i"]],["zero"],["zero"]]],["bvar",9]],["bvar",8]]],["app",["const",["str",
["str",["str",["anonymous"],"PFunctor"],"FreeM"],"instMonad"],[["param",["str",
["anonymous"],"i"]],["zero"],["zero"]]],["app",["app",["const",["str",["str",
["anonymous"],"OracleSpec"],"toPFunctor"],[["param",["str",["anonymous"],"i"]],["zero"]]],
["bvar",9]],["bvar",8]]]],["forall",["str",["anonymous"],"adv"],"explicit",["app",["app",
["app",["app",["app",["app",["app",["const",["str",["str",["anonymous"],"SignatureAlg"],
"UnforgeableAdversary"],[["param",["str",["anonymous"],"i"]]]],["bvar",10]],["bvar",9]],
["bvar",8]],["bvar",7]],["bvar",6]],["bvar",5]],["bvar",1]],["app",["app",["app",["app",
["const",["str",["str",["anonymous"],"LE"],"le"],[["zero"]]],["const",["str",
["anonymous"],"ENNReal"],[]]],["const",["str",["str",["anonymous"],"ENNReal"],"instLE"],
[]]],["app",["app",["app",["app",["app",["app",["const",["str",["str",["anonymous"],
"DFunLike"],"coe"],[["succ",["zero"]],["succ",["zero"]],["succ",["zero"]]]],["app",["app",
["const",["str",["str",["anonymous"],"MeasureTheory"],"Measure"],[["zero"]]],["const",
["str",["anonymous"],"Bool"],[]]],["const",["str",["str",["anonymous"],"Bool"],
"instMeasurableSpace"],[]]]],["app",["const",["str",["anonymous"],"Set"],[["zero"]]],
["const",["str",["anonymous"],"Bool"],[]]]],["lam",["num",["str",["str",["num",["str",
["str",["str",["str",["str",["str",["anonymous"],"x"],"_@"],"Mathlib"],"Basic"],
"FunLike"],"Basic"],2582841819],"_hygCtx"],"_hyg"],11],"explicit",["app",["const",["str",
["anonymous"],"Set"],[["zero"]]],["const",["str",["anonymous"],"Bool"],[]]],["const",
["str",["anonymous"],"ENNReal"],[]]]],["app",["app",["const",["str",["str",["str",
["anonymous"],"MeasureTheory"],"Measure"],"instFunLike"],[["zero"]]],["const",["str",
["anonymous"],"Bool"],[]]],["const",["str",["str",["anonymous"],"Bool"],
"instMeasurableSpace"],[]]]],["app",["app",["app",["app",["app",["app",["const",["str",
["str",["anonymous"],"ProbCompRuntime"],"evalDist"],[["param",["str",["anonymous"],"i"]],
["param",["str",["anonymous"],"r"]]]],["app",["app",["const",["str",["anonymous"],
"OracleComp"],[["param",["str",["anonymous"],"i"]],["zero"],["zero"]]],["bvar",11]],
["bvar",10]]],["app",["const",["str",["str",["str",["anonymous"],"PFunctor"],"FreeM"],
"instMonad"],[["param",["str",["anonymous"],"i"]],["zero"],["zero"]]],["app",["app",
["const",["str",["str",["anonymous"],"OracleSpec"],"toPFunctor"],[["param",["str",
["anonymous"],"i"]],["zero"]]],["bvar",11]],["bvar",10]]]],["const",["str",["anonymous"],
"Bool"],[]]],["bvar",1]],["const",["str",["str",["anonymous"],"Bool"],
"instMeasurableSpace"],[]]],["app",["app",["app",["app",["app",["app",["const",["str",
["str",["anonymous"],"Functor"],"map"],[["zero"],["param",["str",["anonymous"],"i"]]]],
["app",["app",["const",["str",["anonymous"],"OracleComp"],[["param",["str",["anonymous"],
"i"]],["zero"],["zero"]]],["bvar",11]],["bvar",10]]],["app",["const",["str",["str",["str",
["anonymous"],"PFunctor"],"FreeM"],"instFunctor"],[["param",["str",["anonymous"],"i"]],
["zero"],["zero"]]],["app",["app",["const",["str",["str",["anonymous"],"OracleSpec"],
"toPFunctor"],[["param",["str",["anonymous"],"i"]],["zero"]]],["bvar",11]],["bvar",10]]]],
["app",["app",["app",["app",["const",["str",["str",["str",["anonymous"],"SignatureAlg"],
"SigningView"],"Observation"],[]],["bvar",9]],["bvar",6]],["bvar",6]],["bvar",5]]],
["const",["str",["anonymous"],"Bool"],[]]],["lam",["str",["anonymous"],"observed"],
"explicit",["app",["app",["app",["app",["const",["str",["str",["str",["anonymous"],
"SignatureAlg"],"SigningView"],"Observation"],[]],["bvar",9]],["bvar",6]],["bvar",6]],
["bvar",5]],["app",["app",["const",["str",["str",["anonymous"],"Bool"],"and"],[]],["app",
["const",["str",["str",["anonymous"],"Bool"],"not"],[]],["app",["app",["app",["app",
["app",["const",["str",["str",["str",["anonymous"],"OracleSpec"],"QueryLog"],
"wasQueried"],[["zero"],["zero"]]],["bvar",10]],["app",["app",["const",["str",["str",
["anonymous"],"OracleSpec"],"ofFn"],[["zero"],["zero"]]],["bvar",10]],["lam",["num",
["str",["str",["num",["str",["str",["str",["str",["str",["str",["anonymous"],"x"],"_@"],
"VCVio"],"CryptoFoundations"],"SignatureAlg"],"SigningView"],3524018119],"_hygCtx"],
"_hyg"],32],"explicit",["bvar",10],["bvar",8]]]],["lam",["str",["anonymous"],"a"],
"explicit",["bvar",10],["lam",["str",["anonymous"],"b"],"explicit",["bvar",11],["app",
["const",["str",["str",["anonymous"],"Classical"],"propDecidable"],[]],["app",["app",
["app",["const",["str",["anonymous"],"Eq"],[["succ",["zero"]]]],["bvar",12]],["bvar",1]],
["bvar",0]]]]]],["app",["app",["app",["app",["const",["str",["str",["str",["str",
["anonymous"],"SignatureAlg"],"SigningView"],"Outcome"],"rawLog"],[]],["bvar",10]],
["bvar",7]],["bvar",7]],["app",["app",["app",["app",["app",["const",["str",["str",["str",
["str",["anonymous"],"SignatureAlg"],"SigningView"],"Observation"],"toOutcome"],[]],
["bvar",10]],["bvar",7]],["bvar",7]],["bvar",6]],["bvar",0]]]],["app",["app",["app",
["const",["str",["str",["anonymous"],"Prod"],"fst"],[["zero"],["zero"]]],["bvar",10]],
["bvar",7]],["app",["app",["app",["app",["const",["str",["str",["str",["str",
["anonymous"],"SignatureAlg"],"SigningView"],"Outcome"],"forgery"],[]],["bvar",10]],
["bvar",7]],["bvar",7]],["app",["app",["app",["app",["app",["const",["str",["str",["str",
["str",["anonymous"],"SignatureAlg"],"SigningView"],"Observation"],"toOutcome"],[]],
["bvar",10]],["bvar",7]],["bvar",7]],["bvar",6]],["bvar",0]]]]]]],["app",["app",["app",
["app",["const",["str",["str",["str",["str",["anonymous"],"SignatureAlg"],"SigningView"],
"Outcome"],"verified"],[]],["bvar",10]],["bvar",7]],["bvar",7]],["app",["app",["app",
["app",["app",["const",["str",["str",["str",["str",["anonymous"],"SignatureAlg"],
"SigningView"],"Observation"],"toOutcome"],[]],["bvar",10]],["bvar",7]],["bvar",7]],
["bvar",6]],["bvar",0]]]]]],["app",["app",["app",["app",["app",["app",["app",["app",
["app",["app",["app",["app",["const",["str",["str",["str",["anonymous"],"SignatureAlg"],
"SigningView"],"countedExperiment"],[["param",["str",["anonymous"],"i"]]]],["bvar",11]],
["bvar",10]],["bvar",9]],["bvar",8]],["bvar",7]],["bvar",6]],["bvar",6]],["bvar",5]],
["bvar",4]],["bvar",3]],["app",["app",["app",["app",["app",["app",["app",["const",["str",
["str",["str",["anonymous"],"SignatureAlg"],"SigningView"],"ofTotal"],[["param",["str",
["anonymous"],"i"]]]],["bvar",9]],["bvar",8]],["bvar",7]],["bvar",6]],["app",["app",
["const",["str",["anonymous"],"OracleComp"],[["param",["str",["anonymous"],"i"]],["zero"],
["zero"]]],["bvar",11]],["bvar",10]]],["app",["const",["str",["str",["str",["anonymous"],
"PFunctor"],"FreeM"],"instMonad"],[["param",["str",["anonymous"],"i"]],["zero"],
["zero"]]],["app",["app",["const",["str",["str",["anonymous"],"OracleSpec"],"toPFunctor"],
[["param",["str",["anonymous"],"i"]],["zero"]]],["bvar",11]],["bvar",10]]]],["bvar",2]]],
["app",["app",["app",["app",["app",["app",["app",["app",["const",["str",["str",["str",
["anonymous"],"SignatureAlg"],"UnforgeableAdversary"],"main"],[["param",["str",
["anonymous"],"i"]]]],["bvar",11]],["bvar",10]],["bvar",9]],["bvar",8]],["bvar",7]],
["bvar",6]],["bvar",2]],["bvar",0]]]]]],["app",["app",["app",["app",["const",["str",
["str",["anonymous"],"Singleton"],"singleton"],[["zero"],["zero"]]],["const",["str",
["anonymous"],"Bool"],[]]],["app",["const",["str",["anonymous"],"Set"],[["zero"]]],
["const",["str",["anonymous"],"Bool"],[]]]],["app",["const",["str",["str",["anonymous"],
"Set"],"instSingletonSet"],[["zero"]]],["const",["str",["anonymous"],"Bool"],[]]]],
["const",["str",["str",["anonymous"],"Bool"],"true"],[]]]]],["app",["app",["app",["app",
["app",["app",["const",["str",["str",["anonymous"],"DFunLike"],"coe"],[["succ",["zero"]],
["succ",["zero"]],["succ",["zero"]]]],["app",["app",["const",["str",["str",["anonymous"],
"MeasureTheory"],"Measure"],[["zero"]]],["const",["str",["anonymous"],"Bool"],[]]],
["const",["str",["str",["anonymous"],"Bool"],"instMeasurableSpace"],[]]]],["app",["const",
["str",["anonymous"],"Set"],[["zero"]]],["const",["str",["anonymous"],"Bool"],[]]]],
["lam",["num",["str",["str",["num",["str",["str",["str",["str",["str",["str",
["anonymous"],"x"],"_@"],"Mathlib"],"Basic"],"FunLike"],"Basic"],2582841819],"_hygCtx"],
"_hyg"],11],"explicit",["app",["const",["str",["anonymous"],"Set"],[["zero"]]],["const",
["str",["anonymous"],"Bool"],[]]],["const",["str",["anonymous"],"ENNReal"],[]]]],["app",
["app",["const",["str",["str",["str",["anonymous"],"MeasureTheory"],"Measure"],
"instFunLike"],[["zero"]]],["const",["str",["anonymous"],"Bool"],[]]],["const",["str",
["str",["anonymous"],"Bool"],"instMeasurableSpace"],[]]]],["app",["app",["app",["app",
["app",["app",["const",["str",["str",["anonymous"],"ProbCompRuntime"],"evalDist"],
[["param",["str",["anonymous"],"i"]],["param",["str",["anonymous"],"r"]]]],["app",["app",
["const",["str",["anonymous"],"OracleComp"],[["param",["str",["anonymous"],"i"]],["zero"],
["zero"]]],["bvar",11]],["bvar",10]]],["app",["const",["str",["str",["str",["anonymous"],
"PFunctor"],"FreeM"],"instMonad"],[["param",["str",["anonymous"],"i"]],["zero"],
["zero"]]],["app",["app",["const",["str",["str",["anonymous"],"OracleSpec"],"toPFunctor"],
[["param",["str",["anonymous"],"i"]],["zero"]]],["bvar",11]],["bvar",10]]]],["const",
["str",["anonymous"],"Bool"],[]]],["bvar",1]],["const",["str",["str",["anonymous"],
"Bool"],"instMeasurableSpace"],[]]],["app",["app",["app",["app",["app",["app",["const",
["str",["str",["anonymous"],"Functor"],"map"],[["zero"],["param",["str",["anonymous"],
"i"]]]],["app",["app",["const",["str",["anonymous"],"OracleComp"],[["param",["str",
["anonymous"],"i"]],["zero"],["zero"]]],["bvar",11]],["bvar",10]]],["app",["const",["str",
["str",["str",["anonymous"],"PFunctor"],"FreeM"],"instFunctor"],[["param",["str",
["anonymous"],"i"]],["zero"],["zero"]]],["app",["app",["const",["str",["str",
["anonymous"],"OracleSpec"],"toPFunctor"],[["param",["str",["anonymous"],"i"]],["zero"]]],
["bvar",11]],["bvar",10]]]],["app",["app",["app",["app",["const",["str",["str",["str",
["anonymous"],"SignatureAlg"],"SigningView"],"Observation"],[]],["bvar",9]],["bvar",6]],
["bvar",6]],["bvar",5]]],["const",["str",["anonymous"],"Bool"],[]]],["lam",["str",
["anonymous"],"observed"],"explicit",["app",["app",["app",["app",["const",["str",["str",
["str",["anonymous"],"SignatureAlg"],"SigningView"],"Observation"],[]],["bvar",9]],
["bvar",6]],["bvar",6]],["bvar",5]],["app",["app",["const",["str",["str",["anonymous"],
"Decidable"],"decide"],[]],["app",["app",["app",["app",["app",["const",["str",["str",
["str",["anonymous"],"SignatureAlg"],"SigningView"],"Wins"],[]],["bvar",10]],["bvar",7]],
["bvar",7]],["app",["app",["app",["app",["app",["app",["app",["app",["const",["str",
["str",["str",["anonymous"],"SignatureAlg"],"SigningView"],"readback"],[["param",["str",
["anonymous"],"i"]]]],["app",["app",["const",["str",["anonymous"],"OracleComp"],[["param",
["str",["anonymous"],"i"]],["zero"],["zero"]]],["bvar",12]],["bvar",11]]],["app",["const",
["str",["str",["str",["anonymous"],"PFunctor"],"FreeM"],"instMonad"],[["param",["str",
["anonymous"],"i"]],["zero"],["zero"]]],["app",["app",["const",["str",["str",
["anonymous"],"OracleSpec"],"toPFunctor"],[["param",["str",["anonymous"],"i"]],["zero"]]],
["bvar",12]],["bvar",11]]]],["bvar",10]],["bvar",9]],["bvar",8]],["bvar",7]],["bvar",7]],
["app",["app",["app",["app",["app",["app",["app",["const",["str",["str",["str",
["anonymous"],"SignatureAlg"],"SigningView"],"ofTotal"],[["param",["str",["anonymous"],
"i"]]]],["bvar",10]],["bvar",9]],["bvar",8]],["bvar",7]],["app",["app",["const",["str",
["anonymous"],"OracleComp"],[["param",["str",["anonymous"],"i"]],["zero"],["zero"]]],
["bvar",12]],["bvar",11]]],["app",["const",["str",["str",["str",["anonymous"],"PFunctor"],
"FreeM"],"instMonad"],[["param",["str",["anonymous"],"i"]],["zero"],["zero"]]],["app",
["app",["const",["str",["str",["anonymous"],"OracleSpec"],"toPFunctor"],[["param",["str",
["anonymous"],"i"]],["zero"]]],["bvar",12]],["bvar",11]]]],["bvar",3]]]],["app",["app",
["app",["app",["app",["const",["str",["str",["str",["anonymous"],"SignatureAlg"],
"SigningView"],"erase"],[]],["bvar",10]],["bvar",7]],["bvar",7]],["bvar",6]],["bvar",
0]]]],["app",["const",["str",["str",["anonymous"],"Classical"],"propDecidable"],[]],
["app",["app",["app",["app",["app",["const",["str",["str",["str",["anonymous"],
"SignatureAlg"],"SigningView"],"Wins"],[]],["bvar",10]],["bvar",7]],["bvar",7]],["app",
["app",["app",["app",["app",["app",["app",["app",["const",["str",["str",["str",
["anonymous"],"SignatureAlg"],"SigningView"],"readback"],[["param",["str",["anonymous"],
"i"]]]],["app",["app",["const",["str",["anonymous"],"OracleComp"],[["param",["str",
["anonymous"],"i"]],["zero"],["zero"]]],["bvar",12]],["bvar",11]]],["app",["const",["str",
["str",["str",["anonymous"],"PFunctor"],"FreeM"],"instMonad"],[["param",["str",
["anonymous"],"i"]],["zero"],["zero"]]],["app",["app",["const",["str",["str",
["anonymous"],"OracleSpec"],"toPFunctor"],[["param",["str",["anonymous"],"i"]],["zero"]]],
["bvar",12]],["bvar",11]]]],["bvar",10]],["bvar",9]],["bvar",8]],["bvar",7]],["bvar",7]],
["app",["app",["app",["app",["app",["app",["app",["const",["str",["str",["str",
["anonymous"],"SignatureAlg"],"SigningView"],"ofTotal"],[["param",["str",["anonymous"],
"i"]]]],["bvar",10]],["bvar",9]],["bvar",8]],["bvar",7]],["app",["app",["const",["str",
["anonymous"],"OracleComp"],[["param",["str",["anonymous"],"i"]],["zero"],["zero"]]],
["bvar",12]],["bvar",11]]],["app",["const",["str",["str",["str",["anonymous"],"PFunctor"],
"FreeM"],"instMonad"],[["param",["str",["anonymous"],"i"]],["zero"],["zero"]]],["app",
["app",["const",["str",["str",["anonymous"],"OracleSpec"],"toPFunctor"],[["param",["str",
["anonymous"],"i"]],["zero"]]],["bvar",12]],["bvar",11]]]],["bvar",3]]]],["app",["app",
["app",["app",["app",["const",["str",["str",["str",["anonymous"],"SignatureAlg"],
"SigningView"],"erase"],[]],["bvar",10]],["bvar",7]],["bvar",7]],["bvar",6]],["bvar",
0]]]]]]],["app",["app",["app",["app",["app",["app",["app",["app",["app",["app",["app",
["app",["const",["str",["str",["str",["anonymous"],"SignatureAlg"],"SigningView"],
"countedExperiment"],[["param",["str",["anonymous"],"i"]]]],["bvar",11]],["bvar",10]],
["bvar",9]],["bvar",8]],["bvar",7]],["bvar",6]],["bvar",6]],["bvar",5]],["bvar",4]],
["bvar",3]],["app",["app",["app",["app",["app",["app",["app",["const",["str",["str",
["str",["anonymous"],"SignatureAlg"],"SigningView"],"ofTotal"],[["param",["str",
["anonymous"],"i"]]]],["bvar",9]],["bvar",8]],["bvar",7]],["bvar",6]],["app",["app",
["const",["str",["anonymous"],"OracleComp"],[["param",["str",["anonymous"],"i"]],["zero"],
["zero"]]],["bvar",11]],["bvar",10]]],["app",["const",["str",["str",["str",["anonymous"],
"PFunctor"],"FreeM"],"instMonad"],[["param",["str",["anonymous"],"i"]],["zero"],
["zero"]]],["app",["app",["const",["str",["str",["anonymous"],"OracleSpec"],"toPFunctor"],
[["param",["str",["anonymous"],"i"]],["zero"]]],["bvar",11]],["bvar",10]]]],["bvar",2]]],
["app",["app",["app",["app",["app",["app",["app",["app",["const",["str",["str",["str",
["anonymous"],"SignatureAlg"],"UnforgeableAdversary"],"main"],[["param",["str",
["anonymous"],"i"]]]],["bvar",11]],["bvar",10]],["bvar",9]],["bvar",8]],["bvar",7]],
["bvar",6]],["bvar",2]],["bvar",0]]]]]],["app",["app",["app",["app",["const",["str",
["str",["anonymous"],"Singleton"],"singleton"],[["zero"],["zero"]]],["const",["str",
["anonymous"],"Bool"],[]]],["app",["const",["str",["anonymous"],"Set"],[["zero"]]],
["const",["str",["anonymous"],"Bool"],[]]]],["app",["const",["str",["str",["anonymous"],
"Set"],"instSingletonSet"],[["zero"]]],["const",["str",["anonymous"],"Bool"],[]]]],
["const",["str",["str",["anonymous"],"Bool"],"true"],[]]]]]]]]]]]]]]]]]
"####)
  let type ← ofExcept (decodeExpr raw)
  unless (← ofExcept (encodeExpr type)) == raw do
    throwError "Generic counted literal type roundtrip changed"
  if type == mkSort .zero || type.hasLooseBVars || type.hasFVar || type.hasMVar ||
      type.hasLevelMVar then
    throwError "A complete closed generic proposition is required"
  return ([`i, `r], type)

end HashSigTest.SLHDSA.Refactor.Recovery.Generic

public section

run_cmd do
  let (levels, type) ← HashSigTest.SLHDSA.Refactor.Recovery.Generic.readGoal
  unless levels == [`i, `r] do throwError "Independent raw universe order changed"
  let name := `HashSigTest.SLHDSA.Refactor.Recovery.Generic.genericCounted36
  if ((← getEnv).find? name).isSome then throwError "Duplicate generic counted theorem"
  let value ← liftTermElabM do
    Term.withDeclName name <| Term.withLevelNames levels do
      Term.withoutErrToSorry do
        let proof ← `(by
          classical
          intro ι spec M PK SK S C _ policy sigAlg runtime adv
          rw [SignatureAlg.SigningView.ofTotal_countedUnforgeableAdvantage
            policy runtime sigAlg adv]
          rw [SignatureAlg.SigningView.ofTotal_countedStrongUnforgeableAdvantage
            policy runtime sigAlg
              (⟨adv.main⟩ : SignatureAlg.StrongUnforgeableAdversary sigAlg)]
          exact SignatureAlg.unforgeableAdvantage_le_strongUnforgeableAdvantage runtime adv)
        let result ← Term.elabTermEnsuringType proof (some type)
        Term.synthesizeSyntheticMVarsNoPostponing
        instantiateMVars result
  if value.hasLooseBVars || value.hasFVar || value.hasMVar || value.hasLevelMVar ||
      value.hasSorry then
    throwError "Generic counted proof is not closed"
  if (← MonadLog.hasErrors) then throwError "Generic counted proof elaboration recorded errors"
  liftCoreM <| withExporting do
    addAndCompile (.thmDecl {
      name := name
      levelParams := levels
      type := type
      value := value
    })
  addDocStringCore name
    "Message-fresh success is bounded by pair-fresh success for one counted experiment."
  let .thmInfo actual ← getConstInfo name | throwError "Expected checked generic counted theorem"
  unless (← ofExcept (encodeExpr actual.type)) == (← ofExcept (encodeExpr type)) &&
      actual.levelParams == levels do
    throwError "Actual generic counted full type or raw universes changed"
  logInfo "GENERIC_COUNTED_DOMINATION_WITNESS_CREATED_NATIVE_EXIT_REQUIRED"
