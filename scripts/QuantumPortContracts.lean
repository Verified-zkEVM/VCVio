/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import Lean

/-!
# Compiled quantum-port contracts

Read-only inspection of kernel-level types, binder kinds and exposed definition bodies.
Run through Lake's environment on each pinned toolchain. The JSON retains kernel terms,
stripping only kernel-irrelevant `mdata` source metadata. No renaming, binder erasure or
instance synthesis is performed by the inspector. An optional compatibility check asks the
kernel to accept the current constant at its recorded old type; its result does not replace
the strict raw-term and definition-body comparison.
-/

open Lean

namespace SignatureManifest

structure Config where
  roots : Array Name := #[]
  modules : Array Name := #[]
  declarations : Array Name := #[]
  checkAgainst : Option String := none

def parseArgs : List String → Config → Except String Config
  | [], cfg => .ok cfg
  | "--root" :: name :: rest, cfg => parseArgs rest {cfg with roots := cfg.roots.push name.toName}
  | "--module" :: name :: rest, cfg =>
    parseArgs rest {cfg with modules := cfg.modules.push name.toName}
  | "--decl" :: name :: rest, cfg =>
    parseArgs rest {cfg with declarations := cfg.declarations.push name.toName}
  | "--check-against" :: path :: rest, cfg => parseArgs rest {cfg with checkAgainst := some path}
  | _, _ => .error "expected --root MODULE, --module MODULE or --decl DECLARATION"

partial def levelJson : Level → Json
  | .zero => Json.arr #[toJson "zero"]
  | .succ l => Json.arr #[toJson "succ", levelJson l]
  | .max a b => Json.arr #[toJson "max", levelJson a, levelJson b]
  | .imax a b => Json.arr #[toJson "imax", levelJson a, levelJson b]
  | .param n => Json.arr #[toJson "param", toJson n.toString]
  | .mvar n => Json.arr #[toJson "mvar", toJson n.name.toString]

def binderJson (b : BinderInfo) : Json := toJson (reprStr b)

partial def exprJson : Expr → Json
  | .bvar i => Json.arr #[toJson "bvar", toJson i]
  | .fvar i => Json.arr #[toJson "fvar", toJson i.name.toString]
  | .mvar i => Json.arr #[toJson "mvar", toJson i.name.toString]
  | .sort l => Json.arr #[toJson "sort", levelJson l]
  | .const n ls => Json.arr #[toJson "const", toJson n.toString, toJson (ls.map levelJson)]
  | .app f a => Json.arr #[toJson "app", exprJson f, exprJson a]
  | .lam n t b bi => Json.arr #[toJson "lam", toJson n.toString, binderJson bi,
      exprJson t, exprJson b]
  | .forallE n t b bi => Json.arr #[toJson "forall", toJson n.toString, binderJson bi,
      exprJson t, exprJson b]
  | .letE n t v b nondep => Json.arr #[toJson "let", toJson n.toString, toJson nondep,
      exprJson t, exprJson v, exprJson b]
  | .lit (.natVal n) => Json.arr #[toJson "nat", toJson n]
  | .lit (.strVal s) => Json.arr #[toJson "str", toJson s]
  | .mdata _ e => exprJson e
  | .proj n i e => Json.arr #[toJson "proj", toJson n.toString, toJson i, exprJson e]

def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def definitionValue? : ConstantInfo → Option Expr
  | .defnInfo d => some d.value
  | .opaqueInfo d => some d.value
  | _ => none

partial def binders (e : Expr) (i : Nat := 0) : Array Json :=
  match e with
  | .forallE n t b bi =>
    #[Json.mkObj [("index", toJson i), ("name", toJson n.toString),
      ("binderInfo", binderJson bi), ("domain", exprJson t),
      ("default", (t.getOptParamDefault?.map exprJson).getD Json.null),
      ("autoParamTactic", (t.getAutoParamTactic?.map exprJson).getD Json.null)]] ++ binders b (i+1)
  | .letE n t v b _ =>
    #[Json.mkObj [("index", toJson i), ("name", toJson n.toString),
      ("binderInfo", toJson "let"), ("domain", exprJson t), ("value", exprJson v)]] ++
        binders b (i+1)
  | .mdata _ e => binders e i
  | _ => #[]

def selectedModules : Array Name := #[
  `VCVio.Quantum.Oracle.ParallelSearch,
  `VCVio.Quantum.Oracle.ParallelPreimage,
  `VCVio.Quantum.Oracle.ParallelPlantedPreimage,
  `VCVio.Quantum.Oracle.ParallelSecurity,
  `VCVio.Schemes.MaskedChainPuzzle,
  `VCVio.Schemes.MaskedChainPuzzle.Preprocessing,
  `VCVio.Schemes.PointerChainPuzzle.QuantumCoupling.RankBounds,
  `VCVio.Schemes.PointerChainPuzzle.QuantumCoupling.Preprocessing]

def semanticModules : Array Name := #[
  `VCVio.Quantum.Comp.RoundBound, `VCVio.Quantum.Comp.TotalQueryBound,
  `VCVio.CryptoFoundations.TimeLockPuzzle.Quantum,
  `VCVio.Quantum.Oracle.MaskedChain.Model,
  `VCVio.Quantum.Oracle.MaskedChain.Preprocessing.Model,
  `VCVio.Quantum.Oracle.MaskedChain.Bounds,
  `VCVio.Quantum.Oracle.MaskedChain.Preprocessing,
  `VCVio.Quantum.Oracle.MaskedChain.RootBounds,
  `VCVio.Quantum.Oracle.Parallel,
  `VCVio.Schemes.PointerChainPuzzle.QuantumEncoding,
  `VCVio.Schemes.PointerChainPuzzle.QuantumCoupling.Scheme,
  `VCVio.Schemes.PointerChainPuzzle.QuantumCoupling.Programming,
  `VCVio.Schemes.PointerChainPuzzle.QuantumCoupling.Incidence,
  `VCVio.Schemes.PointerChainPuzzle.QuantumCoupling.RankHybrid,
  `VCVio.Schemes.PointerChainPuzzle.QuantumCoupling.RankSchedule,
  `VCVio.Schemes.PointerChainPuzzle.QuantumCoupling.PreprocessingIncidence]

def semanticExtra : Array Name := #[
  `Quantum.qromBatchSpec, `Quantum.parallelOracleRuntime, `Quantum.parallelOracleUnitary,
  `Quantum.QuantumRuntime.run, `Quantum.QuantumRuntime.evalDistMap,
  `Quantum.QuantumRuntime.evalDist, `Quantum.sampledEvalDistMap,
  `Quantum.SubState, `Quantum.SubState.mk, `Quantum.PlantedPreimageAdversary,
  `Quantum.QuantumComp, `Quantum.QuantumComp.toIPFunctor, `Quantum.LocalSig.Interp,
  `Quantum.QuantumRuntime.runAux, `Quantum.QuantumRuntime.jointPost,
  `ProbabilityTheory.plantedTargetDensity,
  `PointerChainPuzzle.keyRound,
  `PointerChainPuzzle.hitBound,
  `PointerChainPuzzle.LeanSeal.evalDist_quantumWindowScheme_solve,
  `PointerChainPuzzle.LeanSeal.uniformOn_pathInputCollision_le,
  `PointerChainPuzzle.LeanSeal.lintegral_uniform_programPath,
  `PointerChainPuzzle.LeanSeal.masked_le_programmed_add_collision,
  `PointerChainPuzzle.LeanSeal.real_le_programmed_add_collision,
  `PointerChainPuzzle.LeanSeal.delayAdvantage_quantumWindowScheme_eq_lintegral,
  `PointerChainPuzzle.LeanSeal.qromDelayAdvantage_quantumWindowScheme_eq_lintegral,
  `PointerChainPuzzle.LeanSeal.uniformOn_mem_futureRawPathInputs_resample_le]

def priorityHeadlines : Array Name := #[
  `Quantum.markedSearchAdvantage_le,
  `Quantum.markedSearchAdvantage_le_of_isPointBound,
  `Quantum.preimageSearchAdvantage_le,
  `Quantum.preimageSearchAdvantage_le_of_isPointBound,
  `Quantum.plantedPreimageAdvantage_le,
  `Quantum.plantedPreimageAdvantage_le_of_isPointBound,
  `Quantum.ParallelQROMBits,
  `Quantum.parallelQROMBits_markedSearch,
  `Quantum.parallelQROMBits_preimageSearch,
  `Quantum.parallelQROMBits_plantedPreimage,
  `MaskedChainPuzzle.qromDelayAdvantage_le,
  `MaskedChainPuzzle.qromDelayAdvantage_le_root,
  `MaskedChainPuzzle.qromDelayAdvantage_le_of_preprocessing,
  `MaskedChainPuzzle.qromDelayAdvantage_le_of_preprocessing_min,
  `MaskedChainPuzzle.qromDelayAdvantage_le_of_preprocessing_points,
  `MaskedChainPuzzle.qromDelayAdvantage_le_of_preprocessing_root,
  `MaskedChainPuzzle.qromDelaySecure,
  `MaskedChainPuzzle.qromDelaySecure_points,
  `MaskedChainPuzzle.qromDelaySecure_root,
  `PointerChainPuzzle.LeanSeal.sqrt_sum_rankHybridSuccess_resample_le,
  `PointerChainPuzzle.LeanSeal.sqrt_averageRankHybridSuccess_le_succ,
  `PointerChainPuzzle.LeanSeal.sqrt_averageRankHybridSuccess_zero_le,
  `PointerChainPuzzle.LeanSeal.averageRankHybridSuccess_zero_le,
  `PointerChainPuzzle.LeanSeal.averageRankHybridSuccess_zero_le_mul_mass,
  `PointerChainPuzzle.LeanSeal.rankHybridSuccess_zero,
  `PointerChainPuzzle.LeanSeal.sum_programmedRecovery_le_mul_mass,
  `PointerChainPuzzle.LeanSeal.qromDelayAdvantage_quantumWindowScheme_le_of_preprocessing,
  `PointerChainPuzzle.LeanSeal.qromDelaySecure_quantumWindowScheme]

def isPublicName (n : Name) : Bool := !n.toString.startsWith "_private." &&
  (n.toString.splitOn "._proof_").length == 1 && (n.toString.splitOn "._aux_").length == 1

def declarationJson (name moduleName : Name) (headline : Bool) : CoreM Json := do
  let env ← getEnv
  let some ci := env.find? name | throwError "missing declaration {name}"
  let opts := (← getOptions).setBool `pp.explicit true |>.setBool `pp.universes true
    |>.setBool `pp.fullNames true |>.setBool `pp.proofs true |>.set `pp.width (120 : Nat)
  let pretty ← withOptions (fun _ => opts) <| Meta.MetaM.run' do
    pure (← Meta.ppExpr ci.type).pretty
  let value := definitionValue? ci
  let valuePretty ← match value with
    | none => pure Json.null
    | some e => withOptions (fun _ => opts) <| Meta.MetaM.run' do
      pure (toJson (toString e))
  let bodyNames := value.map fun e => e.getUsedConstantsAsSet.toList.map Name.toString
  pure <| Json.mkObj [
    ("name", toJson name.toString), ("module", toJson moduleName.toString),
    ("headlineModule", toJson headline), ("kind", toJson (kind ci)),
    ("levelParameters", toJson (ci.levelParams.map Name.toString)),
    ("type", exprJson ci.type), ("typePretty", toJson pretty),
    ("binders", toJson (binders ci.type)),
    ("typeConstants", toJson (ci.type.getUsedConstantsAsSet.toList.map Name.toString)),
    ("reducibility", toJson (reprStr (getReducibilityStatusCore env name))),
    ("value", (value.map exprJson).getD Json.null),
    ("valuePretty", valuePretty), ("valueConstants", toJson bodyNames)]

def snapshot (cfg : Config) : CoreM Json := do
  let env ← getEnv
  let mut found : Array (Name × Name × Bool) := #[]
  let mut seen : Std.HashSet Name := {}
  for (m, data) in env.header.moduleNames.zip env.header.moduleData do
    let headline :=
      if cfg.modules.isEmpty then selectedModules.contains m else cfg.modules.contains m
    let semantic := cfg.modules.isEmpty && cfg.declarations.isEmpty && semanticModules.contains m
    if headline || semantic then
      for n in data.constNames do
        let chosenPrivate := n.toString.endsWith ".programmedSample_eq_lintegral"
        if (isPublicName n || chosenPrivate) && !seen.contains n && cfg.declarations.isEmpty then
          let some ci := env.find? n | continue
          if headline || (kind ci != "theorem" && kind ci != "recursor") then
            found := found.push (n, m, headline)
            seen := seen.insert n
  for n in cfg.declarations do
    if !seen.contains n then
      unless (env.find? n).isSome do throwError "requested declaration {n} was not imported"
      let moduleName := (env.getModuleIdxFor? n).map (env.header.moduleNames[·]!)
      found := found.push (n, moduleName.getD .anonymous, true)
      seen := seen.insert n
  for m in cfg.modules do
    unless env.header.moduleNames.contains m do throwError "requested module {m} was not imported"
  for n in (if cfg.declarations.isEmpty && cfg.modules.isEmpty then semanticExtra else #[]) do
    unless (env.find? n).isSome do throwError "semantic contract {n} was not imported"
    if !seen.contains n then
      let moduleName := (env.getModuleIdxFor? n).map (env.header.moduleNames[·]!)
      found := found.push (n, moduleName.getD .anonymous, false)
      seen := seen.insert n
  if cfg.modules.isEmpty && cfg.declarations.isEmpty then
    for n in priorityHeadlines do
      unless (env.find? n).isSome do throwError "priority headline {n} was not imported"
  let sorted := found.qsort fun a b => a.1.toString < b.1.toString
  if sorted.isEmpty then throwError "requested scope has no public contract declarations"
  let entries ← sorted.mapM fun (n,m,h) => declarationJson n m h
  pure <| Json.mkObj [
    ("format", toJson "qrom-port-signatures-v1"),
    ("leanVersion", toJson Lean.versionString),
    ("importRoots", toJson (cfg.roots.map Name.toString)),
    ("requestedModules", toJson (cfg.modules.map Name.toString)),
    ("requestedDeclarations", toJson (cfg.declarations.map Name.toString)),
    ("selectedModules", toJson (selectedModules.map Name.toString)),
    ("semanticModules", toJson (semanticModules.map Name.toString)),
    ("priorityHeadlines", toJson (priorityHeadlines.map Name.toString)),
    ("declarations", toJson entries)]

partial def readLevel (j : Json) : Except String Level := do
  let a ← j.getArr?
  match ← a[0]!.getStr? with
  | "zero" => pure .zero
  | "succ" => return .succ (← readLevel a[1]!)
  | "max" => return .max (← readLevel a[1]!) (← readLevel a[2]!)
  | "imax" => return .imax (← readLevel a[1]!) (← readLevel a[2]!)
  | "param" => return .param (← a[1]!.getStr?).toName
  | _ => throw "unexpected universe node in compiled contract"

def readBinder (j : Json) : Except String BinderInfo := do
  match ← j.getStr? with
  | "Lean.BinderInfo.default" => pure .default
  | "Lean.BinderInfo.implicit" => pure .implicit
  | "Lean.BinderInfo.strictImplicit" => pure .strictImplicit
  | "Lean.BinderInfo.instImplicit" => pure .instImplicit
  | s => throw s!"unexpected binder kind {s}"

partial def readExpr (j : Json) : Except String Expr := do
  let a ← j.getArr?
  match ← a[0]!.getStr? with
  | "bvar" => return .bvar (← a[1]!.getNat?)
  | "sort" => return .sort (← readLevel a[1]!)
  | "const" =>
    let name ← a[1]!.getStr?
    let levels ← (← a[2]!.getArr?).toList.mapM readLevel
    return .const name.toName levels
  | "app" => return .app (← readExpr a[1]!) (← readExpr a[2]!)
  | "forall" =>
    let name ← a[1]!.getStr?
    let domain ← readExpr a[3]!
    let body ← readExpr a[4]!
    return .forallE name.toName domain body (← readBinder a[2]!)
  | "lam" =>
    let name ← a[1]!.getStr?
    let domain ← readExpr a[3]!
    let body ← readExpr a[4]!
    return .lam name.toName domain body (← readBinder a[2]!)
  | "let" =>
    let name ← a[1]!.getStr?
    let domain ← readExpr a[3]!
    let value ← readExpr a[4]!
    let body ← readExpr a[5]!
    return .letE name.toName domain value body (← a[2]!.getBool?)
  | "nat" => return .lit (.natVal (← a[1]!.getNat?))
  | "str" => return .lit (.strVal (← a[1]!.getStr?))
  | "proj" =>
    let name ← a[1]!.getStr?
    return .proj name.toName (← a[2]!.getNat?) (← readExpr a[3]!)
  | _ => throw "unexpected expression node in closed compiled contract"

/-- Ask the kernel to check the current constant at the old recorded type. This is deliberately
separate from raw comparison, because kernel conversion ignores binder annotations. -/
def compatibilityCheck (cfg : Config) (path : String) : CoreM Json := do
  let content ← IO.FS.readFile path
  let .ok old := Json.parse content | throwError "cannot parse old contract JSON"
  let .ok entries := old.getObjValAs? (Array Json) "declarations" |
    throwError "old contract has no declarations"
  let mut oldNames : Std.HashSet Name := {}
  let mut oldModules : Std.HashSet Name := {}
  for entry in entries do
    let .ok name := entry.getObjValAs? String "name" | throwError "missing old name"
    let .ok moduleName := entry.getObjValAs? String "module" | throwError "missing old module"
    oldNames := oldNames.insert name.toName
    oldModules := oldModules.insert moduleName.toName
  for name in cfg.declarations do
    unless oldNames.contains name do throwError "requested declaration {name} has no old contract"
  for name in cfg.modules do
    unless oldModules.contains name do throwError "requested module {name} has no old contracts"
  let mut results := #[]
  for entry in entries do
    let .ok nameString := entry.getObjValAs? String "name" | throwError "missing old name"
    let name := nameString.toName
    let .ok modString := entry.getObjValAs? String "module" | throwError "missing old module"
    if !cfg.declarations.isEmpty && !cfg.declarations.contains name then continue
    if !cfg.modules.isEmpty && !cfg.modules.contains modString.toName then continue
    try
      let .ok typeJson := entry.getObjVal? "type" | throwError "missing old type"
      let .ok type := readExpr typeJson | throwError "invalid old type expression"
      let .ok levels := entry.getObjValAs? (Array String) "levelParameters" |
        throwError "missing old universe parameters"
      let env ← getEnv
      let some _ := env.find? name | throwError "current declaration {name} is missing"
      let levelNames := levels.toList.map String.toName
      let adapter := Name.str `QuantumPortContractCompatibility nameString
      let decl := Declaration.defnDecl {
        name := adapter, levelParams := levelNames, type := type,
        value := .const name (levelNames.map Level.param),
        hints := .abbrev, safety := .safe }
      withOptions (fun opts => opts.setBool `debug.skipKernelTC false) <| addDecl decl
      results := results.push <| Json.mkObj [
        ("name", toJson nameString), ("kernelAccepted", toJson true)]
    catch error =>
      results := results.push <| Json.mkObj [("name", toJson nameString),
        ("kernelAccepted", toJson false), ("error", toJson (← error.toMessageData.toString))]
  if results.isEmpty then throwError "old compatibility scope is empty"
  pure <| Json.mkObj [("oldManifest", toJson path), ("declarations", toJson results)]

end SignatureManifest

unsafe def main (args : List String) : IO UInt32 := do
  let out :: rest := args |
    IO.eprintln ("usage: lake env lean --run QuantumPortContracts.lean OUTPUT.json " ++
      "[--root MODULE]* [--module MODULE]* [--decl NAME]* [--check-against OLD.json]")
    return 2
  let .ok cfg := SignatureManifest.parseArgs rest {} |
    IO.eprintln "invalid quantum-port-contract options"; return 2
  if !cfg.modules.isEmpty && !cfg.declarations.isEmpty then
    IO.eprintln "choose module scope or declaration scope, not both"
    return 2
  let cfg := if cfg.roots.isEmpty then {cfg with roots := #[`VCVio]} else cfg
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (cfg.roots.map fun root => {module := root}) {}
    (trustLevel := 1024) (loadExts := true)
  let (result, _) ← (SignatureManifest.snapshot cfg).toIO
    {fileName := "<qrom-port-signatures>", fileMap := default} {env}
  let compatibility ← match cfg.checkAgainst with
    | none => pure Json.null
    | some path =>
      let (check, _) ← (SignatureManifest.compatibilityCheck cfg path).toIO
        {fileName := "<qrom-port-compatibility>", fileMap := default} {env}
      pure check
  let result := result.setObjVal! "kernelCompatibility" compatibility
  IO.FS.writeFile out (result.pretty ++ "\n")
  IO.println s!"Wrote {out}"
  let rejected := match cfg.checkAgainst with
    | none => false
    | some _ => match compatibility.getObjValAs? (Array Json) "declarations" with
      | .error _ => true
      | .ok checks => checks.any fun check =>
        match check.getObjValAs? Bool "kernelAccepted" with
        | .ok accepted => !accepted
        | .error _ => true
  return if rejected then 1 else 0
