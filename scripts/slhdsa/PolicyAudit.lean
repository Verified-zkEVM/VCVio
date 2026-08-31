/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module
public import Lean.Compiler.ExternAttr
public meta import Lean.Compiler.ExternAttr
public import Lean.Compiler.ImplementedByAttr
public meta import Lean.Compiler.ImplementedByAttr
public import Lean.Compiler.InitAttr
public meta import Lean.Compiler.InitAttr
public import Lean.Compiler.Old
public meta import Lean.Compiler.Old
public import Lean.Data.Options
public meta import Lean.Data.Options
public import Lean.Elab.Command
public meta import Lean.Elab.Command
public import Lean.Elab.Tactic.Decide
public meta import Lean.Elab.Tactic.Decide
public import Lean.LabelAttribute
public meta import Lean.LabelAttribute
public import Lean.Util.CollectAxioms
public meta import Lean.Util.CollectAxioms

/-!
# Elaborated-environment policy audit for HashSig

This script audits the compiled environment rather than trying to recognize all Lean syntax.
The source-token checks in `check-harness.py` are a separate defense-in-depth layer.
-/

open Lean Elab Command

public section

namespace SLHDSAPolicyAudit

inductive FindingKind where
  | unexpectedAxiom
  | unsafeDecl
  | partialDecl
  | externAttr
  | initializerEntry
  | runtimeOverride
  | externModuleEntry
  | initializerModuleEntry
  | runtimeModuleEntry
deriving BEq, Repr

structure Finding where
  kind : FindingKind
  declName : Name
  detail : Name := .anonymous
  surface : String := ""
deriving BEq, Repr

structure AuditResult where
  findings : Array Finding := #[]
  axiomUnion : Array Name := #[]
  ownedCount : Nat := 0

def standardAxiomAllowlist : Array Name := #[
  ``propext,
  ``Classical.choice,
  ``Quot.sound
]

def s00Placeholder : Name := `SLHDSA.slhdsa_euf_cma_security

private def axiomAllowed (declName axiomName : Name) : Bool :=
  standardAxiomAllowlist.contains axiomName ||
    (declName == s00Placeholder && axiomName == ``sorryAx)

/-- Exact Lean 4.33.1 compiler helpers generated for the current recursive HashSig definitions. -/
def compilerHelperAllowlist : Array (Name × Name) := #[
  (`SLHDSA.base2bFill._unsafe_rec, `SLHDSA.base2bFill),
  (`SLHDSA.base2bGo._unsafe_rec, `SLHDSA.base2bGo),
  (`SLHDSA.WotsChecksum.digitsOfBaseW._unsafe_rec, `SLHDSA.WotsChecksum.digitsOfBaseW),
  (`SLHDSA.chainWith._unsafe_rec, `SLHDSA.chainWith),
  (`SLHDSA.C13.chain._unsafe_rec, `SLHDSA.C13.chain),
  (`SLHDSA.xmssAuthPathWith._unsafe_rec, `SLHDSA.xmssAuthPathWith),
  (`SLHDSA.forsAuthPathVector._unsafe_rec, `SLHDSA.forsAuthPathVector),
  (`SLHDSA.forsAuthPathVectorM._unsafe_rec, `SLHDSA.forsAuthPathVectorM),
  (`SLHDSA.LayerPosition.atWithLayer._unsafe_rec, `SLHDSA.LayerPosition.atWithLayer),
  (`SLHDSA.GeneralHypertree.signFromPosition._unsafe_rec,
    `SLHDSA.GeneralHypertree.signFromPosition),
  (`SLHDSA.GeneralHypertree.signFromPositionM._unsafe_rec,
    `SLHDSA.GeneralHypertree.signFromPositionM),
  (`SLHDSA.GeneralHypertree.signFromPositionWith._unsafe_rec,
    `SLHDSA.GeneralHypertree.signFromPositionWith),
  (`SLHDSA.GeneralHypertree.recoverFromPosition._unsafe_rec,
    `SLHDSA.GeneralHypertree.recoverFromPosition),
  (`SLHDSA.GeneralHypertree.recoverFromPositionM._unsafe_rec,
    `SLHDSA.GeneralHypertree.recoverFromPositionM),
  (`SLHDSA.GeneralHypertree.recoverFromPositionWith._unsafe_rec,
    `SLHDSA.GeneralHypertree.recoverFromPositionWith),
  (`SLHDSA.GeneralHypertree.signLoopQueryBound._unsafe_rec,
    `SLHDSA.GeneralHypertree.signLoopQueryBound),
  (`SLHDSA.Security.perfectInternalCoords._unsafe_rec,
    `SLHDSA.Security.perfectInternalCoords)
]

private def isAllowedCompilerHelper (declName : Name) : Bool :=
  compilerHelperAllowlist.any fun entry => entry.1 == declName

private def isHashSigModule (moduleName : Name) : Bool :=
  moduleName == `HashSig || moduleName.toString.startsWith "HashSig."

private def isHashSigDeclaration (env : Environment) (declName : Name) : Bool :=
  match env.getModuleIdxFor? declName with
  | none => false
  | some moduleIdx => isHashSigModule env.allImportedModuleNames[moduleIdx.toNat]!

private def addFinding (findings : Array Finding) (kind : FindingKind)
    (declName : Name) (detail : Name := .anonymous) : Array Finding :=
  findings.push { kind, declName, detail }

/-- Inspect declarations accepted by `owns` in the supplied static environment. -/
def collectAudit (env : Environment) (owns : Environment → Name → Bool) : CommandElabM AuditResult :=
  withEnv env do
    let mut findings := #[]
    let mut axiomUnion := #[]
    let mut ownedCount := 0
    for (declName, info) in env.constants do
      if !owns env declName then
        continue
      ownedCount := ownedCount + 1
      let axioms ← Lean.collectAxioms declName
      for axiomName in axioms do
        unless axiomUnion.contains axiomName do
          axiomUnion := axiomUnion.push axiomName
        unless axiomAllowed declName axiomName do
          findings := addFinding findings .unexpectedAxiom declName axiomName
      if info.isUnsafe then
        findings := addFinding findings .unsafeDecl declName
      if info.isPartial && !isAllowedCompilerHelper declName then
        findings := addFinding findings .partialDecl declName
      if Lean.isExtern env declName then
        findings := addFinding findings .externAttr declName
      if Lean.hasInitAttr env declName || Lean.isIOUnitInitFn env declName then
        findings := addFinding findings .initializerEntry declName
      if let some implementation := Lean.Compiler.getImplementedBy? env declName then
        findings := addFinding findings .runtimeOverride declName implementation
    return { findings, axiomUnion, ownedCount }

private def validateCompilerHelpers (env : Environment) : CommandElabM Unit := withEnv env do
  let mut observed := #[]
  for (declName, info) in env.constants do
    if isHashSigDeclaration env declName && info.isPartial then
      observed := observed.push declName
  unless observed.size == compilerHelperAllowlist.size &&
      observed.all (fun name => isAllowedCompilerHelper name) do
    throwError "HashSig partial constants differ from the exact compiler-helper allowlist: {observed}"
  for (helper, expectedParent) in compilerHelperAllowlist do
    unless Lean.Compiler.isUnsafeRecName? helper == some expectedParent do
      throwError "compiler helper {helper} does not map structurally to {expectedParent}"
    let some helperInfo := env.find? helper
      | throwError "missing allowlisted compiler helper {helper}"
    let some parentInfo := env.find? expectedParent
      | throwError "missing parent of compiler helper {helper}: {expectedParent}"
    unless helperInfo.isPartial && !helperInfo.isUnsafe do
      throwError "compiler helper {helper} is not partial-and-kernel-safe"
    unless !parentInfo.isPartial && !parentInfo.isUnsafe do
      throwError "compiler-helper parent {expectedParent} is partial or unsafe"
    unless env.getModuleIdxFor? helper == env.getModuleIdxFor? expectedParent &&
        isHashSigDeclaration env helper do
      throwError "compiler helper {helper} is not owned by its parent's HashSig module"
    unless !Lean.isExtern env helper && !Lean.hasInitAttr env helper &&
        !Lean.isIOUnitInitFn env helper &&
        (Lean.Compiler.getImplementedBy? env helper).isNone do
      throwError "compiler helper {helper} has an extern/init/runtime override"
    let axioms ← Lean.collectAxioms helper
    unless !axioms.contains helper && !axioms.contains ``sorryAx do
      throwError "compiler helper {helper} is an axiom or transitively uses sorryAx"
  logInfo m!"SLH-DSA compiler-helper allowlist: PASS \
    ({compilerHelperAllowlist.size} exact `_unsafe_rec` auxiliaries)"

private def addUniqueFinding (findings : Array Finding) (finding : Finding) : Array Finding :=
  if findings.contains finding then findings else findings.push finding

/-- Serialized names from each ordinary/IR persistent-extension surface for one module. -/
structure ModuleEntryArrays where
  regularInit : Array Name := #[]
  regularInitIR : Array Name := #[]
  builtinInit : Array Name := #[]
  builtinInitIR : Array Name := #[]
  extern : Array Name := #[]
  externIR : Array Name := #[]
  implementedBy : Array Name := #[]
  implementedByIR : Array Name := #[]

private def addModuleSurfaceFindings (findings : Array Finding) (moduleName : Name)
    (surface : String) (kind : FindingKind) (entries : Array Name) : Array Finding :=
  entries.foldl (init := findings) fun acc declName =>
    addUniqueFinding acc { kind, declName, detail := moduleName, surface }

/-- Pure production mapper shared by the imported-module audit and raw-state self-test. -/
def mapModuleEntryFindings (moduleName : Name) (entries : ModuleEntryArrays) : Array Finding :=
  let findings := addModuleSurfaceFindings #[] moduleName "regular-init/ordinary"
    .initializerModuleEntry entries.regularInit
  let findings := addModuleSurfaceFindings findings moduleName "regular-init/ir"
    .initializerModuleEntry entries.regularInitIR
  let findings := addModuleSurfaceFindings findings moduleName "builtin-init/ordinary"
    .initializerModuleEntry entries.builtinInit
  let findings := addModuleSurfaceFindings findings moduleName "builtin-init/ir"
    .initializerModuleEntry entries.builtinInitIR
  let findings := addModuleSurfaceFindings findings moduleName "extern/ordinary"
    .externModuleEntry entries.extern
  let findings := addModuleSurfaceFindings findings moduleName "extern/ir"
    .externModuleEntry entries.externIR
  let findings := addModuleSurfaceFindings findings moduleName "implemented-by/ordinary"
    .runtimeModuleEntry entries.implementedBy
  addModuleSurfaceFindings findings moduleName "implemented-by/ir"
    .runtimeModuleEntry entries.implementedByIR

def collectHashSigModuleEntryFindings (env : Environment) : Array Finding := Id.run do
  let mut findings := #[]
  for moduleIdx in [:env.allImportedModuleNames.size] do
    let moduleName := env.allImportedModuleNames[moduleIdx]!
    if !isHashSigModule moduleName then
      continue
    let moduleFindings := mapModuleEntryFindings moduleName {
      regularInit := (Lean.regularInitAttr.ext.getModuleEntries env moduleIdx).map (·.1)
      regularInitIR := (Lean.regularInitAttr.ext.getModuleIREntries env moduleIdx).map (·.1)
      builtinInit := (Lean.builtinInitAttr.ext.getModuleEntries env moduleIdx).map (·.1)
      builtinInitIR := (Lean.builtinInitAttr.ext.getModuleIREntries env moduleIdx).map (·.1)
      extern := (Lean.externAttr.ext.getModuleEntries env moduleIdx).map (·.1)
      externIR := (Lean.externAttr.ext.getModuleIREntries env moduleIdx).map (·.1)
      implementedBy :=
        (Lean.Compiler.implementedByAttr.ext.getModuleEntries env moduleIdx).map (·.1)
      implementedByIR :=
        (Lean.Compiler.implementedByAttr.ext.getModuleIREntries env moduleIdx).map (·.1)
    }
    findings := moduleFindings.foldl (init := findings) addUniqueFinding
  return findings

private def validateHashSigAxiomUnion (audit : AuditResult) : CommandElabM Unit := do
  let expected := standardAxiomAllowlist
  unless audit.axiomUnion.size == expected.size &&
      audit.axiomUnion.all expected.contains do
    throwError "HashSig transitive axiom union changed: {audit.axiomUnion}"
  logInfo m!"SLH-DSA HashSig inventory: {audit.ownedCount} owned constants; transitive axiom union exactly [propext, Classical.choice, Quot.sound]"

private def findingLess (left right : Finding) : Bool :=
  if left.declName == right.declName then
    toString (repr left.kind) < toString (repr right.kind)
  else
    Name.quickLt left.declName right.declName

private def renderFinding (finding : Finding) : MessageData :=
  let suffix := if finding.detail.isAnonymous then m!"" else m!" ({finding.detail})"
  let surface := if finding.surface.isEmpty then m!"" else m!" [{finding.surface}]"
  m!"{repr finding.kind}: {finding.declName}{suffix}{surface}"

private def failOnFindings (label : String) (findings : Array Finding) : CommandElabM Unit := do
  unless findings.isEmpty do
    let findings := findings.qsort findingLess
    for finding in findings do
      logError <| renderFinding finding
    throwError "{label}: {findings.size} prohibited elaborated-environment entries"

/-- Meta-import a compiled target while keeping extension initialization and initializers disabled. -/
def importStaticTargetEnvironment (target : Name) : CommandElabM Environment := do
  let enabledBefore ← liftIO Lean.isInitializerExecutionEnabled
  unless !enabledBefore do
    throwError "initializer execution was enabled before static import of {target}"
  let opts ← getOptions
  let env ← liftIO <| Lean.importModules
    #[{ module := target, isMeta := true }] opts (loadExts := false)
  let enabledAfter ← liftIO Lean.isInitializerExecutionEnabled
  unless !enabledAfter do
    throwError "initializer execution became enabled during static import of {target}"
  let hashSigModuleCount := env.allImportedModuleNames.countP isHashSigModule
  logInfo m!"SLH-DSA static meta import: {target}; loadExts=false; initializer execution false→false; {hashSigModuleCount} HashSig modules"
  return env

/-! ## Compiled negative fixtures

These declarations live only in this script module. They reproduce admission/runtime classes that
evaded earlier token scans; the self-test below requires the semantic audit to find each class.
-/

namespace Fixtures

axiom explicitAxiom : False

theorem directSorry : True := by
  sorry

theorem rootQualifiedSorryAx : False :=
  _root_.sorryAx False true

private def messageInterpolation := m!"{(by sorry : String)}"

private def separatedInterpolation := m! /- gap -/ "{(by sorry : String)}"

def importedInterpolation : IO Unit := do
  println! "{(by sorry : String)}"

def unprefixedInterpolation : Nat :=
  dbg_trace "{(by sorry : Nat)}"; 0

unsafe def unsafeDefinition : Nat := 0

partial def partialDefinition (_ : Unit) : Nat :=
  partialDefinition ()

@[extern "slhdsa_policy_fixture_extern"]
opaque externDefinition : Nat

def initDefinition : IO Unit := pure ()
attribute [init] initDefinition

def builtinInitDefinition : IO Unit := pure ()
attribute [builtin_init] builtinInitDefinition

register_option slhdsaPolicyFixtureOption : Bool := {
  defValue := false
}

register_builtin_option slhdsaPolicyFixtureBuiltinOption : Bool := {
  defValue := false
}

register_label_attr slhdsa_policy_fixture_label

def runtimeImplementation : Nat := 1
@[implemented_by runtimeImplementation]
def logicalDefinition : Nat := 0

inductive ComputedFixture where
  | zero
  | value (n : Nat)
with
  @[computed_field] computedValue : ComputedFixture → Nat
    | .zero => 0
    | .value n => n

theorem nativeDecideAxiom : (1 : Nat) = 1 := by
  native_decide

run_cmd liftCoreM <| Lean.addDecl (.axiomDecl {
  name := `SLHDSAPolicyAudit.Fixtures.injectedAxiom
  levelParams := []
  type := mkConst ``False
  isUnsafe := false
})

end Fixtures

namespace ExternalDependencyFixture

axiom externalAxiom : False

theorem ownedTheorem : False := externalAxiom

end ExternalDependencyFixture

private def rawRegularTarget := `SLHDSAPolicyAudit.RawEntryFixture.regularTarget
private def rawBuiltinTarget := `SLHDSAPolicyAudit.RawEntryFixture.builtinTarget
private def rawExternTarget := `SLHDSAPolicyAudit.RawEntryFixture.externTarget
private def rawImplementedByTarget := `SLHDSAPolicyAudit.RawEntryFixture.implementedByTarget

private def ownsHistoricalFixture (env : Environment) (declName : Name) : Bool :=
  (env.getModuleIdxFor? declName).isNone &&
    declName.toString.contains "SLHDSAPolicyAudit.Fixtures."

private def ownsExternalDependencyTheorem (env : Environment) (declName : Name) : Bool :=
  (env.getModuleIdxFor? declName).isNone &&
    declName == ``ExternalDependencyFixture.ownedTheorem

inductive PatternMode where
  | exact
  | suffix
  | contains

structure NamePattern where
  mode : PatternMode
  text : String

private def NamePattern.matches (pattern : NamePattern) (name : Name) : Bool :=
  match pattern.mode with
  | .exact => name.toString == pattern.text
  | .suffix => name.toString.endsWith pattern.text
  | .contains => name.toString.contains pattern.text

structure ExpectedFinding where
  kind : FindingKind
  decl : NamePattern
  detail : Option NamePattern := none
  surface : String := ""

private def ExpectedFinding.matches (expected : ExpectedFinding) (actual : Finding) : Bool :=
  expected.kind == actual.kind && expected.decl.matches actual.declName &&
    expected.surface == actual.surface &&
    match expected.detail with
    | none => actual.detail.isAnonymous
    | some pattern => pattern.matches actual.detail

private def exactPattern (text : String) : NamePattern := { mode := .exact, text }
private def suffixPattern (text : String) : NamePattern := { mode := .suffix, text }
private def containsPattern (text : String) : NamePattern := { mode := .contains, text }

private def exactExpected (kind : FindingKind) (decl : String)
    (detail : Option String := none) : ExpectedFinding := {
  kind
  decl := exactPattern decl
  detail := detail.map exactPattern
}

private def fixtureExpected : Array ExpectedFinding := #[
  exactExpected .unexpectedAxiom "SLHDSAPolicyAudit.Fixtures.explicitAxiom"
    (some "SLHDSAPolicyAudit.Fixtures.explicitAxiom"),
  exactExpected .unexpectedAxiom "SLHDSAPolicyAudit.Fixtures.injectedAxiom"
    (some "SLHDSAPolicyAudit.Fixtures.injectedAxiom"),
  { kind := .unexpectedAxiom,
    decl := suffixPattern "SLHDSAPolicyAudit.Fixtures.nativeDecideAxiom._native.native_decide.ax_1_1",
    detail := some <| suffixPattern
      "SLHDSAPolicyAudit.Fixtures.nativeDecideAxiom._native.native_decide.ax_1_1" },
  { kind := .unexpectedAxiom,
    decl := exactPattern "SLHDSAPolicyAudit.Fixtures.nativeDecideAxiom",
    detail := some <| suffixPattern
      "SLHDSAPolicyAudit.Fixtures.nativeDecideAxiom._native.native_decide.ax_1_1" },
  exactExpected .unexpectedAxiom "SLHDSAPolicyAudit.Fixtures.directSorry" (some "sorryAx"),
  exactExpected .unexpectedAxiom "SLHDSAPolicyAudit.Fixtures.rootQualifiedSorryAx"
    (some "sorryAx"),
  { kind := .unexpectedAxiom,
    decl := suffixPattern "SLHDSAPolicyAudit.Fixtures.messageInterpolation",
    detail := some <| exactPattern "sorryAx" },
  { kind := .unexpectedAxiom,
    decl := suffixPattern "SLHDSAPolicyAudit.Fixtures.separatedInterpolation",
    detail := some <| exactPattern "sorryAx" },
  exactExpected .unexpectedAxiom "SLHDSAPolicyAudit.Fixtures.importedInterpolation"
    (some "sorryAx"),
  exactExpected .unexpectedAxiom "SLHDSAPolicyAudit.Fixtures.unprefixedInterpolation"
    (some "sorryAx"),
  exactExpected .unsafeDecl "SLHDSAPolicyAudit.Fixtures.unsafeDefinition",
  exactExpected .unsafeDecl "SLHDSAPolicyAudit.Fixtures.ComputedFixture.zero._override",
  exactExpected .unsafeDecl "SLHDSAPolicyAudit.Fixtures.ComputedFixture.value._override",
  exactExpected .unsafeDecl "SLHDSAPolicyAudit.Fixtures.ComputedFixture.casesOn._override",
  exactExpected .unsafeDecl "SLHDSAPolicyAudit.Fixtures.ComputedFixture.computedValue._override",
  exactExpected .unexpectedAxiom "SLHDSAPolicyAudit.Fixtures.ComputedFixture.zero._override"
    (some "lcProof"),
  exactExpected .unexpectedAxiom "SLHDSAPolicyAudit.Fixtures.ComputedFixture.value._override"
    (some "lcProof"),
  exactExpected .unexpectedAxiom "SLHDSAPolicyAudit.Fixtures.ComputedFixture.casesOn._override"
    (some "lcProof"),
  exactExpected .unexpectedAxiom
    "SLHDSAPolicyAudit.Fixtures.ComputedFixture.computedValue._override" (some "lcProof"),
  exactExpected .partialDecl "SLHDSAPolicyAudit.Fixtures.partialDefinition._unsafe_rec",
  exactExpected .externAttr "SLHDSAPolicyAudit.Fixtures.externDefinition",
  exactExpected .initializerEntry "SLHDSAPolicyAudit.Fixtures.initDefinition",
  exactExpected .initializerEntry "SLHDSAPolicyAudit.Fixtures.builtinInitDefinition",
  exactExpected .initializerEntry "SLHDSAPolicyAudit.Fixtures.slhdsaPolicyFixtureOption",
  exactExpected .initializerEntry "SLHDSAPolicyAudit.Fixtures.slhdsaPolicyFixtureBuiltinOption",
  { kind := .initializerEntry,
    decl := containsPattern "SLHDSAPolicyAudit.Fixtures.ext._@.scripts.slhdsa.PolicyAudit.",
    detail := none },
  exactExpected .runtimeOverride "SLHDSAPolicyAudit.Fixtures.logicalDefinition"
    (some "SLHDSAPolicyAudit.Fixtures.runtimeImplementation"),
  exactExpected .runtimeOverride "SLHDSAPolicyAudit.Fixtures.ComputedFixture.zero"
    (some "SLHDSAPolicyAudit.Fixtures.ComputedFixture.zero._override"),
  exactExpected .runtimeOverride "SLHDSAPolicyAudit.Fixtures.ComputedFixture.value"
    (some "SLHDSAPolicyAudit.Fixtures.ComputedFixture.value._override"),
  exactExpected .runtimeOverride "SLHDSAPolicyAudit.Fixtures.ComputedFixture.casesOn"
    (some "SLHDSAPolicyAudit.Fixtures.ComputedFixture.casesOn._override"),
  exactExpected .runtimeOverride "SLHDSAPolicyAudit.Fixtures.ComputedFixture.computedValue"
    (some "SLHDSAPolicyAudit.Fixtures.ComputedFixture.computedValue._override")
]

private def validateExactFindings (label : String) (actual : Array Finding)
    (expected : Array ExpectedFinding) : CommandElabM Unit := do
  for expectation in expected do
    let count := actual.countP expectation.matches
    unless count == 1 do
      throwError "{label}: expected exactly one match for {repr expectation.kind} / {expectation.decl.text}, got {count}"
  for finding in actual do
    let count := expected.countP fun expectation => expectation.matches finding
    unless count == 1 do
      throwError "{label}: actual finding must match exactly one expectation, got {count}: {renderFinding finding}"
  unless actual.size == expected.size do
    for finding in actual.qsort findingLess do
      logError <| renderFinding finding
    throwError "{label}: expected {expected.size} total findings, got {actual.size}"

private def rawEntryNames {α} (entries : Array (Name × α)) : Array Name :=
  entries.filterMap fun entry =>
    if entry.1.toString.startsWith "SLHDSAPolicyAudit.RawEntryFixture." then
      some entry.1
    else
      none

private def collectRawCurrentEntryFixture : CommandElabM (Array Finding) := do
  let env ← getEnv
  let env := Lean.regularInitAttr.ext.addEntry env (rawRegularTarget, Name.anonymous)
  let env := Lean.builtinInitAttr.ext.addEntry env (rawBuiltinTarget, Name.anonymous)
  let env := Lean.externAttr.ext.addEntry env
    (rawExternTarget, { entries := [Lean.ExternEntry.adhoc `all] })
  let env := Lean.Compiler.implementedByAttr.ext.addEntry env
    (rawImplementedByTarget, `Nat.succ)
  let regularInit := rawEntryNames <|
    (Lean.regularInitAttr.ext.exportEntriesFn env
      (Lean.regularInitAttr.ext.getState env)).«private»
  let builtinInit := rawEntryNames <|
    (Lean.builtinInitAttr.ext.exportEntriesFn env
      (Lean.builtinInitAttr.ext.getState env)).«private»
  let extern := rawEntryNames <|
    (Lean.externAttr.ext.exportEntriesFn env
      (Lean.externAttr.ext.getState env)).«private»
  let implementedBy := rawEntryNames <|
    (Lean.Compiler.implementedByAttr.ext.exportEntriesFn env
      (Lean.Compiler.implementedByAttr.ext.getState env)).«private»
  return mapModuleEntryFindings env.mainModule {
    regularInit
    builtinInit
    extern
    implementedBy
  }

/-- Validate a compiled regular initializer, including its IR entry, on the production path. -/
def validateStaticInitializerFixture (target declName : Name) : CommandElabM Unit := do
  let some sentinelText ← liftIO <| IO.getEnv "SLHDSA_POLICY_SENTINEL"
    | throwError "SLHDSA_POLICY_SENTINEL is unset in compiled fixture mode"
  let sentinel : System.FilePath := ⟨sentinelText⟩
  if ← sentinel.pathExists then
    throwError "compiled fixture sentinel already exists before static import: {sentinel}"
  let env ← importStaticTargetEnvironment target
  if ← sentinel.pathExists then
    throwError "compiled fixture initializer executed during static import: {sentinel}"
  for moduleIdx in [:env.allImportedModuleNames.size] do
    if env.allImportedModuleNames[moduleIdx]! == target then
      let ordinary := Lean.regularInitAttr.ext.getModuleEntries env moduleIdx
      let ir := Lean.regularInitAttr.ext.getModuleIREntries env moduleIdx
      logInfo m!"SLH-DSA compiled fixture entries: regular/ordinary={ordinary}; regular/ir={ir}"
  let actual := collectHashSigModuleEntryFindings env
  let expected : Array ExpectedFinding := #[
    { kind := .initializerModuleEntry
      decl := exactPattern declName.toString
      detail := some <| exactPattern target.toString
      surface := "regular-init/ordinary" },
    { kind := .initializerModuleEntry
      decl := exactPattern declName.toString
      detail := some <| exactPattern target.toString
      surface := "regular-init/ir" }
  ]
  validateExactFindings "compiled initializer fixture" actual expected
  logInfo m!"SLH-DSA compiled initializer fixture: REJECTED on exact ordinary and IR surfaces; configured sentinel remained absent ({sentinel})"

private def runPrimaryAudit : CommandElabM Unit := do
  let scriptEnv ← getEnv
  let fixtureAudit ← collectAudit scriptEnv ownsHistoricalFixture
  validateExactFindings "historical elaborated-policy fixtures" fixtureAudit.findings fixtureExpected
  logInfo m!"SLH-DSA historical elaborated-policy fixtures: PASS ({fixtureAudit.findings.size} exact findings)"

  let externalAudit ← collectAudit scriptEnv ownsExternalDependencyTheorem
  let externalExpected := #[exactExpected .unexpectedAxiom
    "SLHDSAPolicyAudit.ExternalDependencyFixture.ownedTheorem"
    (some "SLHDSAPolicyAudit.ExternalDependencyFixture.externalAxiom")]
  validateExactFindings "external-axiom owned-subset fixture" externalAudit.findings externalExpected
  logInfo "SLH-DSA external-axiom owned-subset fixture: PASS"

  let rawEntryFindings ← collectRawCurrentEntryFixture
  let rawExpected : Array ExpectedFinding := #[
    { kind := .initializerModuleEntry
      decl := exactPattern "SLHDSAPolicyAudit.RawEntryFixture.regularTarget"
      detail := some <| containsPattern "scripts.slhdsa.PolicyAudit"
      surface := "regular-init/ordinary" },
    { kind := .initializerModuleEntry
      decl := exactPattern "SLHDSAPolicyAudit.RawEntryFixture.builtinTarget"
      detail := some <| containsPattern "scripts.slhdsa.PolicyAudit"
      surface := "builtin-init/ordinary" },
    { kind := .externModuleEntry
      decl := exactPattern "SLHDSAPolicyAudit.RawEntryFixture.externTarget"
      detail := some <| containsPattern "scripts.slhdsa.PolicyAudit"
      surface := "extern/ordinary" },
    { kind := .runtimeModuleEntry
      decl := exactPattern "SLHDSAPolicyAudit.RawEntryFixture.implementedByTarget"
      detail := some <| containsPattern "scripts.slhdsa.PolicyAudit"
      surface := "implemented-by/ordinary" }
  ]
  validateExactFindings "raw extension-entry fixture" rawEntryFindings rawExpected
  logInfo "SLH-DSA raw extension-entry fixture: PASS (4 current-state surfaces via production mapper)"

  let hashSigEnv ← importStaticTargetEnvironment `HashSig
  validateCompilerHelpers hashSigEnv
  let hashSigAudit ← collectAudit hashSigEnv isHashSigDeclaration
  validateHashSigAxiomUnion hashSigAudit
  let moduleEntryFindings := collectHashSigModuleEntryFindings hashSigEnv
  failOnFindings "SLH-DSA HashSig elaborated policy"
    (hashSigAudit.findings ++ moduleEntryFindings)
  logInfo "SLH-DSA HashSig elaborated policy audit: PASS"

run_cmd do
  match (← liftIO <| IO.getEnv "SLHDSA_POLICY_RUN_IR_FIXTURE") with
  | none => runPrimaryAudit
  | some "1" =>
      validateStaticInitializerFixture
        `HashSig.PolicyIRFixture `hiddenInitializer
  | some value =>
      throwError "SLHDSA_POLICY_RUN_IR_FIXTURE must be absent or exactly 1, got {value}"

end SLHDSAPolicyAudit
