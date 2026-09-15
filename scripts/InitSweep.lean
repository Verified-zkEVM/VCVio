/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import Lean

/-!
# Init sweep: whole-library accounting of what a module costs when it is loaded

Walks the compiled environment and flags every constant whose module initialiser evaluates
something — before any `main` runs — when the value that runs names an entry point that
enumerates a type.

The predicate, in one sentence: *a constant is flagged when loading its module evaluates a
value on its behalf — its own, because its compiled declaration takes no parameters, or an
`initialize` body registered for it — and that value names one of the
`enumerationEntryPoints` below.*

Every clause is load-bearing, and every number below was measured over this repository's
own build; `scripts/test-initsweep.sh` carries the fixtures that falsify each one.

* **the module initialiser evaluates something for it.**
  `Lean.Compiler.LCNF.emitDeclInit` has exactly two branches that emit work into the
  module initialisation function: it calls the initialiser registered for an `initialize`
  declaration, and it assigns `x = _init_x();` for a declaration whose parameter list is
  empty (the LLVM backend's `Lean.IR.EmitLLVM` makes the same decision on `xs.size == 0`).
  `loadTimeSource` mirrors those two branches and nothing else. A declaration with
  parameters compiles to a procedure and costs nothing until it is called; one without is
  a value whose cost is paid at load time whether or not anything reads it.

  That correspondence is checked against emitted code rather than only read off the
  compiler source. Over the seven swept libraries the predicate names 27 constants on the
  `initialize` route and 511 on the value route; the C under `.lake/build/ir/` for the
  same libraries contains 27 initialiser calls, 20 of which assign a result (the 20
  `initialize x : T ← e` declarations, the other 7 being `initialize do` blocks), and 499
  `_init_` assignments — see `isCompiledValue` for where the remaining 12 go. For one
  module the correspondence was checked name by name: for `VCVio.Prelude` the predicate
  names 9 constants and `.lake/build/ir/VCVio/Prelude.c` performs exactly those 9
  evaluations.

  This is where a `noncomputable` marker acts, and why a source-level rule is the wrong
  instrument: marking an instance `noncomputable` removes the instance's own compiled code
  and leaves the compiled auxiliary that carries the work, so the two spellings differ in
  source and not in effect. `@[extern]` declarations are excluded in the other direction:
  the emitter calls the foreign symbol, and the Lean-side value is dead.

  The clause is also strictly narrower than "its type is not a `∀`", which the shape of
  the hazard suggests and which would be wrong: 531 constants of the swept libraries have
  a parameterless compiled declaration, while 867 have a compiled declaration and a
  non-`∀` type, the extra 336 being values whose type unfolds to a function type.
* **that value names an enumeration entry point.** The load-time population is 538
  constants, and the rest of it is parser descriptors, macro expanders, attribute and
  environment-extension registrations, `IO.Ref` cells and small closed values; a ceiling
  on *that* number would be noise. The name test is what separates an initialiser that
  allocates a few words from one that materialises a `Finset` of the elements of a type.

Compiler-internal names are deliberately **not** skipped. The hazard this gate exists for
is carried by an auxiliary, `….instFintypeYLimitedPrimitives._aux_1`, and not by the
user-written instance; skipping internal names would make the gate blind to every spelling
of it.

Modes (run after `lake build`):

```
lake exe initsweep                     # summary only
lake exe initsweep --out report.json   # also write the whole load-time population
lake exe initsweep --check             # gate against scripts/init_sweep_baseline.tsv
lake exe initsweep --update-baseline   # rewrite the baseline from the current build
```

The committed baseline (`scripts/init_sweep_baseline.tsv`) is a per-library ceiling in the
shape of `scripts/expose_boundary_baseline.tsv`: lower is always accepted, higher needs an
explicit and reviewable baseline change. Every swept library is at `0`, so the gate carries
no exception list at all — which is the cheapest shape a ratchet can have, and the reason
the entry-point list is drawn as narrowly as the measurements allow.

Known limits, measured rather than assumed:

* It reads the value that runs, and only that value. A helper function that returns
  `Finset.univ` and is *called* from an initialiser is the same hazard and is not flagged.
  Following the compiled code instead does not help: by the time the IR exists the
  enumeration has been folded into closed terms whose names carry no signal at all
  (measured — the fixture's flagged auxiliary reaches `Fintype.piFinset._redArg` through
  its IR and no `Finset.univ` anywhere).
* Conversely, the value it reads is the kernel's, so an entry point that survives only in
  an erased position — inside a proof argument — would be a false positive. None occurs
  in the swept libraries; the summary line reports the whole load-time population so the
  margin stays visible.
* It says nothing about how **large** an initialiser is, only about its shape. A `Fintype`
  on an eight-element type routed through `Finset.univ` would be flagged.
* Unbounded *numeric* ranges — `Finset.range (2 ^ 40)` and friends — are the same hazard
  and are deliberately **not** in the entry-point list. `List.range` has one legitimate
  bounded use in the swept tree (`SLHDSA.Concrete.Keccak.piLUT`), so a range clause could
  not be baselined at zero, and an entry-point list that is zero everywhere is worth more
  than one that ships with an exception.
* It sees only what the swept roots transitively import — the same blind spot
  `scripts/AxiomSweep.lean` documents, with the same mitigation (pair it with the
  import-completeness gate). The test libraries are not swept: `HashSigTest` is a
  `submodules` glob with no umbrella module and cannot be a root, so the gate covers the
  libraries a test executable *imports* rather than the executables themselves.
* It is a static check on the environment and never runs anything, which is also why the
  fixtures are tiny: the sweep imports them.

Exit codes are a contract with CI — `1` is a ratchet verdict, anything else an
infrastructure failure — which is why `main` traps uncaught exceptions into `2`. The
`opaqueValues` line of the summary is the gate's own completeness claim: it counts
load-time constants whose value could not be read, and therefore were accepted without
being looked at.

`scripts/test-initsweep.sh` exercises all of this against the `VCVioInitSweepTestFixtures`
library, whose fixtures carry the three routes into the hazard and one negative control
per clause.
-/
open Lean

namespace InitSweep

/-- Root modules swept when no `--root` is given: the same seven non-test libraries
`scripts/AxiomSweep.lean` sweeps, and for the same reason — `Interop` is the declared TCB,
bounded by its import-isolation gate, and is not built by the main CI build job. -/
def defaultRoots : Array Name :=
  #[`VCVio, `ToMathlib, `Extern, `LatticeCrypto, `HashSig, `Examples, `VCVioWidgets]

/-- The constants whose appearance in an eagerly-initialised value means the initialiser
enumerates a type. Listed in source, with the reason each one is here, so the gate's reach
is auditable where the gate is rather than in a data file.

* `Finset.univ` — the enumeration itself; the elements of a type as a `Finset`.
* `Fintype.elems` — the field `Finset.univ` projects, reached directly by instance code.
* `Fintype.card` — forces the enumeration in order to count it.
* `Fintype.piFinset` — the product enumeration; this is what the `2 ^ 128` initialiser
  that motivated this gate actually built.
* `Fintype.ofFinite` — the noncomputable route from a `Finite` proof to a `Fintype`. A
  constant naming it *and* carrying compiled code means the route that was supposed to
  erase the enumeration did not.
* `Fintype.ofEquiv` — transports an enumeration along an equivalence, so it inherits the
  size of the source type.
* `Set.toFinset` — enumerates the ambient type in order to filter it. -/
def enumerationEntryPoints : List Name :=
  [`Finset.univ, `Fintype.elems, `Fintype.card, `Fintype.piFinset, `Fintype.ofFinite,
    `Fintype.ofEquiv, `Set.toFinset]

/-- The entry points are written as unchecked name literals because this tool imports only
`Lean` — linking Mathlib into a gate that has to run after every build is not worth it —
so nothing at elaboration time checks that they exist. `checkEntryPoints` does it instead,
against the environment actually swept, and fails the run as an infrastructure error
rather than reporting a clean verdict. The gate therefore fails **closed**: if one of
these is renamed upstream, `--check` goes red until someone re-derives the list, instead
of silently matching nothing. -/
def checkEntryPoints (env : Environment) : Except String Unit := do
  let missing := enumerationEntryPoints.filter fun n => (env.find? n).isNone
  if !missing.isEmpty then
    throw s!"entry point(s) not present in the swept environment: {missing} \
      (they were renamed upstream, or the swept roots do not reach Mathlib; \
      re-derive `enumerationEntryPoints` in scripts/InitSweep.lean)"
  return ()

/-- Whether the backend emits `n`'s own value into its module's initialisation function:
a compiled function declaration with no parameters. `@[extern]` declarations are excluded,
because the emitter calls the foreign symbol and never evaluates the Lean-side value.

This over-approximates, deliberately and in the harmless direction. `emitDeclInit` skips a
parameterless declaration whose value is a simple ground expression or a lifted closed
term, laying it out as a static literal instead; both of those caches are non-persistent
environment extensions, so neither survives the olean import this tool does and neither
can be consulted from here. Measured over the seven swept libraries: 511 constants take
this route and the emitted C carries 499 `_init_` assignments, so 12 are exempted —
notation constants and their like, whose values are literals. A literal cannot enumerate a
type, so the surplus can only cost a false positive, and costs none. -/
def isCompiledValue (env : Environment) (n : Name) : Bool :=
  match Lean.IR.findEnvDecl env n with
  | some (.fdecl (xs := xs) ..) => xs.isEmpty
  | some (.extern ..) => false
  | none => false

/-- What loading a module makes `n` cost, and which constant holds the code that runs.
`none` when `n` costs nothing at load time.

`Lean.Compiler.LCNF.emitDeclInit` has exactly these two branches, and this mirrors them:
an `initialize` declaration is called through its registered initialiser function, and a
parameterless declaration is assigned from its `_init_` function. `initialize x : T ← e`
stores `e` in a separate constant and leaves `x` itself valueless, which is why the source
of the value is reported separately from the declaration that carries it — reading `x`
alone would accept every `initialize` in the repository without looking at anything. -/
def loadTimeSource (env : Environment) (n : Name) : Option (String × Name) :=
  if let some initFn := Lean.getInitFnNameFor? env n then
    some ("initialize", initFn)
  else if Lean.isIOUnitInitFn env n then
    some ("initialize", n)
  else if isCompiledValue env n then
    some ("value", n)
  else
    none

/-- The entry points the value of `n` names, in `enumerationEntryPoints` order, or `#[]`
if it names none or has no readable value. -/
def entryPointsOf (env : Environment) (n : Name) : Array String := Id.run do
  let some ci := env.find? n | return #[]
  let some value := ci.value? | return #[]
  let used := value.getUsedConstants
  let mut hits : Array String := #[]
  for e in enumerationEntryPoints do
    if used.contains e then hits := hits.push e.toString
  return hits

/-- One constant the module initialiser evaluates. `library` is the swept root the
constant's module sits under, which is the key the baseline uses. `via` is `value` when the
declaration is itself the parameterless value the initialiser assigns, and `initialize`
when the code that runs is an initialiser body registered for it; `source` is the constant
whose value was read; `entryPoints` is empty for everything the gate accepts. -/
structure Entry where
  name : String
  module : String
  library : String
  via : String
  source : String
  entryPoints : Array String
  deriving ToJson

/-- What one sweep of the environment found. `loadTime` is the whole population the
entry-point test narrows: every constant whose module initialiser evaluates something. It
is reported in full under `--out` and deliberately not gated on. -/
structure Census where
  constants : Nat
  modules : Nat
  /-- Load-time constants whose value the sweep could not read, and which the name test
  therefore accepted without looking at anything. This is the gate's own blind spot; it is
  reported on every run so it cannot grow unnoticed. -/
  opaqueValues : Nat
  loadTime : Array Entry

/-- The load-time constants the entry-point test rejects. -/
def Census.offenders (c : Census) : Array Entry :=
  c.loadTime.filter (!·.entryPoints.isEmpty)

/-- Enumerate every constant of every module under one of `roots` and apply the predicate.
A constant realised on demand can appear in several modules' `constNames`; it is counted
once, under the first module that carries it. -/
def census (roots : Array Name) : CoreM Census := do
  let env ← getEnv
  let mut seen : Std.HashSet Name := {}
  let mut constants := 0
  let mut modules := 0
  let mut opaqueValues := 0
  let mut loadTime : Array Entry := #[]
  for (mname, mdata) in env.header.moduleNames.zip env.header.moduleData do
    -- A module is attributed to the root it was swept under, not to its own first
    -- component, so `--root Foo.Bar` and the baseline agree on one key.
    if let some root := roots.find? (·.isPrefixOf mname) then
      modules := modules + 1
      for c in mdata.constNames do
        if seen.contains c then continue
        seen := seen.insert c
        constants := constants + 1
        let some (via, source) := loadTimeSource env c | continue
        if ((env.find? source).bind (·.value?)).isNone then
          opaqueValues := opaqueValues + 1
        loadTime := loadTime.push {
          name := c.toString
          module := mname.toString
          library := root.toString
          via := via
          source := source.toString
          entryPoints := entryPointsOf env source }
  return { constants, modules, opaqueValues,
           loadTime := loadTime.qsort (fun a b => a.name < b.name) }

/-- Per-library offender counts, in the order `roots` names the libraries, so the baseline
file and the report are both deterministic. -/
def perLibrary (roots : Array Name) (offenders : Array Entry) : Array (String × Nat) :=
  (roots.map (·.toString)).qsort (· < ·) |>.map fun lib =>
    (lib, (offenders.filter (·.library == lib)).size)

/-- Render a baseline file: one `library<TAB>count` line per swept library. -/
def renderBaseline (rows : Array (String × Nat)) : String :=
  rows.foldl (init := "") fun acc (lib, n) => acc ++ s!"{lib}\t{n}\n"

/-- Parse a baseline file. Blank lines are ignored; anything else must be exactly
`library<TAB>count` with a decimal count, so a corrupted file fails loudly rather than
silently reading as a ceiling of zero. -/
def parseBaseline (text : String) : Except String (Array (String × Nat)) := do
  let mut rows : Array (String × Nat) := #[]
  for raw in text.splitOn "\n" do
    let line := raw.trimAscii.copy
    if line.isEmpty then continue
    match line.splitOn "\t" with
    | [lib, count] =>
      let lib := lib.trimAscii.copy
      let some n := (count.trimAscii.copy).toNat? | throw s!"not a decimal count: {line}"
      if lib.isEmpty then throw s!"empty library name: {line}"
      rows := rows.push (lib, n)
    | _ => throw s!"expected `library<TAB>count`: {line}"
  if rows.isEmpty then throw "baseline lists no libraries"
  return rows

/-- Compare the current census against the committed ceiling. Returns the exit code: `1`
iff some library carries more flagged constants than its baseline allows. A library the
baseline does not mention has a ceiling of zero, so a library cannot gain flagged
constants by being left out of the file. -/
def runCheck (cur : Census) (roots : Array Name) (basePath : String) : IO UInt32 := do
  if !(← System.FilePath.pathExists basePath) then
    IO.eprintln s!"initsweep: baseline {basePath} not found; \
      create it with `lake exe initsweep --update-baseline`"
    return 2
  let base ← match parseBaseline (← IO.FS.readFile basePath) with
    | .ok rows => pure rows
    | .error e =>
      IO.eprintln s!"initsweep: cannot parse baseline {basePath}: {e}"
      return 2
  let rows := perLibrary roots cur.offenders
  let ceiling (lib : String) : Nat := (base.find? (·.1 == lib)).map (·.2) |>.getD 0
  let over := rows.filter fun (lib, n) => n > ceiling lib
  if !over.isEmpty then
    IO.eprintln s!"initsweep: {over.size} library(ies) gained eagerly-initialised constants \
      that enumerate a type:"
    for (lib, n) in over do
      IO.eprintln s!"  {lib}: {n} flagged, baseline ceiling {ceiling lib}"
      for o in cur.offenders do
        if o.library == lib then
          IO.eprintln s!"    {o.name}  ({o.module})  via {o.via} {o.source}  \
            names {o.entryPoints}"
    IO.eprintln "initsweep: a top-level constant of non-function type is evaluated when its \
      module is loaded, before any `main` runs. Route the finiteness argument through \
      `Fintype.ofFinite` (a `Prop`-valued `Finite` instance leaves no compiled code), or \
      give the declaration a parameter so it is called rather than initialised."
    IO.eprintln s!"initsweep: `noncomputable` is not a fix — it removes the instance's own \
      code and leaves the compiled auxiliary that carries the work."
    return 1
  let under := rows.filter fun (lib, n) => n < ceiling lib
  if !under.isEmpty then
    IO.println s!"initsweep: good news — {under.size} library(ies) are below their ceiling; \
      run `lake exe initsweep --update-baseline` to shrink the baseline:"
    for (lib, n) in under do
      IO.println s!"  {lib}: {n} flagged, baseline ceiling {ceiling lib}"
  IO.println "initsweep: check passed (no library over its ceiling)."
  return 0

/-- Rewrite the baseline from the current build. Raising an entry above zero is allowed
and is the escape hatch, in the same shape `scripts/check-expose-boundary.sh` uses: the
diff is one line per library and has to be argued in review. -/
def runUpdate (cur : Census) (roots : Array Name) (basePath : String) : IO UInt32 := do
  IO.FS.writeFile basePath (renderBaseline (perLibrary roots cur.offenders))
  IO.println s!"initsweep: wrote baseline to {basePath}"
  return 0

structure Config where
  roots : Array Name := #[]
  out? : Option String := none
  check : Bool := false
  update : Bool := false
  baseline : String := "scripts/init_sweep_baseline.tsv"

def parseArgs : List String → Config → Except String Config
  | [], cfg => .ok cfg
  | "--check" :: rest, cfg => parseArgs rest { cfg with check := true }
  | "--update-baseline" :: rest, cfg => parseArgs rest { cfg with update := true }
  | "--out" :: path :: rest, cfg => parseArgs rest { cfg with out? := some path }
  | "--baseline" :: path :: rest, cfg => parseArgs rest { cfg with baseline := path }
  | "--root" :: mod :: rest, cfg =>
    parseArgs rest { cfg with roots := cfg.roots.push mod.toName }
  | arg :: _, _ => .error s!"initsweep: unknown or incomplete argument: {arg}\n\
      usage: lake exe initsweep [--out FILE] [--check] [--update-baseline] \
      [--baseline FILE] [--root MOD]*\n      (--check and --update-baseline are mutually exclusive)"

end InitSweep

open InitSweep in
/-- Tool body. Exit codes are a contract with CI, which reads `1` as a ratchet verdict and
anything else as an infrastructure failure; `main` wraps this so an uncaught exception
cannot masquerade as the former. -/
unsafe def run (args : List String) : IO UInt32 := do
  let cfg ← match parseArgs args {} with
    | .ok cfg => pure cfg
    | .error e => IO.eprintln e; return 2
  if cfg.check && cfg.update then
    IO.eprintln "initsweep: --check and --update-baseline are mutually exclusive"
    return 2
  let roots := if cfg.roots.isEmpty then defaultRoots else cfg.roots
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← try
      importModules (roots.map ({ module := · })) {} (trustLevel := 1024)
        (loadExts := true)
    catch e =>
      IO.eprintln s!"initsweep: cannot import root modules {roots}: {e.toString}\n\
        (roots must be importable modules — glob-based libs without an umbrella \
        module cannot be swept by library name)"
      return (2 : UInt32)
  match checkEntryPoints env with
    | .ok _ => pure ()
    | .error e => IO.eprintln s!"initsweep: {e}"; return (2 : UInt32)
  let (cur, _) ← (census roots).toIO { fileName := "<initsweep>", fileMap := default } { env }
  IO.println s!"initsweep: {cur.constants} constants across {cur.modules} modules \
    under {roots}"
  IO.println s!"  evaluated when their module is loaded: {cur.loadTime.size}"
  IO.println s!"  of those, with no readable value (blind spot): {cur.opaqueValues}"
  IO.println s!"  of those, naming a type-enumeration entry point: {cur.offenders.size}"
  if let some out := cfg.out? then
    let report := Json.mkObj [
      ("roots", toJson (roots.map (·.toString))),
      ("constantCount", toJson cur.constants),
      ("loadTimeCount", toJson cur.loadTime.size),
      ("opaqueValueCount", toJson cur.opaqueValues),
      ("loadTime", toJson cur.loadTime)]
    IO.FS.writeFile out (report.pretty ++ "\n")
    IO.println s!"initsweep: wrote report to {out}"
  if cfg.update then
    return (← runUpdate cur roots cfg.baseline)
  if cfg.check then
    return (← runCheck cur roots cfg.baseline)
  return 0

open InitSweep in
unsafe def main (args : List String) : IO UInt32 := do
  try
    run args
  catch e =>
    IO.eprintln s!"initsweep: internal error: {e}"
    return 2
