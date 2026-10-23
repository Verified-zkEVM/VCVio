/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio
import Examples
import LatticeCrypto
import HashSig
import VCVioFoxglove
import Foxglove
import VCVio.ProgramLogic.Tactics.Common.Route

/-!
# Route census

Classify the statement of every theorem in the cryptographic libraries with
`OracleComp.ProgramLogic.Route.classify`, and report how declarations and proof lines split
across routes. Run with `lake env lean scripts/RouteCensus.lean`. The per-declaration rows go to
`.lake/route-census.csv`; the summary is printed.
-/

open Lean Meta Elab Command OracleComp.ProgramLogic.Route

/-- Module prefixes whose theorems are classified. -/
def censusPrefixes : List Name :=
  [`VCVio.CryptoFoundations, `Examples, `LatticeCrypto, `HashSig, `Foxglove, `VCVioFoxglove]

/-- Whether a declaration name is an auxiliary one. -/
def isAuxName (n : Name) : Bool :=
  n.isInternalDetail || n.components.any fun c ↦
    let s := c.toString
    s.startsWith "_" || s.startsWith "proof_" || s.startsWith "match_" || s == "eq_def" ||
      s.startsWith "eq_" || s == "induct" || s.startsWith "_unfold" || s == "sizeOf_spec" ||
      s == "inj" || s == "injEq" || s == "ext_iff" || s == "noConfusion"

run_cmd liftTermElabM do
  let env ← getEnv
  let mut rows : Array String := #["decl,module,route,fox,judg,relOp,lhs,rhs,carrier,interp,premises,ns,lines"]
  let mut foxCandidates : Nat × Nat := (0, 0)
  let mut perRoute : Std.HashMap String (Nat × Nat) := {}
  let mut perFamily : Std.HashMap (String × String) Nat := {}
  let mut times : Array Nat := #[]
  let mut noRouteHeads : Std.HashMap Name Nat := {}
  for (n, ci) in env.constants.map₁.toList do
    let .thmInfo _ := ci | continue
    if isAuxName n then continue
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    let some pre := censusPrefixes.find? (·.isPrefixOf mod) | continue
    let t0 ← IO.monoNanosNow
    let k ← try classify ci.type catch _ => pure {}
    let t1 ← IO.monoNanosNow
    times := times.push (t1 - t0)
    let lines := match ← findDeclarationRanges? n with
      | some r => r.range.endPos.line - r.range.pos.line + 1
      | none => 0
    let tag := k.route.tag
    let fox := k.foxProdEvent && k.route != .foxglove
    let (d, l) := perRoute.getD tag (0, 0)
    perRoute := perRoute.insert tag (d + 1, l + lines)
    perFamily := perFamily.insert (pre.toString, tag) (perFamily.getD (pre.toString, tag) 0 + 1)
    if k.route == .none then
      let h := (← instantiateMVars ci.type).getForallBody.getAppFn.constName?.getD `other
      noRouteHeads := noRouteHeads.insert h (noRouteHeads.getD h 0 + 1)
    if fox then foxCandidates := (foxCandidates.1 + 1, foxCandidates.2 + lines)
    rows := rows.push s!"{n},{mod},{tag},{fox},{repr k.judg},{k.relOp.getD .anonymous},{repr k.lhs},\
      {repr k.rhs},{repr k.carrier},{repr k.interp},{k.premises},{t1 - t0},{lines}"
  IO.FS.writeFile ".lake/route-census.csv" (String.intercalate "\n" rows.toList)
  let total := perRoute.fold (fun acc _ v ↦ acc + v.1) 0
  let totalLines := perRoute.fold (fun acc _ v ↦ acc + v.2) 0
  let sorted := perRoute.toArray.qsort (fun a b ↦ a.2.2 > b.2.2)
  let mut msg := s!"{total} theorems, {totalLines} lines\n"
  for (tag, d, l) in sorted do
    msg := msg ++ s!"  {tag}: {d} decls, {l} lines\n"
  let ts := times.qsort (· < ·)
  msg := msg ++ s!"classify: p50 {ts[ts.size / 2]! / 1000}µs, p99 {ts[ts.size * 99 / 100]! / 1000}µs, \
    max {ts.back! / 1000}µs\n"
  msg := msg ++ s!"Foxglove candidates (pair events): {foxCandidates.1} decls, {foxCandidates.2} lines\n"
  msg := msg ++ "by library:\n"
  for p in censusPrefixes do
    let entries := perFamily.toArray.filter (·.1.1 == p.toString) |>.qsort (fun a b ↦ a.2 > b.2)
    msg := msg ++ s!"  {p}: {entries.toList.map fun e ↦ s!"{e.1.2}={e.2}"}\n"
  let heads := noRouteHeads.toArray.qsort (fun a b ↦ a.2 > b.2)
  msg := msg ++ s!"no-route heads: {(heads.toList.take 20).map fun h ↦ s!"{h.1}={h.2}"}"
  logInfo msg
