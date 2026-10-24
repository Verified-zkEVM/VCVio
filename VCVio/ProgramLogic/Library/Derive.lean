/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Library.T1.RunNF
public meta import Lean.Elab.Command
public meta import Lean.Meta.Tactic.Split

/-!
# Deriving one-step specifications of oracle handlers

`derive_handler_specs h` states and proves, for a handler `h : ∀ ps, QueryImpl spec m`, one
equation per branch of its query type:

* `h.apply_<branch> : h ps q = rhs`, the handler unfolded at the branch and normalized by the
  monad laws of `simulateQ_nf`;
* `h.run_<branch> : (h ps q).run s = rhs'` when `m` is `StateT σ n`, the one-step run
  normalized by `simulateQ_nf` into the base monad `n`.

The branches are found by splitting the query type: a `Sum` input is split into `.inl` and `.inr`
(recursively, so `(spec₁ + spec₂) + spec₃` has the branches `inl_inl`, `inl_inr` and `inr`), and an
input of another inductive type is split into its constructors when the unfolded handler matches
on it (or only unfolds on constructors, as a definition by pattern matching does).

The handler is unfolded by its equations, or by its definition when they take more arguments than
a query (`fun q s => …`). Sum handlers `impl₁ + impl₂` dispatch to their summands
(`QueryImpl.add_apply_inl` of `simulateQ_nf`, and `queryImplAddApply` when a summand is elaborated
as a plain function); a summand that is a named handler is left applied, to be rewritten by its own
equations. A composition `outer ∘ₛ inner` is unfolded together with the inner handler. In a run, a
`match` on the state, such as a cache lookup, is pushed through `StateT.run` by `stateTRunMatch`,
so the run equation is a `match` of runs in the base monad.

The `run_` lemmas are `@[simp]`: they are the one-step facts that the run of a simulation reduces
to (`simulateQ_nf` leaves a chain of `(impl t).run s`), and simp rewrites the outer `.run` before
the handler application only if the `apply_` lemma is not also a simp lemma. So the `apply_`
lemmas are `@[simp]` only for handlers that are not `StateT` handlers; otherwise they are used by
name. The answer type of a `run_` lemma is stated in simp normal form and not indexed, so the
lemma fires both before and after `simp` rewrites `(spec₁ + spec₂).Range (.inl t)` to
`spec₁.Range t`. A branch that does not unfold or normalize is skipped with a warning.

* `derive_handler_specs h with [l₁, l₂]` adds the theorems or definitions `lᵢ` to the simp set;
* `derive_handler_specs? h` adds nothing and prints the statements it would add.
-/

public meta section

open Lean Meta Elab Command

namespace OracleComp.ProgramLogic.HandlerSpecs

/-- `StateT.run` of a non-dependent `match` is the `match` of the runs of its alternatives. -/
simproc_decl stateTRunMatch (StateT.run _ _) := fun e => do
  let_expr StateT.run σ n α x s := e | return .continue
  let some app ← matchMatcherApp? x | return .continue
  let some uPos := app.uElimPos? | return .continue
  unless app.remaining.isEmpty do return .continue
  if ← lambdaTelescope app.motive fun xs b => return b.hasAnyFVar (xs.contains <| .fvar ·) then
    return .continue
  let tgt := mkApp n (← mkAppM ``Prod #[α, σ])
  let motive ← lambdaTelescope app.motive fun xs _ => mkLambdaFVars xs tgt
  let us := e.getAppFn.constLevels!
  let alts ← (app.alts.zip app.altNumParams).mapM fun (alt, k) => do
    forallBoundedTelescope (← inferType alt) k fun ys _ =>
      mkLambdaFVars ys (mkAppN (.const ``StateT.run us) #[σ, n, α, (mkAppN alt ys).headBeta, s])
  let lvl ← getLevel tgt
  let e' := { app with motive, alts, matcherLevels := app.matcherLevels.set! uPos lvl }.toExpr
  let goal ← mkFreshExprMVar (← mkEq e e')
  try
    for g in ← Split.splitMatch goal.mvarId! x do g.refl
  catch _ => return .continue
  return .visit { expr := e', proof? := ← instantiateMVars goal }

/-- `StateT.run` of a `fun`, or of `StateT.mk` of one, is its body at the initial state. -/
dsimproc_decl stateTRunLam (StateT.run _ _) := fun e => do
  let_expr StateT.run _ _ _ x s := e | return .continue
  let x := if x.isAppOfArity ``StateT.mk 4 then x.appArg! else x
  unless x.isLambda do return .continue
  return .visit (x.beta #[s])

/-- `(impl₁ + impl₂) (.inl t)` is `impl₁ t` and `(impl₁ + impl₂) (.inr t)` is `impl₂ t`, also when
a summand is elaborated as a plain function, where `QueryImpl.add_apply_inl` does not unify. -/
dsimproc_decl queryImplAddApply (@HAdd.hAdd _ _ (QueryImpl _ _) _ _ _ _) := fun e => do
  unless e.isAppOfArity ``HAdd.hAdd 7 &&
      (e.getArg! 3).isAppOf ``QueryImpl.instHAddSumHAddOracleSpec do
    return .continue
  let x := e.getArg! 6
  if x.isAppOfArity ``Sum.inl 3 then return .visit (mkApp (e.getArg! 4) x.appArg!)
  if x.isAppOfArity ``Sum.inr 3 then return .visit (mkApp (e.getArg! 5) x.appArg!)
  return .continue

/-- A branch of the query type: the suffix of its lemma names and the query as a closed
function of the branch variables. -/
structure Branch where
  sfx : List String
  qf : Expr

/-- One generated equation. -/
structure Spec where
  name : Name
  type : Expr
  value : Expr
  simp : Bool

/-- The outcome of a derivation: branches attempted, generated lemmas and, per failing branch,
its failure class (`opaque`, `no progress`, `simp error`, `timeout`, `kernel`). -/
structure Report where
  handler : Name
  branches : Nat := 0
  derived : Nat := 0
  specs : Array Spec := #[]
  failures : Array (String × String × MessageData) := #[]
  ms : Nat := 0

/-- Split the first variable of `Sum` type of a branch into `.inl` and `.inr`. -/
def splitSum? (b : Branch) : MetaM (Option (List Branch)) :=
  lambdaTelescope b.qf fun xs q => do
    for h : i in [:xs.size] do
      let x := xs[i]
      let ty ← whnfR (← inferType x)
      unless ty.isAppOfArity ``Sum 2 do continue
      let nm ← x.fvarId!.getUserName
      let mk (c : Name) (tag : String) (t : Expr) : MetaM Branch :=
        withLocalDeclD nm t fun y => do
          let v := mkApp3 (.const c ty.getAppFn.constLevels!) (ty.getArg! 0) (ty.getArg! 1) y
          return ⟨b.sfx ++ [tag], ← mkLambdaFVars (xs.set! i y) (q.replaceFVar x v)⟩
      return some [← mk ``Sum.inl "inl" (ty.getArg! 0), ← mk ``Sum.inr "inr" (ty.getArg! 1)]
    return none

/-- Split the first variable whose position satisfies `p`, of a non-indexed inductive type with at
least two constructors, into its constructors. -/
def splitCtor? (b : Branch) (p : Nat → Bool) : MetaM (Option (List Branch)) :=
  lambdaTelescope b.qf fun xs q => do
    for h : i in [:xs.size] do
      let x := xs[i]
      unless p i do continue
      let ty ← whnf (← inferType x)
      let .const I us := ty.getAppFn | continue
      let .inductInfo info ← getConstInfo I | continue
      unless info.numIndices == 0 && info.ctors.length ≥ 2 do continue
      let ps := ty.getAppArgs
      let bs ← info.ctors.mapM fun c => do
        let cty ← instantiateForall (← inferType (mkConst c us)) ps
        forallTelescope cty fun fs _ => do
          let ys := xs[:i].toArray ++ fs ++ xs[i+1:].toArray
          let v := mkAppN (mkConst c us) (ps ++ fs)
          return ⟨b.sfx ++ [c.lastComponentAsString], ← mkLambdaFVars ys (q.replaceFVar x v)⟩
      return some bs
    return none

/-- The positions of the variables among `xs` that `e` matches on. -/
def matchedVars (xs : Array Expr) (e : Expr) : MetaM (Array Nat) := do
  let out ← IO.mkRef (#[] : Array Nat)
  forEachExpr e fun s => do
    if let some app ← matchMatcherApp? s (alsoCasesOn := true) then
      for d in app.discrs do
        if let some i := xs.idxOf? d then out.modify (·.push i)
  out.get

/-- Application lemmas of the handler combinators beyond the sums of `simulateQ_nf`. -/
def combinatorLemmas : Array Name :=
  #[``QueryImpl.apply_compose, ``QueryImpl.id_apply, ``QueryImpl.id'_apply,
    ``QueryImpl.ofLift_apply, ``QueryImpl.ofFn_apply, ``QueryImpl.addLift_def,
    ``HasQuery.toQueryImpl_apply]

/-- The simp context normalizing the branches of `h`: `simulateQ_nf`, the combinator lemmas, `h`
and `extras`, with the default simprocs and those of this file. -/
def mkSimpCtx (h : Name) (extras : Array Name) : MetaM (Simp.Context × Simp.SimprocsArray) := do
  let some ext ← getSimpExtension? `simulateQ_nf | throwError "simp set `simulateQ_nf` not found"
  let mut thms ← (← ext.getTheorems).addDeclToUnfold h
  for n in combinatorLemmas ++ extras do
    unless (← getEnv).contains n do continue
    thms ← if ← isProp (← getConstInfo n).type then thms.addConst n else thms.addDeclToUnfold n
  let mut procs ← Simp.getSimprocs
  for n in [``stateTRunMatch, ``stateTRunLam, ``queryImplAddApply] do
    procs ← procs.add n (post := true)
  return (← Simp.mkContext {} #[thms] (← getSimpCongrTheorems), #[procs])

/-- Run `x` on a fresh heartbeat budget, returning the failure class and message of an error. -/
def attempt {α : Type} (x : MetaM α) : MetaM (Except (String × MessageData) α) :=
  tryCatchRuntimeEx (return .ok (← withCurrHeartbeats x)) fun ex =>
    return .error (if ex.isRuntime then "timeout" else "simp error", ex.toMessageData)

/-- The closed equation `∀ bs, lhs = r.expr` with its proof, as the theorem `name`. -/
def mkSpec (name : Name) (bs : Array Expr) (lhs : Expr) (r : Simp.Result) (simp : Bool) :
    MetaM Spec := do
  let type ← instantiateMVars (← mkForallFVars bs (← mkEq lhs r.expr))
  let value ← instantiateMVars (← mkLambdaFVars bs (← r.getProof))
  if type.hasMVar || value.hasMVar then throwError "unassigned metavariables in {name}"
  return { name, type, value, simp }

/-- Add a generated theorem to the environment, checked by the kernel synchronously. -/
def addSpec (lps : List Name) (s : Spec) : MetaM Unit := do
  withOptions (Elab.async.set · false) do
    addDecl (.thmDecl { name := s.name, levelParams := lps, type := s.type, value := s.value })
  if s.simp then addSimpTheorem simpExtension s.name true false .global (eval_prio default)

/-- The name of the lemma of kind `kind` (`apply` or `run`) on the branch with suffix `sfx`. -/
def specName (h : Name) (kind : String) (sfx : List String) : Name :=
  .str h (if sfx.isEmpty then kind else kind ++ "_" ++ "_".intercalate sfx)

/-- The data shared by the branches of one derivation. -/
structure Ctx where
  h : Name
  lps : List Name
  hps : Expr
  st? : Option (Expr × Expr)
  ctx : Simp.Context
  procs : Simp.SimprocsArray
  /-- The default simp set, putting the answer type of a run in the form `simp` leaves it in. -/
  dctx : Simp.Context

/-- The handler constants other than `h`, applied to a query, that are the program of a
`simulateQ` in `e`: the inner handlers of a composition `outer ∘ₛ inner`. -/
def innerHandlers (h : Name) (e : Expr) : MetaM (Array Name) := do
  let out ← IO.mkRef (#[] : Array Name)
  forEachExpr e fun s => do
    unless s.isAppOfArity ``simulateQ 7 do return
    let .const c _ := (s.getArg! 6).getAppFn | return
    if c == h || (← out.get).contains c then return
    if ← forallTelescope (← getConstInfo c).type fun ps b =>
        return b.isAppOfArity ``QueryImpl 3 && (s.getArg! 6).getAppNumArgs == ps.size + 1 then
      out.modify (·.push c)
  out.get

/-- The simp normal form of `lhs`, unfolding `h` by its equations or else by its definition, and
then the inner handlers of compositions; `none` if this makes no progress. -/
def normalize (c : Ctx) (lhs : Expr) : MetaM (Option Simp.Result) := do
  for start in [lhs, ← deltaExpand lhs (· == c.h)] do
    let mut (r, _) ← simp start c.ctx c.procs
    let inner ← innerHandlers c.h r.expr
    unless inner.isEmpty do
      let thms ← inner.foldlM (·.addDeclToUnfold ·) c.ctx.simpTheorems[0]!
      (r, _) ← simp start (c.ctx.setSimpTheorems #[thms]) c.procs
    r := { r with expr := ← instantiateMVars r.expr }
    if r.expr != lhs then return some r
  return none

/-- Derive the lemmas of a branch, splitting it first at `Sum` inputs and at the inputs that the
unfolded handler matches on (at most `fuel` constructor splits deep). -/
partial def visit (c : Ctx) (b : Branch) (fuel : Nat) : StateRefT Report MetaM Unit := do
  if let some bs ← splitSum? b then
    for b in bs do visit c b fuel
    return
  let tag := if b.sfx.isEmpty then "q" else "_".intercalate b.sfx
  let fail (cls : String) (msg : MessageData) : StateRefT Report MetaM Unit :=
    modify fun r => { r with failures := r.failures.push (tag, cls, msg) }
  let split? ← lambdaTelescope b.qf fun xs q => do
    let lhs := mkApp c.hps q
    match ← attempt (normalize c lhs) with
    | .error (cls, msg) => fail cls msg; return none
    | .ok r? =>
      if fuel > 0 then
        let mv ← match r? with
          | some r => matchedVars xs r.expr
          | none => pure (Array.range xs.size)
        if let some bs ← splitCtor? b mv.contains then return some bs
      modify fun r => { r with branches := r.branches + 1 }
      let some r := r? | fail "no progress" m!"{lhs} does not unfold"; return none
      let mut specs := #[(← mkSpec (specName c.h "apply" b.sfx) (c.hps.getAppArgs ++ xs) lhs r
        c.st?.isNone)]
      if let some (σ, _) := c.st? then
        let runSpec? ← withLocalDeclD `s σ fun s => do
          let lhs ← mkAppM ``StateT.run #[lhs, s]
          let (α, _) ← dsimp (lhs.getArg! 2) c.dctx
          let lhs := mkAppN lhs.getAppFn (lhs.getAppArgs.set! 2 α)
          let bs := c.hps.getAppArgs ++ xs.push s
          -- the answer type is not indexed, so the lemma also fires where it is not normalized
          let key := mkAppN lhs.getAppFn (lhs.getAppArgs.set! 2 (DiscrTree.mkNoindexAnnotation α))
          match ← attempt (normalize c lhs) with
          | .ok (some r) => return some (← mkSpec (specName c.h "run" b.sfx) bs key r true)
          | .ok none => fail "no progress" m!"{lhs} does not normalize"; return none
          | .error (cls, msg) => fail cls msg; return none
        specs := specs ++ runSpec?.toArray
      let mut ok := false
      for s in specs do
        try
          addSpec c.lps s
          ok := true
          modify fun r => { r with specs := r.specs.push s }
        catch ex => fail "kernel" ex.toMessageData
      if ok then modify fun r => { r with derived := r.derived + 1 }
      return none
  if let some bs := split? then
    for b in bs do visit c b (fuel - 1)

/-- Derive and add the branch lemmas of the handler `h`, with `extras` added to the simp set. -/
def derive (h : Name) (extras : Array Name := #[]) : MetaM Report := do
  let t0 ← IO.monoMsNow
  let ci ← getConstInfo h
  let rep ← forallTelescope ci.type fun ps body => do
    unless body.isAppOfArity ``QueryImpl 3 do
      throwError "{h} is not a handler: its type does not end in `QueryImpl spec m`"
    if !ci.hasValue || (← isProjectionFn h) then
      return { handler := h, failures := #[("q", "opaque", m!"{h} has no visible definition")] }
    let m ← whnfR (body.getArg! 2)
    let st? := if m.isAppOfArity ``StateT 2 then some (m.getArg! 0, m.getArg! 1) else none
    let (ctx, procs) ← mkSimpCtx h extras
    let dctx ← Simp.mkContext {} #[← getSimpTheorems] (← getSimpCongrTheorems)
    let c : Ctx := { h, lps := ci.levelParams, st?, ctx, procs, dctx,
                     hps := mkAppN (.const h (ci.levelParams.map mkLevelParam)) ps }
    let b ← withLocalDeclD `q (body.getArg! 0) fun q => mkLambdaFVars #[q] q
    let ((), rep) ← (visit c ⟨[], b⟩ 2).run { handler := h }
    return rep
  return { rep with ms := (← IO.monoMsNow) - t0 }

/-- Report the failing branches of a derivation as warnings. -/
def logFailures (rep : Report) : MetaM Unit := do
  for (tag, cls, msg) in rep.failures do
    logWarning
      m!"derive_handler_specs {rep.handler}: skipped branch {tag} ({cls}):{indentD msg}"

/-- Elaborate `derive_handler_specs`, adding the lemmas unless `dry`. -/
def elabDerive (id : Ident) (extras : Array Syntax) (dry : Bool) : CommandElabM Unit :=
  liftTermElabM do
    let h ← realizeGlobalConstNoOverloadWithInfo id
    let extras ← extras.mapM (realizeGlobalConstNoOverloadWithInfo ·)
    let rep ← if dry then withoutModifyingEnv (derive h extras) else derive h extras
    logFailures rep
    if dry then
      let stmts := rep.specs.map fun s => m!"theorem {s.name} : {s.type}"
      logInfo m!"{rep.specs.size} lemmas on {rep.derived}/{rep.branches} branches:\
        {indentD (MessageData.joinSep stmts.toList "\n")}"
    else if rep.specs.isEmpty then
      logWarning m!"derive_handler_specs {h}: no lemma derived"

/-- `derive_handler_specs h` adds the one-step equations `h.apply_<branch>` and, for `StateT`
handlers, `h.run_<branch>` of the handler `h`; `with [l, …]` adds lemmas or definitions to the
normalizing simp set. -/
elab (name := deriveHandlerSpecs) "derive_handler_specs " id:ident
    ls:(" with " "[" ident,* "]")? : command =>
  elabDerive id (ls.map (·.raw[2].getSepArgs) |>.getD #[]) false

/-- `derive_handler_specs? h` prints the equations that `derive_handler_specs h` would add. -/
elab (name := deriveHandlerSpecsDry) "derive_handler_specs? " id:ident
    ls:(" with " "[" ident,* "]")? : command =>
  elabDerive id (ls.map (·.raw[2].getSepArgs) |>.getD #[]) true

end OracleComp.ProgramLogic.HandlerSpecs
