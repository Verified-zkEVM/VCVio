# Handlers as one-field structures

Status: describes the change that makes `QueryImpl` (VCVio) and `PFunctor.Handler` (PolyFun)
one-field structures, the evidence for it, and what porting ArkLib to it showed. The guide for
writing handlers is the *QueryImpl* section of
[`docs/agents/oracle-comp.md`](../agents/oracle-comp.md); when to choose a structure over an
abbreviation is in
[`docs/agents/module-system.md`](../agents/module-system.md).

## The change

Both types were reducible function types:

```lean
@[reducible] def QueryImpl (spec : OracleSpec ι) (m : Type u → Type v) :=
  (x : spec.Domain) → m (spec.Range x)
```

Instance search unfolds reducible definitions, so an instance stated for handlers was also an
instance for every function of the same shape. The `HAdd` that sums handlers over a sum of
interfaces therefore competed with pointwise addition of ordinary functions. Both types are now
structures with one field:

```lean
structure QueryImpl (spec : OracleSpec ι) (m : Type u → Type v) where
  toFun : (x : spec.Domain) → m (spec.Range x)
```

A handler coerces to its answer function (`CoeFun`, with the projection registered as a coercion),
so `impl x`, `simulateQ impl oa` and CSLib's `FreeM.liftM h` read as before. A function does not
coerce to a handler. `impl.toHandler` and `QueryImpl.ofHandler` convert between VCVio's and
PolyFun's structures. PolyFun's `HandlerCoercion` test fixes the coercion behaviour: which
coercions elaborate and which do not, application lemmas at abstract and literal interfaces, `+` on
handlers and on functions, and that kernel comparison does not reduce a handler's answers.

## Using handlers

A handler built by the constructor is used through the equation for its application, as bundled
morphisms are in Mathlib. `@[simps]` generates the equation. `@[simps -isSimp]` generates it without
the simp attribute; it is used where the equation competes with a preferred lemma (a `run` or
`evalDist` lemma) or where it would leave a `match` on a variable. Proofs then name `foo_apply`.

Unfolding a handler instead (`simp only [foo]`) makes `simp` traverse its whole body at each
occurrence, and leaves `{ toFun := … }` terms that later rewrites do not match. A first version of
this change that relied on unfolding was markedly slower in the modules that unfold handlers.
Mathlib (`v4.36.0`) uses the same pattern: of 2785 constructor-built definitions of 22 bundled
types, 1928 have an application lemma and 1802 have a simp one, and about 290 of 8363 `simps` uses,
counted by text, are `-isSimp`.

Equalities of handlers use `ext` (`ext t : 1` stops at the answers) or `QueryImpl.ext`.

## Enforcement

The environment linter `handlerApply` (PolyFun) reports a definition headed by the constructor of a
handler structure that is reducible or has no application lemma: a stated theorem of its module, or
a simp lemma, whose left side applies it. Equation lemmas that Lean derives from the definition do
not count. `PolyFun.Lint.handlerApplyFor` takes a list of structures; VCVio's `queryImplApply`
instantiates it for `QueryImpl`.

The linters run where they are imported. In VCVio's CI that is the `VCVio` root; the other five
roots import VCVio modules but not the umbrella. They were run on all six roots for this change and
report nothing. ArkLib does not run environment linters in CI.

## Cost

Measured with `lean -j1` per module against the pins-only parent commit, on a machine running
other work.

- **VCVio.** All 810 `VCVio/` modules, one paired run each, three at a time: 1655 s before and
  1649 s after (0.997×). The 45 modules that differed by more than 20% were re-timed sequentially
  (median of three). All but four were within 12%, so the single runs were mostly noise. The four
  (BLS `Generic/Cache` 1.84×, `Generic/ReductionCost` 1.74×, `AGM/Reductions` 1.31×, Fiat–Shamir
  `Stateful/Compatibility` 1.27×) unfolded handlers by name in `simp`. Naming the application
  lemmas instead brought them to 1.00–1.05× and lowered the total by about 6 s more. The largest
  remaining differences are `GPVHashAndSign/GameRuns` (1.20×), `PointerChainPuzzle/HidingIdeal` and
  `QueryTracking/QueryLog` (1.12× each).
- **ArkLib.** 1164 of 1277 `ArkLib/` modules, one run each, before the run was stopped: 3041 s
  before and 2968 s after (0.976×). Single runs of 2–5 s modules vary by up to 30% here; the
  largest apparent slowdowns (FRI `Spec/SingleRound` 1.62×, `ToyProblem/ConstrainedCode`,
  `Sumcheck/Spec/General`) were not re-timed.
- **CI.** The PR's first CI build took 1.47× the module time of `main`'s nightly clean build on
  the 1230 modules both built. Modules the change cannot affect were slower by the same factor
  (`Cslib` 1.36×, `ToMathlib` 1.65×, `Extern` 1.29×), so the two runs were on runners of different
  speed, and that comparison does not measure the change. It is consistent with a change within
  about 10%.

## Consumer test: ArkLib

ArkLib was moved onto both changes as a downstream test, in two commits: the first moves its pins
to PolyFun and VCVio `main` without the change, the second takes the change. The second commit
touches 69 library files, 55 test files and the four runtime executables in `scripts/`.

| Class of edit | Hunks |
| --- | --- |
| Handler built with `where toFun …` instead of `fun … =>` | 216 |
| Raw function or draw wrapped as `⟨…⟩` where a handler is expected | 243 |
| `funext` or `congrFun` on handlers replaced by `ext` or `QueryImpl.congr_fun` | 28 |
| `@[simps]` added, an `_apply` lemma named, or `toHandler` | 27 |
| Other: type ascriptions, named arguments, one restructured proof | 25 |

Twenty-four ArkLib library handlers (two with `-isSimp`) and one test handler are tagged
`@[simps]`. None of the
roughly 270 `change`, `show` and `rfl` steps across handlers that a census flagged as at risk
broke. No theorem was weakened, and no `erw`, option or suppression was added.

## What the ports exposed

| File | Symptom | Cause | Fix |
| --- | --- | --- | --- |
| VCVio `QueryImpl/Basic.lean` | ArkLib proofs no longer simplified `liftTarget m impl` to `impl` | PolyFun's `Handler.liftTarget_self` is a simp lemma and used to apply to `QueryImpl`; VCVio's own `liftTarget` had no simp counterpart | `QueryImpl.liftTarget_self` is `@[simp]` |
| PolyFun `Lint/HandlerApply.lean` | Some handlers without application lemmas were not reported | An equation lemma derived by `rw [foo]` or `simp only [foo]` counted as an application lemma | Derived equation lemmas are excluded; the linter test has a control |
| VCVio `HashSig` cache replay, Merkle tests | `toHasQuery_query` stopped firing on local `HasQuery` instances | It matched a raw-function instance `⟨f⟩` by unifying `f` with a handler | The instance is `(replay cache).toHasQuery`; tests name `HasQuery.query` |
| VCVio `Computability` test | `initsweep` reported a handler constant | A parameterless handler is now a structure value, evaluated when its module loads | The test handler takes a `Unit` argument |
| VCVio `GeneralizedRelations` test | `gcongr with q` failed | A bundled handler is not a varying function for `gcongr` | `gcongr; intro q` |
| ArkLib `Fri/Spec/SingleRound.lean` | A heterogeneous equality of oracle interfaces failed | `congr 1` now stops at the handler's constructor | One more `congr 1` and the old proof for the field |
| ArkLib `Security/Agreement.lean`, `KnowledgeComposition.lean` | Rewrites of transported or combined draws failed | `⇑(e ▸ f)` is not syntactically `e ▸ ⇑f`, and `?d p` does not unify with `⇑(d p)` | The statement transports a handler; the draw argument is named |
| ArkLib `Interaction/Oracle/DerivedOracles` test | No coercion to a function | A handler stored as `(OracleBundle.ofSpec spec).Data` is not seen as a `QueryImpl` without unfolding | `QueryImpl.toFun` is written explicitly |
| VCVio BLS `Generic/Cache`, `Generic/ReductionCost`, `AGM/Reductions`; Fiat–Shamir `Stateful/Compatibility` | 1.27–1.84× slower | `simp [foo, …]` unfolded handlers that have application lemmas | The proofs name `foo_apply`, or drop `foo` where its lemma is already a simp lemma |
| ArkLib CI | The handler linters do not run | ArkLib imports VCVio modules, not its umbrella, and runs no environment linters | Recorded; with `VCVio.Lint.HandlerApply` imported, ArkLib reports nothing |

Challenge draws in ArkLib (`combineDraw`, `prefixDraw`, `suffixDraw`, `transportDraw`, `sampler`)
recurse and fold over raw functions, as `FreeM.liftM` does, and stay raw functions. They are
wrapped where a handler is expected.

## Edits in the three repositories

| Repository | Hunks | Mechanical | Other |
| --- | --- | --- | --- |
| PolyFun | 325 | 290 (89%), including 48 signatures respelled from function types to `Handler` | the `HAdd` instance, combinator names replacing raw lambdas, import lines |
| VCVio | 1503 | 1409 (94%) | ascriptions, `change` repairs, the cases above |
| ArkLib | 539 | 514 (95%) | ascriptions, named arguments, one restructured proof |

Counts are diff hunks classified by pattern, so they are approximate. VCVio tags 234 handlers with
`@[simps]`, 49 of them `-isSimp`.
