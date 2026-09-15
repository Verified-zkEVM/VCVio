# VCVioComplexity

`VCVioComplexity` is an optional, isolated Lake package for VCVio's first concrete
complexity-theory backend substrate. It is not imported by VCVio's root library and therefore
does not add complexitylib to ordinary VCVio consumers.

This preservation draft uses the Lean 4.34.0-rc2 dependency set described in the
[UC checkpoint](../docs/design/uc-rc2-checkpoint.md). The production compatibility preflight
and `PROVENANCE.md` still describe the 4.33 baseline and must be updated before adoption.
The build and kernel trust checks passed in the isolated candidate; the full adoption gates
remain open.

The current package provides:

- direct compatibility canaries for `Complexitylib.Models.TuringMachine` and
  `Complexitylib.Classes.P.Cobham.Defs` on the candidate Lean/Mathlib dependency set;
- a closed grammar of word, empty, unit, Boolean, unary-natural, fixed-width `BitVec`, product,
  dependent-pair, sum, and option representations, with proved codecs rather than
  caller-selected injective encodings;
- exact total-machine `Code` certificates based on complexitylib's `TM.reachesIn`, with a bridge
  to `TM.ComputesInTime`;
- exact run cost, a bundled `PolynomialCode` certificate, and an adapter from complexitylib's
  `TM.ComputesInTime`;
- an output-length theorem derived directly from each exact `TM.reachesIn` run, showing that every
  emitted bit consumes at least one concrete transition;
- inhabited PolyFun quantitative step classes for exact `Code` and polynomially certified
  `PolynomialCode`, without assuming machine-level categorical closure;
- `PolynomialCode.toPolyRealizer`, for callers with a sharp encoded-output bound, and
  `PolynomialCode.toPolyRealizerFromTime`, which honestly uses the concrete time polynomial as an
  output-size bound;
- a complete `PureCanary`: concrete exact machines for unit initialization, the resolved-left sum
  tag, and the unreachable update; a VCVio `PureCertificate`; a nonvacuous empty-oracle contract;
  and the backend-relative theorem `unitIdentity_isOraclePPTBy`;
- an `OracleCanary` whose concrete initialization, readout, and enabled-update machines implement
  one fair-coin query, charge both Boolean answer branches and the dependent query/answer code,
  and prove both the free-monad theorem `oneCoin_isOraclePPTBy` and the public `OracleComp`
  facade `oneCoin_isPPTBy`;
- exact linear copying, left-sum injection and optional-value injection for arbitrary trusted
  representations, with respective transition counts `n + 2`, `n + 3`, and `n + 3`;
- a variable-input `HandlerCanary` which executes an inhabited echo interface through two
  administrative transitions and realizes the resulting optional word with actual copying
  machines; its derived bound is `2n + 7` work, `n + 1` state size and `n + 2` readout size;
- a `VCVioComplexityTest` aggregate containing public-facade checks, guarded kernel trust reports,
  compiling upstream capability probes, an executable regression for the pair-codec mismatch,
  and one fixed-answer second-order witness checked against two distinct response-size models;
- PolyFun's category, exact-category, product, sum, option, and distributivity mixins as the single
  interface for machine combinators whose adapter witnesses remain to be implemented; the adapter does
  not duplicate those requirements in VCVio-specific wrapper structures.

The qualitative carrier deliberately admits every semantic function: all computational evidence
lives in the Type-valued realizers of the two quantitative step classes. Thus the carrier alone
makes no complexity claim, while every quantitative realizer still contains one concrete machine
and an exact run on every word.

The canaries show that actual complexitylib run certificates can pass through PolyFun's
polynomial-realizer machinery and VCVio's strict pathwise definition. The first isolates the
certified-`pure` base case; the second exercises a real enabled oracle transition and every fair
coin reply. The handler canary covers arbitrary-length binary inputs and checks that one
transition leaves the handler's return pending. It specializes the echo program; compilation of
the general dispatcher remains a separate obligation.

The package does not currently provide a general `OracleTM` compiler, an inhabited general
category of complexitylib programs, a PolyFun-to-machine adequacy theorem, or an unqualified
`IsPPT` predicate. In particular, the generic VCVio predicates `IsOraclePPTBy` and `IsPPTBy`
remain backend-relative; importing this package does not turn them into conventional
machine-model PPT. The unqualified name is reserved until result, complete oracle transcript,
randomness, and polynomial cost preservation are all proved.

General categorical closure remains uninhabited: the candidate complexitylib composition stack
compiles, but the representation translation and PolyFun closure witnesses have not been
implemented. Any future implementation must provide
PolyFun's `QuantitativeStepClass.HasCategory` mixin directly; the specialized unit machines do not
establish that universally quantified interface.

The representation grammar's pairing codec is intentionally unchanged by this spike. It encodes
the empty pair as `[true]`, whereas complexitylib's canonical pairing used by its split and emit
machines encodes it as `[false, true]`. Reusing those machines therefore requires a proved total
translation or a deliberate representation migration; definitional compatibility must not be
assumed.

See [PROVENANCE.md](PROVENANCE.md) for the exact upstream revision and compatibility result.
See the [computational-complexity design](../docs/design/computational-complexity.md) for the trust
boundary, landed API, literature assessment, and staged adequacy plan.

Development and PRs for this integration remain confined to VCVio and PolyFun. No compatibility
PR or issue is opened in complexitylib, CSLib, or Mathlib as part of this work.

Build the package independently from the repository root:

```bash
lake update PolyFun
cd VCVioComplexity
lake exe cache get
lake build
lake build VCVioComplexityTest
./scripts/test.sh
```

`./scripts/compatibility-preflight.sh` checks the pinned revision, builds the supported base API,
and classifies both the upstream composition stack and `Complexitylib.Asymptotics`. By default,
recorded compatibility blockers are reported without failing the spike; changed or unexpected
source diagnostics fail. Pass `--require-upstream-stack` to fail while either upstream surface
remains unavailable. This is a compatibility gate, not proof of VCVio closure: the representation
translation and PolyFun closure witnesses remain separate obligations. The script never patches
dependency sources.
