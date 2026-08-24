# VCVioComplexity

`VCVioComplexity` is an optional, isolated Lake package for VCVio's first concrete
complexity-theory backend substrate. It is not imported by VCVio's root library and therefore
does not add complexitylib to ordinary VCVio consumers.

The current package provides:

- direct compatibility canaries for `Complexitylib.Models.TuringMachine` and
  `Complexitylib.Classes.P.Cobham.Defs` at VCVio's Lean/Mathlib 4.33 pin;
- a closed grammar of word, empty, unit, Boolean, unary-natural, fixed-width `BitVec`, product,
  dependent-pair, sum, and option representations, with proved codecs rather than
  caller-selected injective encodings;
- exact total-machine `Code` certificates based on complexitylib's `TM.reachesIn`, with a bridge
  to `TM.ComputesInTime`;
- exact run cost, a bundled `PolynomialCode` certificate, and an adapter from complexitylib's
  `TM.ComputesInTime`;
- inhabited PolyFun quantitative step classes for exact `Code` and polynomially certified
  `PolynomialCode`, without assuming machine-level categorical closure;
- `PolynomialCode.toPolyRealizer`, which translates its stored Mathlib polynomial into PolyFun's
  deterministic first-order syntax while requiring a separate proof of polynomial encoded-output
  growth;
- a complete `PureCanary`: concrete exact machines for unit initialization, the resolved-left sum
  tag, and the unreachable update; a VCVio `PureCertificate`; a nonvacuous empty-oracle contract;
  and the backend-relative theorem `unitIdentity_isOraclePPTBy`;
- an `OracleCanary` whose concrete initialization, readout, and enabled-update machines implement
  one fair-coin query, charge both Boolean answer branches and the dependent query/answer code,
  and prove `oneCoin_isOraclePPTBy`; and
- explicit `PolynomialClosureGate`, `QuantitativeClosure`, `ExactQuantitativeClosure`, and
  `StructuralClosure` requirement structures for the machine combinators that do not yet compile
  at this toolchain, with conditional adapters to PolyFun's category, exact-category, product,
  sum, option, and distributivity mixins.

The qualitative carrier deliberately admits every semantic function: all computational evidence
lives in the Type-valued realizers of the two quantitative step classes. Thus the carrier alone
makes no complexity claim, while every quantitative realizer still contains one concrete machine
and an exact run on every word.

The two canaries show that actual complexitylib run certificates can pass through PolyFun's
polynomial-realizer machinery and VCVio's strict pathwise definition. The first isolates the
certified-`pure` base case; the second exercises a real enabled oracle transition and every fair
coin reply. They are finite witnesses, not a general adequacy result.

The package does not currently provide a general `OracleTM` compiler, an inhabited general
category of complexitylib programs, a PolyFun-to-machine adequacy theorem, or an unqualified
`IsPPT` predicate. In particular, the generic VCVio predicates `IsOraclePPTBy` and `IsPPTBy`
remain backend-relative; importing this package does not turn them into conventional
machine-model PPT. The unqualified name is reserved until result, complete oracle transcript,
randomness, and polynomial cost preservation are all proved.

`PolynomialClosureGate` states the exact identity and sequential-composition obligations for the
direct base-TM route. The general gate is intentionally uninhabited: the pinned complexitylib
composition stack does not compile at VCVio's toolchain, and this package does not replace it with
an extensional Lean composition or a synthetic cost counter. The specialized unit machines do not
inhabit that universally quantified gate. Its adapter to PolyFun's optional category mixin does
compile, making the gate an executable acceptance test rather than only design prose.

See [PROVENANCE.md](PROVENANCE.md) for the exact upstream revision and compatibility result.
See the [computational-complexity design](../docs/design/computational-complexity.md) for the trust
boundary, landed API, literature assessment, and staged adequacy plan.

Development and PRs for this integration remain confined to VCVio and PolyFun. No compatibility
PR or issue is opened in complexitylib, CSLib, or Mathlib as part of this work.

Build the package independently from the repository root:

```bash
cd VCVioComplexity
lake exe cache get
lake build
```
