# Computational-complexity usability spike

Status: completed on `dtumad/complexity-usability-spike` and
`dtumad/quantitative-usability-spike`, audited 2026-08-24.

## Question and method

This spike measures how far the backend-relative complexity foundation is from ordinary use in
cryptographic developments. It deliberately separates two questions:

1. Can an application proof be expressed compositionally using only PolyFun and VCVio
   interfaces?
2. Can the pinned complexitylib backend discharge every operational obligation with an actual
   machine run?

A generic success does not erase a concrete-backend failure. Conversely, a dependency-port
failure is not counted as a defect in the interaction model. Each workload is classified as a
generic API result, concrete backend result, missing primitive, or unresolved composition theorem.

Complexitylib remains an optional leaf dependency. No generic declaration imports or exposes its
machine, `FP`, Cobham, or encoding definitions. The concrete package wraps those definitions
behind PolyFun realizers, while VCVio's predicates, contracts, polynomials, and interaction traces
remain independently defined and replaceable. The root isolation checker covers ordinary,
`public`, `meta`, and `import all` forms and rejects direct Lake requirements.

## Frozen revisions and compatibility result

The comparison baseline is VCVio commit `4d6149deeb3f4de05cdb4e13a2474f950553cab1`,
PolyFun commit `fd2005910652a67eb0b3a97e2e231fad1df207e0`, and complexitylib commit
`b6738219a3a3c50967d6bd16cba9487887ca6b66`. The completed VCVio spike pins PolyFun commit
`73a924e3160c3930da96f8fa8f3c7298c1b06520` from
`dtumad/quantitative-usability-spike`. Complexitylib is unchanged.

The exact complexitylib leaf substrate builds at Lean and Mathlib 4.33: the base deterministic
TM, `TM.reachesIn`, `TM.ComputesInTime`, the closed VCVio representation grammar, the pure and
one-query canaries, and the local exact-run output theorem. Kernel inspection of representative
public results reports only `propext`, `Classical.choice`, and `Quot.sound`.

The higher complexitylib stack does not build unchanged. The recorded failures are:

- `TuringMachine/Internal.lean` at lines 54 and 71;
- `TuringMachine/Combinators.lean` at lines 328 and 341;
- six `Norm.ext` or coercion proof failures in `Complexitylib/Asymptotics.lean`.

The TM failures block the published sequential composition, Hoare, subroutine, output-bound, and
full Cobham route. VCVio locally proves only the base-model output-length theorem needed by the
adapter; it does not edit the dependency checkout or assume any unavailable declaration.

Run `VCVioComplexity/scripts/compatibility-preflight.sh` to rebuild the supported leaf surface and
check that the source-located failures are exactly the recorded set. Passing
`--require-upstream-stack` makes the command fail while either upstream surface remains
unavailable. This strict mode is only an upstream compatibility probe: it does not inhabit
VCVio's closure gates, reconcile representations, or prove PolyFun composition.

## Implemented generic slice

PolyFun now owns the backend-independent control-flow machinery:

- `RankedRunCertificate` proves nonvacuous termination from a decreasing natural rank;
- bidirectional trace transport for input precomposition and result mapping;
- bounded input precomposition using the backend's certified composition-cost upper bound;
- `MapResultCostCertificate` and bounded result mapping with an explicit pathwise cost comparison.

VCVio adds the resource and cryptographic layer:

- `PureCertificate.ofPolyRealizer` and program-equality transport;
- `ResourcePotentialCertificate`, whose local inequalities mention the packaged realization's
  actual init, head, update, traffic, and observation costs;
- `RankedPPTCertificate`, which packages ranked local evidence into `IsOraclePPTBy` once one
  second-order polynomial has been supplied;
- exact semantic machines and certificate builders for two coins, adaptive one-or-two coins, and
  one fixed natural-input parity loop;
- semantic handler substitution for every contract-admitted answer path.

The two-coin, adaptive, and parity files are deliberately certificate-builder tests. They prove
control flow and expose the exact code and inequality obligations, but do not instantiate a
backend, a potential, or a resource polynomial. They are not end-to-end PPT witnesses.

## Concrete complexitylib slice

The optional `VCVioComplexity` package now provides:

- exact pure and one-coin machines and public `oneCoin_isPPTBy`;
- `Code.encodedSize_output_le_valueCost`, derived from the same exact `TM.reachesIn` run as work;
- `PolynomialCode.toPolyRealizerFromTime`, using that theorem instead of an asserted size meter;
- a regression proving VCVio's empty-pair word code differs from complexitylib's canonical pair
  code, so upstream pairing machines cannot be silently reused;
- a two-model second-order canary and guarded trust reports;
- an aggregate test script and a CI job for exact machines, trust scanning, and compatibility.

The second-order canary uses the same fixed two-bit coin answer under tight size `2` and slack size
`3` envelopes. It proves that one bound can quantify over and observe multiple admissible moduli;
it is not a genuine variable-response-size workload.

## Final acceptance matrix

“Control pass” means the syntactic machine, `Implements` theorem, and sound certificate interface
exist. “PPT pass” additionally requires executable backend code, instantiated cost proofs, and one
polynomial witness.

| Workload | Generic PolyFun/VCVio | Concrete complexitylib | Result |
|---|---|---|---|
| Public one coin | PPT pass | PPT pass | Exact machine is exposed through the canonical `OracleComp` facade |
| Pure fixed-width XOR | Pure constructor passes | blocked | No executable complexitylib XOR primitive |
| Two coins and adaptive coin | control/certificate-builder pass | blocked | No bounded `seqComp` theorem or concrete composed code |
| Uniform `n`-coin parity | uniform control/rank pass | blocked | One fixed machine has rank `n`; no loop compiler or instantiated polynomial witness |
| Variable-size oracle reply | second-order syntax passes | not demonstrated | The concrete two-model canary has a fixed-size answer |
| Certified handler substitution | semantic pass | blocked | No typed substitution machine, trace splice, or resource substitution theorem |
| Uniform one-time pad | blocked | blocked | Uniform sampler handler, width-uniform XOR, bounded loop, and handler closure are missing |
| ElGamal reduction | open syntax and query accounting pass | blocked | Primitive code and quantitative caller/handler composition remain missing |

## Measured usability

The operationally honest backend remains expensive:

| Artifact | Lines | What the count means |
|---|---:|---|
| Pure unit complexitylib canary | 232 | Explicit total tag machines and exact runs |
| Public one-coin complexitylib canary | 831 | Roughly 449 lines are transition/configuration/run plumbing |
| Generic ranked API | 194 | Reusable rank, potential, and strict-PPT packaging |
| Two/adaptive/parity regression | 594 | Hand-built semantic machines, simulations, ranks, and local certificate builders |
| Open ElGamal workload | 199 | Reused syntax and query accounting, without a PPT witness |
| Two-model modulus canary | 135 | Reuses the one-coin machine; tests quantification, not variable replies |

Ergonomics are scored from zero to three. The production threshold is at least two in every
dimension.

| Dimension | Score | Evidence |
|---|---:|---|
| Locality of primitive-code obligations | 2 | Pure and ElGamal interfaces isolate missing code, but concrete one coin remains large |
| Compositional reuse without direct trace induction | 1 | Ranked potentials help; bounded `seqComp` and handler substitution are absent |
| Clarity of failed proof diagnostics | 2 | Certificate fields and preflight failures identify exact missing laws |
| Reuse of probability syntax by complexity proofs | 3 | `Implements` targets the original `FreeM`; coin and ElGamal semantic bridges are exact |
| Backend replacement without client redesign | 3 | Generic APIs quantify over `Q`; import isolation and codec mismatch are tested |

The score is **11/15, not broadly usable**. The score of one for compositional reuse is decisive:
ordinary clients still have to construct or analyze composite machines directly.

## Exact blockers

### Bounded sequential composition

An honest `RunsWithinUnder.seqComp` needs a dependent decomposition of every composite trace.
A trace may stop in the left phase; after a left return, the right initial view is exposed without
a silent trace event; and the first right query transitions directly from a left-tagged state to a
right-tagged state. The theorem must compare the assembled head/update code with both phase traces,
including terminal observations and peak sizes. Its second-phase premise must be one uniform
realization and bound over every intermediate result, not pointwise machine choices.

### Handler substitution

Semantic leaf conformance composes, but PolyFun has no machine-level handler-substitution
constructor. A sound construction needs a typed phase state, a reachable-state invariant proving
that every packed returned tag matches the suspended outer position, an `Implements` theorem for
`FreeM.liftM`, caller/handler trace splicing, termination and progress preservation, and
second-order substitution for handler work, traffic, state, and output growth. A numeric handler
cost cannot replace this operational construction.

### One-time pad

The existing probability program samples `BitVec n` and applies XOR. A uniform PPT proof needs one
security-family realization, an efficient sampler that refines the uniform query to random bits,
a probability-agreement theorem, a width-uniform XOR realizer, a bounded fold or loop compiler,
and quantitative handler substitution. Constructing a separate fixed-width machine for each `n`
would be the nonuniform escape this design is intended to reject.

### ElGamal

The open three-query syntax and semantic closing theorem are sound. Completion additionally needs
representations and realizers for group addition, message selection, and bit equality; executable
dependent adversary-state wiring; a bounded three-phase realization; certified adversary and coin
handlers; and quantitative handler substitution. The unavailable complexitylib combinators and
pair-code mismatch prevent obtaining those facts by importing upstream structural code.

## Promotion decision

Promote as foundational APIs:

- PolyFun ranked termination/progress, bounded precomposition, trace transports, and explicit
  bounded result mapping;
- VCVio resource potentials, ranked PPT packaging, pure/program transport helpers, and semantic
  handler closing;
- the optional exact-run output theorem and time-to-output-bound adapter.

Keep as experiments or regression canaries:

- the hand-built two-coin, adaptive, parity, and concrete one-coin machines;
- the fixed-answer second-order canary;
- the uninhabited machine-closure gates, compatibility preflight, pair-code mismatch, and local
  attributed `PolyBound` port;
- PolyFun's synthetic zero-cost backend, which is explicitly only a structural elaboration test
  and contributes no computational-complexity evidence.

Do not export or claim general `IsPPT`, an `OracleTM` adequacy theorem, bounded bind, quantitative
handler closure, or genuine variable-answer complexity. Do not reuse complexitylib pairing
machines without a proved total translator or an explicit representation migration.

## Trust and validation gates

Every future positive application result must retain:

- executable Type-valued realizers for every host function;
- semantic implementation of the original `FreeM` or `OracleComp` program;
- costs for every contract-allowed path, including zero-probability paths;
- work, queries, traffic, peak state/head size, and output growth;
- one realization and one polynomial for a security family;
- total concrete behavior on malformed words;
- no `sorry`, custom axiom, `unsafe`, or native trust;
- no dependency from core PolyFun or VCVio to the optional backend.

The reproducible checks are:

```bash
lake build
lake build VCVioTest
./scripts/test-axiomsweep.sh
lake exe axiomsweep --check
bash scripts/test-complexity-backend-isolation.sh
bash scripts/check-complexity-backend-isolation.sh

cd VCVioComplexity
./scripts/test.sh
./scripts/compatibility-preflight.sh --require-upstream-stack  # expected to fail today
```

The optional package's `test.sh` builds its aggregate canaries, checks guarded axiom reports and
proof escapes, and verifies the exact known dependency diagnostics. The root CI runs the same
package independently, while the core build remains free of complexitylib.

## Scope boundary

This spike covers strict worst-case polynomial time for finite syntactic oracle interactions.
Expected-time rejection sampling, reactive/UC scheduling, and whole-oracle-machine adequacy remain
separate projects. The unqualified `IsPPT` name stays reserved until compilation preserves
results, complete oracle transcripts, coins, and polynomial overhead.
