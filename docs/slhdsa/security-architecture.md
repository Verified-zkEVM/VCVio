# S02 classical security architecture

Status: r4 acceptance invalidated; independent r5/r6/r7 FAIL; successor-routing repair pending r8 review.

This document records the proposed shape of the classical SLH-DSA reduction before any component
proof is attempted. D-006 and D-009 remain proposed with no named approver, so this is a candidate
design rather than an accepted theorem/game selection. It is not a claim that the reduction has
been proved. Accepted S00/S01 infrastructure is unchanged, and the rejected placeholder in
`HashSig/SLHDSA/Security.lean` is not an authority for this design.

## Authority and repair boundary

The load-bearing source is `EUFCMA_SPHINCS_PLUS` in `proofs/SPHINCS_PLUS.ec:4338-4370`, pinned at
revision `a28e4c53897a4bb57b575a177225862d48f824b7`. CCS 2019 Theorem 17 is historical authority for
the PRF, PRFmsg, Hmsg/ITSR, and reconstructed FORS boundary. Its invalid WOTS reasoning is not
reused; the WOTS boundary is the repaired Hülsing-Kudinov/EasyCrypt UD-C, TCR-C, and PRE-C split.

The EasyCrypt development is classical. It has no quantum state, superposition-query semantics,
unitary oracle, or classical-to-QROM lift. Lean therefore exposes only `OracleComp` semantics;
`QROMClaim` is deliberately uninhabited.

## Exact master inequality

Under proposed D-006, the candidate RHS has exactly these twelve terms in source order:

1. SKG PRF advantage.
2. MKG PRFmsg advantage.
3. Hmsg ITSR probability.
4. `max(0, Pr[DSPR_F] - SPprob_F)`.
5. `3 * Pr[TCR_F]`.
6. FORS-H TCR-C.
7. FORS-Tl TCR-C.
8. `(w - 2) * Adv[WOTS-F UD-C]`.
9. WOTS-F TCR-C.
10. WOTS-F PRE-C.
11. WOTS-Tl TCR-C.
12. XMSS-H TCR-C.

`MasterTermRole` is a closed twelve-constructor type. SKG and MKG use VCVio `PRFScheme` real/ideal
experiments. The ITSR term runs a post-SKG/post-MKG reduction against the default fresh-key oracle.
Under proposed D-009, the other nine target-bearing terms are standalone source-shaped oracle
games, not events applied after an original-scheme transcript. This implemented candidate does not
supersede the earlier contract unless D-009 receives named approval.

There is no birthday/interleaving term and no additive `qS`/`qH` term. The rejected expression
`qS * (qS + qH) / 2^(8*m)` is not in the pinned theorem and is not probability-bounded for arbitrary
inputs: `m=1,qS=17,qH=0` gives `289/256 > 1`.

## Standalone target games

`TwoPhaseAdversary` models the source `pick`/`find`, `pick`/`guess`, and `pick`/`distinguish`
interfaces. Its `pick` phase can query the relevant game oracles and returns private state; its
`finish` phase receives the sampled public seed and that state but has no oracle access. The same
stateful program is run independently in the DSPR and SPprob experiments, and SPprob ignores only
the returned Boolean guess.

For TCR and DSPR, the target oracle accepts `(tweak,input)`, evaluates the role-specific primitive,
and logs the target. For PRE and real UD, each target query samples a fresh hidden `Y` input and
returns its F output. Ideal UD samples a fresh `Y` output. No real input or output is preloaded from
an earlier execution, and the program sees outputs only through its oracle.

Each `-C` program receives the sum of its target oracle and the collection oracle. Both are
interpreted with the same sampled public seed and logged during the same `pick` execution. The event
checks that actual target tweaks and actual collection tweaks are disjoint. It also checks the
formula-derived target-query bound and distinctness of the actual target trace. Invalid selection,
too many targets, duplicate tweaks, or overlap makes the event false; none makes the context
uninhabitable.

The collection language distinguishes F, H, FORS-Tl, and WOTS-Tl input types. `TargetInput`
separates all eight theorem roles, including fixed vectors of length `k` and `len` for the two Tl
roles.

## ITSR hybrid

`PostHopITSRAdversary` owns a `ProbComp` setup phase and its private state. That setup is the typed
boundary for the NPRF key material after both preceding PRF hops; the generic challenger does not
generate or inject a real SLH secret key. The state exposes only the public Hmsg parameters and the
reduction's oracle program.

The default ITSR oracle samples a fresh `Y` for each request and logs `(request,randomizer)`. The
challenger recomputes every Hmsg digest under the program-owned public parameters, then checks that
the returned `(randomizer,request)` is fresh and that its digest targets are contained in the union
of earlier targets. Message caching required by the concrete EUF-to-ITSR reduction belongs inside
that fixed reduction program, matching the source module boundary.

The original EUF transcript separately projects `(R,request)` from honest signing entries and
proves Hmsg coherence. That projection is useful for the scheme experiment but is not substituted
for the quantitative standalone ITSR game.

## Key, transcript, and query coupling

`SchemeInterface` is an arbitrary signature-scheme experiment boundary: it bundles a signature
carrier, randomizer projection, coherent key distribution, signing operation, and verification
operation, but supplies no law coupling those fields to each other or to the general SLH-DSA
construction. It removes the previous syntactic call to the known single-layer implementation; it
does not prove construction refinement. F-079 and PO-003 therefore remain open for S08/S09. A
generated pair packages public/secret seed and root equality. Original EUF execution queries are
indexed by that public key; `queryImpl` uses its seed/root. The public adversary language cannot
express PRF or PRFmsg.

`honestTranscriptDistribution` owns original key generation and uses `QueryImpl.withLogging`. It is
the LHS EUF probability space. Honest signing is currently one outer event; internal construction
instrumentation remains later implementation work. Crucially, no exact-target provider or
certificate is required from this opaque log, so a no-query adversary yields an ordinary empty log
rather than an impossible security context.

Freshness compares the complete request: mode, context, prehash identifier/output length, and
message. The forgery randomizer is the interface projection. Proving that projection is the exact
signature `R` consumed by general signing, digest, and verification remains part of F-079/PO-003.

`SigningBound` and `HashQueryBound` are `OracleComp.IsQueryBoundP` properties of the actual public
adversary program for every public key. `qH` counts explicit adversarial F, H, both Tl arities, and
Hmsg. These budgets are structural premises, not extra RHS loss.

## Formula-derived target bounds

Let `N_i = 2^(hp*(d-i-1))`, `C_X = sum_i N_i`, and
`C_W = sum_i N_i * 2^hp`. The game caps are:

| role | maximum target queries |
| --- | ---: |
| FORS F | `2^h * k * 2^a` |
| FORS H | `2^h * k * (2^a - 1)` |
| FORS Tl | `2^h` |
| WOTS F UD-C | `C_W * len` |
| WOTS F TCR-C | `C_W * len * w` |
| WOTS F PRE-C | `C_W * len` |
| WOTS Tl | `C_W` |
| XMSS H | `C_X * (2^hp - 1)` |

The FORS EasyCrypt variable named `d` is the number of FORS instances and maps to `2^h`, not
`Params.d`. `ParameterConditions` requires positivity, `h=hp*d`, and `lgw in {2,4,8}`.
`targetCount_pos` proves every cap positive. A game may make fewer target queries, including zero,
as in the source; selecting a nonexistent target simply fails its event.

## Quantifier order and non-claims

`ClassicalSecurityContext` fixes parameters, conditions, encoding, and the complete named reduction
system before `RepairedMasterStatement` quantifies over every adversary and its `qS/qH` witnesses.
The context has no target/transcript sampler, public seed, free target count, component probability,
or scalar loss field.

- `RepairedMasterStatement` is a proposition-valued definition, not a theorem.
- The context accepts any scheme-interface implementation; S02 neither reviews its construction
  refinement nor claims the current `d = 1` construction instantiates the general FIPS experiment.
- D-006 and D-009 remain proposed and unapproved. Their affected obligations remain pending.
- Constructing the authoritative concrete reductions and proving the inequality remain future work.
- Post-hop setup is a typed reduction boundary; proving the concrete NPRF setup correspondence is a
  later reduction obligation.
- Request encoding remains explicit until the external pure/prehash API is formalized.
- Honest signing internals remain uninstrumented; component games no longer depend on that absent
  trace refinement.
- No classical result is cast or advertised as QROM.
- The rejected legacy `Security.lean` remains untouched and its findings are not globally closed.

## Lean surface

- `Notions.lean`: requests, digest mapping, ITSR, target predicates, and classical/QROM boundary.
- `OracleSurface.lean`: generated-key provenance, public/internal queries, origin tags, and bounds.
- `Transcript.lean`: original honest experiment, logging, freshness, and scheme-transcript ITSR.
- `Architecture.lean`: roles/counts, target/collection oracle games, post-hop ITSR, twelve-term RHS,
  and master statement shape.
