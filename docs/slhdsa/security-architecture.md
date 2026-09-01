# Classical security architecture

This document describes the implemented game boundary and its missing proof obligations. It does
not claim a completed security theorem.

## Authority and semantics

The repaired EasyCrypt development at revision
`a28e4c53897a4bb57b575a177225862d48f824b7` is the load-bearing classical proof source. CCS 2019
is historical comparison authority; its invalid WOTS reasoning is not reused. The Lean model uses
classical `OracleComp`/`ProbComp` semantics. It contains no quantum state, superposition queries,
unitary oracle, or classical-to-QROM lifting.

## Candidate master expression

The modeled source order has twelve terms:

1. secret-key-generation PRF advantage;
2. message-randomization PRF advantage;
3. Hmsg ITSR probability;
4. `max(0, Pr[DSPR_F] - SPprob_F)`;
5. `3 * Pr[TCR_F]`;
6. FORS-H TCR-C;
7. FORS-Tl TCR-C;
8. `(w - 2) * Adv[WOTS-F UD-C]`;
9. WOTS-F TCR-C;
10. WOTS-F PRE-C;
11. WOTS-Tl TCR-C;
12. XMSS-H TCR-C.

`MasterTermRole` closes this list. `RepairedMasterStatement` fixes parameters, encodings, and a
complete `ReductionSystem` before quantifying over adversaries and their query-bound witnesses. It
is a `Prop` definition: no concrete reduction system or proof of the inequality is supplied.

## Target and collection games

Two-phase programs query challenger-owned target oracles during `pick` and return private state to a
non-querying finish phase. TCR and DSPR target queries log `(tweak,input)`; real PRE/UD queries
sample hidden inputs and expose only primitive outputs, while ideal UD samples outputs. Collection
variants interpret target and collection oracles under the same public seed and execution and test
distinct target tweaks plus target/collection disjointness. Invalid selection, excessive or
duplicate targets, or overlap makes the event false.

Formula-derived target counts are positive upper bounds. An execution may make fewer or zero target
queries; selecting a nonexistent target fails rather than making the context inconsistent.

## ITSR and outer transcript

The post-hop ITSR setup owns reduction state after the two PRF hops. Each oracle request samples a
fresh randomizer and records the Hmsg request; the final event checks freshness and target reuse.
The original CMA transcript separately records honest signing requests and projects their Hmsg
inputs. A proof connecting these structures to a concrete general-scheme reduction is still needed.

Generated key records preserve public/secret seed and root coherence, and public queries are indexed
by that key. `SigningBound` and `HashQueryBound` are predicates on the actual adversary program.
`qH` covers explicit F, H, both Tl arities, and Hmsg calls. Internal construction instrumentation
and the outer atomic signing-log refinement remain open.

## Construction connections

`CanonicalGames` instantiates the canonical generic problem types with encoded addresses and types
the required reduction fields. `ReachableTargets` provides structural FORS/XMSS/WOTS ledgers with
cardinality and `Nodup` facts. `TraceTargets` proves WOTS free-oracle programs stay inside their
structural address union and transfers that certificate to deterministic public-hash logs.

Still required are concrete encoded injectivity, nonempty distinct-target batches, input pairing,
FORS/XMSS/hypertree trace bridges, outer-CMA log refinement, experiment equivalences, an inhabitant
of `ReductionAdversaries`, the selected `CountingInterface`, and the master inequality. The exact
SUF partition also leaves its same-message residual unbounded.

## Exact target caps

Let `N_i = 2^(hp*(d-i-1))`, `C_X = sum_i N_i`, and
`C_W = sum_i N_i * 2^hp`.

| Role | Upper bound |
|---|---:|
| FORS F | `2^h * k * 2^a` |
| FORS H | `2^h * k * (2^a - 1)` |
| FORS Tl | `2^h` |
| WOTS F UD-C | `C_W * len` |
| WOTS F TCR-C | `C_W * len * w` |
| WOTS F PRE-C | `C_W * len` |
| WOTS Tl | `C_W` |
| XMSS H | `C_X * (2^hp - 1)` |

The FORS proof variable called `d` denotes a number of FORS instances and maps to `2^h`; it is not
`Params.d`. `ParameterConditions` enforces positivity, `h = hp*d`, and `lgw ∈ {2,4,8}`.
