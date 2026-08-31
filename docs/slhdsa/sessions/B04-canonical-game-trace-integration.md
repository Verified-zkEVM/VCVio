# B04 canonical-game and construction-trace visibility integration

Status: integration adaptation complete; independent review pending. No S07 or reduction is
claimed.

Date: 2026-08-31
Branch: `codex/sphincsplus-formalization`
Accepted predecessor: B03 review head `e6ad65272816dfe78e0f2f5e6a0dccf5f3032cd1`.

## History reconciliation

Exact shared head `c149dc23d2545aa4afab2705c7247af4608021ad` was merged normally with
`e6ad65272816dfe78e0f2f5e6a0dccf5f3032cd1` as first parent. Merge commit
`aca369d1050fdaa0f70389db94bb2d341eac6772` has tree
`c6b3bd84ec88abf543cdb52d815196bcafa2b906`. The sole conflict was the ordering of the same exact
seventeen `PolicyAudit` compiler-helper pairs; B04 retained the incoming order while preserving
every exact-parent, module-ownership, partial/safe-parent, extern, initializer, runtime-override,
axiom, and `sorryAx` check.

The remote removed two intentional Markdown hard-break spaces from the immutable S00 r5 review.
Commit `92a4c63ea920b80cd057b2b902f1125a1203973e` restores the exact predecessor blob
`aede719995060c1bf38659ffc74f44a821612678`; no historical review content changes.

## Imported surface and limits

The generic PR #594/#596 games are now present together with
`HashSig/SLHDSA/Security/CanonicalGames.lean` and
`HashSig/SLHDSA/Security/TraceTargets.lean`. `CanonicalGames` instantiates the generic
final-validity DSPR/TCR/PRE/UD-C and keyed-hash ITSR problem types at encoded SLH-DSA addresses,
formula-derived target caps, fixed primitive arities, and construction evaluation bridges.
`ReductionAdversaries` packages the types of ten future reductions and their advantage terms; no
inhabitant or reduction program is supplied.

`TraceTargets` collects the six structural construction-address ledgers after `adrsToKey`, proves
typed address membership, and pairs WOTS generation/sign/recovery provenance with their existing
query bounds. A deterministic logged interpreter preserves the pathwise address predicate. This
does not refine the outer CMA transcript, whose signing handler still records one atomic `.sign`
entry, and it supplies no FORS, XMSS, or hypertree program-level trace bridge.

The imported modules are therefore conditional infrastructure. Still open are the selected
proof's `CountingInterface`; an inhabitant of `ReductionAdversaries`; outer-CMA signing-log
refinement; FORS/XMSS/hypertree trace coverage and input pairing; concrete encoded injectivity and
distinct target batches; equivalences between the older architecture experiments and canonical
games; and the repaired master inequality, including the same-message SUF residual.

## Narrow policy and provenance adaptation

The source scanner's generic `run_` command rejection now applies only to unqualified command
tokens. Explicit dangerous leaves such as `run_cmd`, `addDecl`, initialization, registration, and
runtime-override surfaces remain rejected even when qualified. A positive canary admits qualified
proof identifiers such as `WriterT.run_bind'` and `Id.run_map`, while the existing `run_elab`
negative canary continues to reject the command escape.

The exact five-glob source recipe is unchanged and now produces a 45-line manifest with SHA-256
`6ae29b5b4d7c96fb8b6189d42a01c26391ee8c27a5875c450567c8825a65050c`. The declaration,
coverage, and obligation inventories register only the imported conditional surface and retain all
open reductions and conformance work explicitly.

## Validation

Focused validation covers both new security modules, the generic PR #594/#596 test modules, the
qualified-identifier policy canary, exact axiom footprints, aggregate `HashSig`/`HashSigTest` and
`VCVioTest` builds, the compiled `PolicyAudit`, deterministic harness/provenance checks, and the
authoritative wrapper. Exact command results are recorded in the implementation handoff; passing
them is not a reduction, conformance claim, or independent review.
