# Joint signature-experiment cost observation

This reviewed generic research artifact stays outside the production import graph.
It establishes an observational identity, not an SLH-DSA resource bridge, signing
lifetime result, budget guard, positive-127 recovery or numerical bound improvement.

`selectedCost_run` retains the candidate, raw signing replies, verification result,
final cache and initial counter plus declared cost together in one equality.
It reuses the existing `SigningView.experiment` and `countedExperiment` with an
arbitrary lawful native handler. The theorem adds no sampler, equality, inhabitance,
budget or cryptographic hypothesis. Seven public definitions add deterministic
`Event → PUnit` bookkeeping alongside native queries, with no independent random
oracle or new signature runner. Attempts precede signer callbacks; ambient markers
precede cache answers. Actual replies and the supplied final verifier are preserved.

`SelectedWork.lean` is the exact accepted 233-line source. `ImportAudit.lean` is the
exact separate importing audit: `checkedTarget` closes the reviewed universally
quantified target using the imported theorem, rather than checking an open term.
The source and audit passed strict repository options at default proof limits and
`-j2`, with no warnings. Axiom roots are only `propext`, `Classical.choice` and
`Quot.sound`. Dependency/Std/compiler frames matched before and after both runs.
`manifest.json` pins all files, twelve dependency revisions and original receipts.

To replay, use Lean4.35.0 and already-built immutable libraries from canonical commit
`b63fede77cfcf9e23fda94c28e951e4520fdeb91`, with the manifest's exact dependencies.
Set the three installation-specific paths below, then run these Bash commands.
They create only a fresh external output directory; neither command invokes Lake.

Before and after replay, require clean actual research, canonical and all twelve
dependency worktrees, record the actual research HEAD, and require canonical HEAD
to equal `b63fede77cfcf9e23fda94c28e951e4520fdeb91`.
Record all twelve actual dependency revisions and both Lean source hashes at both
boundaries, requiring manifest matches and unchanged before/after records.
Acceptance requires both compiler commands to exit with status `0`.

```bash
VCVIO_CANON=/path/to/VCVio-at-b63
VCVIO_LEAN=/path/to/lean-v4.35.0/bin/lean
VCVIO_ARCHIVE=/path/to/this/archive
VCVIO_OUT=$(mktemp -d /tmp/slhdsa-selected-work-replay.XXXXXX)
export LEAN_PATH="$VCVIO_OUT:$VCVIO_CANON/.lake/build/lib/lean"
for VCVIO_DEP in "$VCVIO_CANON"/.lake/packages/*/.lake/build/lib/lean; do
  LEAN_PATH="$LEAN_PATH:$VCVIO_DEP"
done
VCVIO_FLAGS=(-j2 -Dpp.unicode.fun=true -Dpp.proofs.withType=false
  -DautoImplicit=false -DrelaxedAutoImplicit=false
  -Dweak.linter.mathlibStandardSet=true -Dweak.linter.redundantVisibility=true
  -Dweak.linter.style.longFile=1500 -Dexperimental.vcgen=true
  -Dweak.linter.unicodeLinter=false)
cd "$VCVIO_ARCHIVE"
"$VCVIO_LEAN" "${VCVIO_FLAGS[@]}" -o "$VCVIO_OUT/SelectedWork.olean" SelectedWork.lean
"$VCVIO_LEAN" "${VCVIO_FLAGS[@]}" -o "$VCVIO_OUT/ImportAudit.olean" ImportAudit.lean
```

The unicode option is the repository's documented setting; other standard checks
remain enabled. Inspect the audit's closed-target and axiom output. Original raw
logs, failed attempts and validation helpers remain outside this archive.

Remaining work includes actual wire/native source-cost transport, graph/fill
observation alignment and any same-measure cache/coverage assembly. Their acceptance
requires separate proofs and reviews; this archive does not settle those questions.
