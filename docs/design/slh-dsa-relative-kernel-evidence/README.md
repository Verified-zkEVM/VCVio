# Relative deferred execution with arbitrary returned observations

`RelativeKernel.lean` constructs the relative handler and proves one averaged law
for every Type-0 result α, retaining the WHOLE α together with deferred graph state
and pending cells, declared Nat cost/phase and selected native cache. Every H_msg
and Rand call, including cache hits and foreign key/salt fields, goes through the
current native role. Other inputs reuse the existing deferred handler through the
private uniform port. A label touch only appends pending work, never draws it.

The proof synchronizes caches and folds the same marked program, then uses existing
IID tape averaging and passive-state projection. The full native RoleState remains
in the common run. Only the source-identification projection erases its passive
watch/tape bookkeeping. There is no fixed-tape equality to an ordinary oracle and
no full-watch ordinary alias. No new state, runner or semantic premise is added.

`DeriveAudit.lean.txt` is an exact PRIVATE non-module import consumer, stored as
text and copied to a fresh external Lean path for replay. Its fully quantified
statement recovers the complete original DeriveOutcome result by specializing the
same public law. Clients needing the actual generated public key must retain it
in α (for example, DeriveOutcome × extraObservation); Bool recovers no erased key.

This is research evidence, not a production API migration or a LOC reduction:
503 kernel lines and 51 audit lines. It proves no actual source phase/GoodQuery or
resource-policy discipline, SLH experiment bridge, endfill, adaptive occupation/AE
charge, seed-cap payment, verification discount or full127 theorem. The original
Derive-specific proof is history only; its duplicate body is not archived here.

## Replay

Use the immutable b63 proof checkout and the accepted SelectedWork artifact named
in the manifest. This recipe writes ONLY a fresh external directory. Before and
after replay, require CLEAN Git status (including untracked files) for research and
artifact checkouts, record research HEAD/tree/semantic index/source Git blobs,
canonical b63 HEAD/tree/index, source hashes, manifest SHA and all twelve actual
clean dependency HEADs matching the manifest locks. Compare these frames exactly.
Set GIT_OPTIONAL_LOCKS=0 for every Git read. No canonical source/cache writes.

```sh
set -eu
export GIT_OPTIONAL_LOCKS=0 LEAN_NUM_THREADS=4
artifact=/tmp/vcvio-slhdsa-integration
research=/tmp/vcvio-slhdsa-security-delta
event_out=/tmp/slhdsa-selected-work-archive-validation-20261102-01/out
evidence="$research/docs/design/slh-dsa-relative-kernel-evidence"
run=$(mktemp -d /tmp/slhdsa-relative-kernel-replay.XXXXXX)
mkdir "$run/src" "$run/out"
cp "$evidence/RelativeKernel.lean" "$run/src/RelativeKernel.lean"
cp "$evidence/DeriveAudit.lean.txt" "$run/src/DeriveAudit.lean"
export LEAN_PATH="$run/out:$event_out:$artifact/.lake/build/lib/lean"
for package in "$artifact"/.lake/packages/*
do
  LEAN_PATH="$LEAN_PATH:$package/.lake/build/lib/lean"
done
export LEAN_PATH
cd "$research"
lean --version
lean -j4 -DautoImplicit=false -DrelaxedAutoImplicit=false \
  -Dweak.linter.mathlibStandardSet=true -Dweak.linter.redundantVisibility=true \
  --root="$run/src" -o "$run/out/RelativeKernel.olean" \
  "$run/src/RelativeKernel.lean" > "$run/RelativeKernel.log" 2>&1
lean -j4 -DautoImplicit=false -DrelaxedAutoImplicit=false \
  -Dweak.linter.mathlibStandardSet=true -Dweak.linter.redundantVisibility=true \
  --root="$run/src" -o "$run/out/DeriveAudit.olean" \
  "$run/src/DeriveAudit.lean" > "$run/DeriveAudit.log" 2>&1
```

Require Lean 4.35, default proof limits, both actual exits zero and no warnings.
Record source/Git-blob/log/output joins. The 20 kernel and one private audit axiom
records must be subsets of propext, Classical.choice and Quot.sound. Source copies
must be byte-exact, including the renamed audit copy; inherited SelectedWork source
17b16a69 and its accepted output artifacts must be pinned unchanged before/after.
