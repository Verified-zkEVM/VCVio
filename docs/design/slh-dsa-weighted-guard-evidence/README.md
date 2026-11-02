# Weighted-query guard evidence

These are exact accepted external proof/audit sources, archived for research only.
One Monad-parametric guard forwards every accepted query, including event markers.
Its ProbComp laws certify all-path caps from zero/unaborted and the mixed-source joint
law under an actual source AE cap. One further law interprets the free guarded
program under arbitrary lawful m, retaining output/cache/counters/flag jointly.
Its tuple permutation erases only PUnit, at every initial cache/count pair/flag.
No old observation guard is bundled.

The interpretation uses
`OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT` and the existing
state-projection law. The historical interpretation packet's first dependency
namespace is a provenance typo; its frozen source/proof/receipt is unchanged.
Manifest pins the accepted packets/reviews and exact bytes. The constructor has
no axioms; cap and interpretation use propext/Quot.sound; AE also uses choice.

Replay only after the six-file archive is committed. Require a CLEAN recorded
research HEAD before and after; record its actual commit and all six Git blob and
content hashes. Verify manifest hashes, clean canonical b63fede77cfcf9e23fda94c28e951e4520fdeb91,
and all12 actual clean dependency HEADs against canonical lake-manifest.json both
BEFORE and AFTER. Also capture source/index, compiler and six Std-root hashes;
all these inputs and the recorded research HEAD must remain identical throughout.
Do not regenerate imports, fetch caches or write into either checkout/dependency.

Create fresh source/output/log directories. Copy the FOUR exact source byte
streams below; the two audit .txt files are copied/renamed, never edited. Canonical
b63 and its normal twelve built dependencies suffice: no SelectedWork,
RelativeKernel, old guard, failed logs or external proof output is needed.

```bash
set -euo pipefail
export GIT_OPTIONAL_LOCKS=0
research=/tmp/vcvio-slhdsa-security-delta
archive="$research/docs/design/slh-dsa-weighted-guard-evidence"
canon=/tmp/vcvio-slhdsa-integration
lean_bin=/home/alh/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean
replay=$(mktemp -d /tmp/slhdsa-weighted-guard-replay.XXXXXX)
mkdir "$replay/src" "$replay/out" "$replay/logs"
cp "$archive/ForwardingBudgetGuard.lean" "$replay/src/ForwardingBudgetGuard.lean"
cp "$archive/FreeGuardInterpretation.lean" "$replay/src/FreeGuardInterpretation.lean"
cp "$archive/GuardAudit.lean.txt" "$replay/src/GuardAudit.lean"
cp "$archive/InterpretationAudit.lean.txt" "$replay/src/InterpretationAudit.lean"
export LEAN_PATH="$replay/out:$canon/.lake/build/lib/lean"
for dep in "$canon"/.lake/packages/*/.lake/build/lib/lean; do
  export LEAN_PATH="$LEAN_PATH:$dep"
done
cd "$replay/src"
for mod in ForwardingBudgetGuard FreeGuardInterpretation GuardAudit InterpretationAudit; do
  "$lean_bin" -j2 -Dpp.unicode.fun=true -Dpp.proofs.withType=false \
    -DautoImplicit=false -DrelaxedAutoImplicit=false \
    -Dweak.linter.mathlibStandardSet=true -Dweak.linter.redundantVisibility=true \
    -Dweak.linter.style.longFile=1500 -Dexperimental.vcgen=true \
    -Dweak.linter.unicodeLinter=false -o "$replay/out/$mod.olean" "$mod.lean" \
    > "$replay/logs/$mod.log" 2>&1 || exit "$?"
done
```

Record actual argv/cwd/LEAN_PATH and all FOUR compiler exit codes (require 0), zero
warnings/admissions, standard axiom reports, source-to-Git-blob/log/new-output joins,
and each later module's exact earlier output input hashes at execution. Keep
Lean proof limits at defaults; an outer240s per-process watchdog is permitted.
Fresh four-module acceptance needs independent review; original receipts are not
that future replay. This package proves no SLH instantiation, cap/source-policy
transport, unique counter ownership, filling, seed accounting or final127 bound.
