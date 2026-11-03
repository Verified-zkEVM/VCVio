# Byte-activation evidence

The exact 214-line owner has one strengthened byte-comparison endpoint and one
independent terminal-key factorization. Its byte-alias contribution requires a
nonempty actual signing log; this is not a claim that every cached key guess
implies signing. The generic byte coupling stays unchanged. The second whole
proof block is byte-identical to the accepted basis. The 85-line PRIVATE NONMODULE
audit checks both endpoints and recovers the exact old first type by monotonicity.
There is no second public weak endpoint or duplicated coupling body.

This is UNGUARDED TOTAL-source research evidence. Raw log nonempty is not accepted
signing-counter positivity after guard fallback. No guarded-use/counter proof,
source/byte cost transport, final-abort Clash filter or full127 bound is established.
The final PR selects live code and needed concise docs/tests, not archive payloads
wholesale. The manifest pins accepted proof/review and external evidence maps.

Replay AFTER this exact four-file archive is committed. Record the ACTUAL CLEAN
research HEAD/tree, four Git blobs/content hashes and manifest hash BEFORE/AFTER;
require all identical. Require clean canonical b63, all12 actual clean dependency
HEADs matching locks, raw indices, pinned compiler and all SIX Std roots unchanged.
Validate all281 ordinary+META source/Git-blob pins and the canonical1405-artifact map
before EACH compile and afterward; include the normal UsesPMF artifact explicitly.
These are fresh execution-input pins. The older280-source packet lacked a historical
meta-artifact pin; its separate current addendum never retroactively supplies one.
Do not fetch, regenerate imports or write into either checkout or its dependencies.

Create fresh source/out/log directories. Copy both byte streams EXACTLY; keep the
private audit basename ImportAudit.lean when renaming its .txt storage. Only the
immutable canonical libraries and normal12 dependency libraries are needed.

```bash
set -euo pipefail
export GIT_OPTIONAL_LOCKS=0
research=/tmp/vcvio-slhdsa-security-delta
archive="$research/docs/design/slh-dsa-byte-activation-evidence"
canon=/tmp/vcvio-slhdsa-integration
lean_bin=/home/alh/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean
replay=$(mktemp -d /tmp/slhdsa-byte-activation-replay.XXXXXX)
mkdir "$replay/src" "$replay/out" "$replay/logs"
cp "$archive/ByteActivation.lean" "$replay/src/ByteActivation.lean"
cp "$archive/ImportAudit.lean.txt" "$replay/src/ImportAudit.lean"
export LEAN_PATH="$replay/out:$canon/.lake/build/lib/lean"
for dep in "$canon"/.lake/packages/*/.lake/build/lib/lean; do
  export LEAN_PATH="$LEAN_PATH:$dep"
done
cd "$replay/src"
"$lean_bin" -j2 -Dpp.unicode.fun=true -Dpp.proofs.withType=false \
  -DautoImplicit=false -DrelaxedAutoImplicit=false \
  -Dweak.linter.mathlibStandardSet=true -Dweak.linter.redundantVisibility=true \
  -Dweak.linter.style.longFile=1500 -Dexperimental.vcgen=true \
  -Dweak.linter.unicodeLinter=false -o "$replay/out/ByteActivation.olean" \
  ByteActivation.lean > "$replay/logs/ByteActivation.log" 2>&1
sha256sum "$replay/out/ByteActivation.olean" "$replay/out/ByteActivation.olean.private" \
  "$replay/out/ByteActivation.olean.server" "$replay/out/ByteActivation.ir" \
  "$replay/out/ByteActivation.ir.sig" > "$replay/body-before-audit.sha256"
"$lean_bin" -j2 -Dpp.unicode.fun=true -Dpp.proofs.withType=false \
  -DautoImplicit=false -DrelaxedAutoImplicit=false \
  -Dweak.linter.mathlibStandardSet=true -Dweak.linter.redundantVisibility=true \
  -Dweak.linter.style.longFile=1500 -Dexperimental.vcgen=true \
  -Dweak.linter.unicodeLinter=false -o "$replay/out/ImportAudit.olean" \
  ImportAudit.lean > "$replay/logs/ImportAudit.log" 2>&1
sha256sum --check "$replay/body-before-audit.sha256" \
  > "$replay/logs/body-artifact-check.log"
```

Record actual argv/cwd/LEAN_PATH, both exits (require0), source/Git-blob/log/new-output
joins and the FIVE new body artifacts observed BEFORE the audit starts. The private
nonmodule audit normally emits ONE olean; do not require five there. Require zero
warnings/admissions and all FIVE printed axiom roots within propext, Classical.choice,
Quot.sound. Keep proof limits at defaults; only an outer240s process watchdog is
permitted. Recheck every recorded input map/source/artifact and clean recorded HEAD
AFTERWARD, then obtain independent postreview. Earlier proof receipts are not this
future committed-head replay. No source/recipe changes are permitted during replay.
