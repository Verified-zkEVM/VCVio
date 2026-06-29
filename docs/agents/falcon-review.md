# Falcon Faithfulness & Soundness Remediation — Working Doc

Canonical state for the `falcon-faithfulness-review` branch. **This file is the bootstrap: a fresh
session must resume from it alone, without chat history.** Paired with the re-runnable adversarial-review
harness [`scripts/falcon_review.mjs`](../../scripts/falcon_review.mjs).

Scope: `LatticeCrypto/Falcon/**` (+ load-bearing `VCVio/CryptoFoundations/GPVHashAndSign.lean`).
Three baselines, judged separately (no single authoritative spec):
**Falcon v1.2** (round-3 PDF; `r‖m` hash, salt-once, L2-only) ·
**FN-DSA / FIPS 206** (pk-bound domain-separated hash, fresh-salt-per-retry, L2 **and** L∞, leaf-range gate,
79-bit base sampler — IPD not public, `csrc.nist.gov/pubs/fips/206/ipd` → 404) ·
**Falcon+ / c-fn-dsa** (Pornin reference @ `33026d4d`; tracks FN-DSA but 72-bit sampler + L2-only).
The repo **targets c-fn-dsa / FN-DSA** (FFI uses `FNDSA_HASH_ID_RAW`); divergences from v1.2 are intended.

---

## 0. Session protocol (bootstrapped, self-contained)

Every session **starts and ends** with a fresh adversarial review + doc refresh. Do not trust this doc
blindly — the protocol re-validates it.

**START** — (1) `git status`: expect branch `falcon-faithfulness-review` (verify with **live** `git`, not the
session's initial reminder — a subagent once misreported `main`). (2) Drift check (§6); compare to Baseline
(§4); reconcile §3/§4 on any mismatch. (3) Adversarial review scoped to the area you'll touch:
`Workflow scriptPath=scripts/falcon_review.mjs args={"dimensions":["…"],"full":false}` — for a hard proof,
have it validate the *proof plan* first. (4) Pick the next §2 item; restate the plan.

**END** — (1) re-run drift check, update §4. (2) Adversarial review of what changed (`args.changed="…"`),
hunting regressions. (3) Refresh this doc (§2 status, §3 findings, append a terse §5 log line). (4) Update
the `falcon-review-status` memory + Artifact if material. (5) **Commit** (doc reflects HEAD).

> Cost: full 9-dim + adversarial sweep ≈ 18–21 agents. Use `full:false` + a `dimensions` subset for routine
> bookends; reserve the full sweep (and `full:true` to re-fetch sources) for milestones. **Validate the
> validator:** subagents have misreported facts (a `main` branch, a 21-sorry count, an `ofInt` mis-sign) —
> re-check load-bearing claims against live source.

---

## 1. Status summary (milestone-verified @ `f405e7c2`, sessions 0–5)
- **Faithful?** v1.2: **no, by design** (FN-DSA target: pk-bound hash, fresh salt). FN-DSA: **partial**
  (omits L∞, leaf-range gate, 79-bit sampler). **c-fn-dsa: yes** at the concrete/constant level — the
  pk-bound hash path is cross-validated by the FFI differential tests.
- **Complete?** No — **19 live Falcon sorries** (+4 GPV +1 ToMathlib). `sign` done (s4); `keyGenFromSeed` +
  NTRUSolve ascent + the security/correctness proofs remain.
- **Sound?** No — 0/4 security theorems proven; `euf_cma_security`/`verify_sign_correct` are `sorry`; the
  generic GPV chain is `sorry`. **But** the pieces built (B1, TS-5, `falconPSF_eval_trapdoorSample`, `sign`,
  B9, **B6 kernel equalities**) were re-audited sound at HEAD (could not refute); B6's two kernel-equality
  theorems are standard-axioms-only.
- **Verify bridge:** `concrete_verify_eq_verify` is proven with **NO semantic hyps** (was 4, then 3): the
  U32-kernel equalities (B6) and **both codec round-trips** (`hsigDecode`/`hpkDecode`, s8/s9) are now
  discharged inline. Remaining hyps are purely structural/numeric: `hn`, `hsbytelen`, `hn_ovf`, `hn4 : 4∣p.n`.
  The byte-level verifier provably equals the spec verifier (VER-1 closed). Standard-axioms-only.
- **One genuine wire bug:** B9/ENC-3 over-length signature malleability (not just an intended divergence).
- Original enquiry ("hash to sign is a sorry") — **RESOLVED** (s4).

## 2. Critical path (status)
- [x] **B8** (s1) — vacuous `hashToPoint_welldefined` removed; `verify_sign_correct`/`euf_cma_security` ⚠-marked.
- [x] **B1** (s1) — `FalconTree.leaf` carries `(σ₀,σ₁,l01)`; `ffSampling` κ=0 mirrors `ffsampFFTDeepest`. SD-5 closed.
- [x] **TS-5** (s2) — `fromFFTPreimage` recomputes `s₁:=c−s₂·h`; `falconPSF_eval_trapdoorSample` proven.
- [x] **B2 `sign`** (s4) — fuel-bounded `Option` rejection loop (`Scheme.lean:262`) + `rqToIntPolyCentered`.
- [ ] **B2′ `verify_sign_correct`** (next, agreed) — prove it. Prereqs: `toRq_rqToIntPolyCentered = id`
  (F8 — coeff-wise + `ofFn`/`toArray` index bridge, see `SchoolbookCert.lean:213` + `centeredRepr_intCast`
  `Norms.lean:112`); induct on `maxAttempts`; stays conditional on the `h_laws` `compress_decompress` (ENC-1).
- [ ] **KG-quickwin** — delete `NTRUSolver`'s local sorry-stub shadows (`FXR.sqr`, `vect_*`,
  `poly_big_to_small`) and use the real `Concrete/FXR.lean` + `PolyBigInt.lean` (already fully implemented).
  Cuts ~8 of 11 NTRUSolver sorries. **CAVEAT (s9 re-check): NOT a clean drop-in** — the real signatures
  differ from the stubs (`poly_big_to_small` is 3-arg vs the stub's 4-arg `_off`; `vect_set` takes
  `Array Int32` vs the stub's `Array Int8`), so call sites need reconciliation. Medium effort, not "no new proofs."
- [x] **B9 / ENC-3** — DONE (s6): `decompress` now rejects `d.length ≠ dlen` (was `< dlen`)
  (`Concrete/Encoding.lean:79`), so over-length/trailing-garbage sigs are refused (the verify path
  `verify → decompress … p.sbytelen` rejects any `comp.length ≠ sbytelen`). Enforces fixed-length
  (NIST/c-fn-dsa) framing; the spec's *optional* unpadded (variable-length) verification remains
  unsupported (it never was — the old `< dlen` already rejected unpadded). Repaired the dependent
  `concrete_verify_eq_verify` nil-branch (`FPRBridge.lean:141`).
- [ ] **ENC-2** — repair/delete the orphan `Falcon.Encoding`/`Laws` (`sigDecode_sigEncode` false for the
  concrete codec). Unsound-as-stated.
- [x] **B6** (s7) — kernel equalities PROVEN (standard-axioms-only): `negacyclicMulU32_eq_negacyclicMul`
  (unconditional, `Instance.lean:447`) + `pairL2NormSqU32_eq_pairL2NormSq` (under UInt64 no-overflow
  `hn : 2*n*(modulus/2)^2 < 2^64`, `Instance.lean:645`). `concrete_verify_eq_verify` reduced **4→3 hyps**
  (`FPRBridge.lean:121`): kernel-equality assumptions removed; remaining = 2 codec round-trips
  (`hsigDecode`/`hpkDecode`) + 1 numeric `hn_ovf`. **NOT** fully unconditional — the ∀n norm equality is
  false by UInt64 overflow at n≈2.4e11; `hn_ovf` holds with vast headroom for n∈{512,1024}
  (2·1024·6144² ≈ 7.7e10 ≪ 2⁶⁴). ~19 private helpers; forIn→foldl bridge + Array.set! invariant
  (technique cribbed, not imported, from `~/CompPoly` NTTFast).
- [ ] **TS-4 two-world bridge** — `Falcon.verify` (byte-level) ↔ the GPV/`falconPSF` verify `euf_cma` targets.
- [ ] **B4** — finish NTRUSolve ascent (`solve_NTRU_intermediate`/`depth0`) + prove `solve_NTRU ⊨ ntruEquation`
  (KG-2/KG-3) → real **`keyGenFromSeed`** (deferred here, KG-1; degenerate stub rejected as dishonest).
- [ ] **B3** — `euf_cma_security`: discharge the generic GPV chain (`reduction`, `programmedPreimageReduction`,
  `forgery_yields_collision[_or_exact_match]`) + supply `Correct (falconPSF)` (eval-half done; isShort-half
  via the rejection loop) + reinterpret collision branch as `ntruPSFCollisionProblem`.
- [ ] **B5** — make `samplerZ_correct` satisfiable (ideal sampler + `SamplerQuality` Rényi); FPR error bounds (SZ-3).
- [ ] **B7** — FN-DSA acceptance-region decision (L∞, leaf-range, 79-bit) — parameterize over optional L∞;
  default target c-fn-dsa; re-check IPD at milestones (still 404).

## 3. Findings (current; full history in git + the Artifact §7)
**Resolved & re-verified sound (s1–s7):** B8, B1/SD-5, TS-5, `falconPSF_eval_trapdoorSample`, B2 `sign`,
B9/ENC-3, **B6** kernel equalities (`negacyclicMulU32_eq_negacyclicMul`/`pairL2NormSqU32_eq_pairL2NormSq`,
standard-axioms-only; END review re-verified the RHS chains target the genuine spec, not a weakened form).

**Spec-divergence — intended (vs v1.2; faithful to FN-DSA/c-fn-dsa):**
- SD-1/M1 pk-bound hash `salt‖SHAKE256(pk)[0:64]‖0x00 0x00‖msg` (`Sampling.lean:39–43`; FFI-cross-validated).
- SD-1/M2,M8 fresh-salt-per-retry single loop (`Scheme.lean:262–274`; `Concrete/Sign.lean:230–244`).
- SD-2/M3 L2-only, no L∞ (`Scheme.lean:283–290`; `Instance.lean:98–99`). SD-3/M4 no leaf-range gate. SD-4/M5 72-bit sampler.

**Spec-divergence — REAL BUG (RESOLVED s6):**
- ~~**B9/ENC-3** over-length signature malleability~~ **FIXED s6**: `decompress` now rejects `d.length ≠ dlen`
  (`Concrete/Encoding.lean:79`), refusing trailing-garbage sigs on the verify path. (Internal unique-encoding
  checks were already faithful; this closes the unbounded-tail gap.)

**Unsound-as-stated:**
- UN-2 `euf_cma_security` — `sorry` + discards all hyps (`let _ :=`) + free `samplerLoss` trivially satisfiable (`Security.lean:302–333`).
- UN-3 generic GPV chain `sorry` (`GPVHashAndSign.lean:270,283,332,363`); `euf_cma_split_bound` is `exact ⟨…sorry…⟩`.
- ENC-2 orphan `Falcon.Encoding`/`Laws`; `sigDecode_sigEncode` false for the concrete codec.

**Incompleteness (unfinished, statement sound-in-shape):**
- UN-1/TS-B `verify_sign_correct` `sorry` (non-vacuous now). **Two-world gap (TS-4):** byte-level
  `Falcon.verify` ≠ GPV verify; no bridge lemma.
- ENC-1 `compress_decompress` only ever the assumed `h_laws` — no `Primitives.Laws (concretePrimitives)` instance.
- F8/ENC-7 `toRq_rqToIntPolyCentered = id` not yet a lemma (needs the index bridge).
- VER-1 (B6 done s7; codecs done s8/s9): **CLOSED** — `concrete_verify_eq_verify` has NO semantic hyps.
  - `hsigDecode` (sig framing round-trip): **PROVEN s8** (`Concrete/Encoding.lean` `sigDecode_sigEncode`,
    standard-axioms-only).
  - `hpkDecode` (14-bit pk pack/unpack round-trip): **PROVEN s9** — `pkDecode_pkEncode` (under `4∣n`) +
    `publicKeyBytes_extract` (unconditional) in `Concrete/Encoding.lean`; standard-axioms-only. The bridge
    drops both `hsigDecode`/`hpkDecode` params and discharges them inline (adds `hn4 : 4 ∣ p.n`).
  - `hn_ovf`: trivially dischargeable numeric bound. Bridge now conditional only on structural/numeric
    side-conditions (`hn`, `hsbytelen`, `hn_ovf`, `hn4 : 4 ∣ p.n`).

**`while`-loop unprovability (KEY FINDING s8, reusable):** Lean's `while c do … (mut)` lowers to
`forIn Lean.Loop.mk` → an opaque `partial` `Lean.Loop.forIn.loop✝` with NO `rfl`-reduction and NO
simp-usable equation (even the 0-iteration case can't be closed). So any imperative codec/kernel written
with `while` is **unprovable as-is** — unlike `for i in [0:n]` (→ `List.foldl`, the B6-provable form).
Fix pattern: refactor `while i+3<n do … i:=i+4` → `for b in [0:n/4] do let i:=4*b; …` (byte-identical;
iteration count `⌊n/4⌋` matches exactly for all n). This affects `compress`/`decompress` (ENC-1) and the
other `Concrete/*.lean` `while` codecs too if they're ever to be proven.

**hpkDecode — DONE (s9).** Both pk codec lemmas proven in `Concrete/Encoding.lean`, standard-axioms-only:
- `pkDecode_pkEncode (hn4 : 4 ∣ n) : pkDecode n (pkEncode n h) = some h` — the decode `forIn` invariant
  (`decode_loop_invariant`: characterizes the loop over `List.range'`, no-reject state `⟨none,R⟩`, correct
  decoded values + frame); no-reject precondition discharged by `pkEncode_not_reject` (dead `≥ modulus`
  branch since each decoded coeff `= h[k].val < modulus`). Per-group crux = the banked `group_roundtrip`.
- `publicKeyBytes_extract` (unconditional) — `(publicKeyBytes logn h).extract 1 size = pkEncode n h`.
- Bridge rewired: `concrete_verify_eq_verify` drops `hsigDecode`/`hpkDecode`, adds `hn4 : 4 ∣ p.n`,
  discharges both inline. The 56-bit pack/unpack scaffolding (`group_roundtrip`, `E_*`, `gblock_*`,
  `pkEncode_eq_E`) was lifted from `docs/agents/falcon-hpkdecode-wip.lean` (still kept as a reference).
- KG-1 `keyGenFromSeed` sorry; KG-2 NTRUSolve ascent sorry; KG-3 no keygen correctness theorem.
- **KG-4/KG-5** NTRUSolver local stubs (`FXR.sqr`/`vect_*`/`poly_big_to_small`) shadow the real, fully-implemented
  `Concrete/FXR.lean`/`PolyBigInt.lean` — ~8 redundant sorries. KG-6 `check_ortho_norm` vacuous (fixed by KG-4).
  (Refuted sub-claim: the local `ofInt` does NOT mis-sign negatives — `<<<32` discards the differing bits.)
- SZ-2 `concretePrimitives.samplerZ` runs over ℝ (≠ FPR path); SZ-3 5 FPR error bounds `sorry`. TS-F transitive ToMathlib Rényi `sorry`.

**Verified-faithful (ok):** params vs Table 3.3 (`betaSquared` 34034726/70265242), centered-rep L2 norm,
RCDT/FACCT/σ constants bit-exact, compress internal unique-encoding checks, headers + 14-bit PK packing,
`toFFTTarget` sign-folding, GS-norm threshold 72251709809335 (v1.2/c-fn-dsa), no `native_decide`/`axiom` in Concrete.

## 4. Baseline — verified 2026-06-29 @ `falcon-faithfulness-review` (s9, hpkDecode landed / VER-1 closed; build-warning total 24)
**19 live Falcon sorries** (authoritative = build `declaration uses 'sorry'` warnings, NOT raw `grep` which
over-counts prose/comments). B6 added two PROVEN theorems (no new sorries) and removed two `concrete_verify_eq_verify`
hypotheses; the live-sorry inventory is unchanged from s6:
- `Concrete/NTRUSolver.lean` ×11 (decls 73,86,89,90,91,92,94,95,97,394,412) — ~8 are KG-4/KG-5 shadows.
- `Concrete/FPRBridge.lean` ×5 (79,85,91,97,105). `Security.lean` ×2 (111 `verify_sign_correct`, 302 `euf_cma_security`).
  `Scheme.lean` ×1 (121 `keyGenFromSeed`). `ApproxArith.lean` = 0 live (241 prose; 257–264 commented).
- Non-Falcon load-bearing: `GPVHashAndSign.lean` ×4 (270/283/332/363) + `ToMathlib/…/RenyiDivergence.lean:736` ×1.
  **Build-warning total = 24.** (Build reports *decl* lines; older notes cited *token* lines — same decls.)
- Anchors: `Scheme.lean` `sign`:262, `rqToIntPolyCentered`:245, `falconPSF_eval_trapdoorSample`:202,
  `fromFFTPreimage`:158, `falconPSF`:185; `Primitives.lean` `FalconTree.leaf`:94, `ffSampling` κ=0:262;
  `Concrete/FFT.lean` `ffsampFFTDeepest`:356; `Concrete/Instance.lean` `negacyclicMulU32_eq_negacyclicMul`:447,
  `pairL2NormSqU32_eq_pairL2NormSq`:645; `Concrete/FPRBridge.lean` `concrete_verify_eq_verify`:121.

## 5. Session log (terse)
- **s0** (review + bootstrap) — three-way audit (Artifact §7), branch + doc + harness created. No code.
- **s1** — **B8** (removed vacuous law, ⚠-marked theorems) + **B1** (leaf 2×2, ffSampling κ=0; counting argument
  256 leaves vs 128 κ=1 nodes overturned a START-review re-leveling). END review caught nothing new.
- **s2** — **TS-5** fix + proved `falconPSF_eval_trapdoorSample`; END review caught & fixed SIGN-3 (stddev/isigma
  docstring inversion). 20 sorries.
- **s3** — checkpoint: locked B2 plan (rejection sampler → fuel-bounded `Option` loop, `fsAbortSignLoop` prior art).
- **s4** — **B2 `sign` implemented** (sorry resolved; enquirer goal met) + `rqToIntPolyCentered`; START review gave
  F5 (productivity probabilistic → `none`) + F7 (`compress … p.sbytelen`); END review confirmed the helper is the
  exact inverse, 0 refuted. 20→19 sorries.
- **s5** — checkpoint: START review validated the `verify_sign_correct` proof plan SOUND (gaps: F8 index bridge,
  ENC-1 conditional); corrected a subagent's false `main`-branch claim. No code.
- **s5-milestone** (this) — full 9-dim adversarial re-audit @ `f405e7c2`: NO DRIFT (19 confirmed); all
  resolved/ok claims re-verified sound; surfaced KG-4/KG-5 (shadowing quick-win) + re-confirmed B9. Doc rewritten fresh.

- **s6** — **B9/ENC-3 fixed**: `decompress` rejects `d.length ≠ dlen` (was `< dlen`), closing over-length
  signature malleability at the single verify chokepoint (`Concrete/Encoding.lean:79`); repaired the
  dependent `concrete_verify_eq_verify` nil-branch (`FPRBridge.lean`, `hsbytelen.ne`) and removed a now-dead
  `hslen`. END review (Encoding+Verify): fix closes the bug with **no regression** (compress pads to exactly
  `dlen`; over-length is a strict superset of previously-rejected inputs), no second `sigDecode` fix needed,
  no new sorry (19). Build + test module green.

- **s7** — **B6 kernel equalities PROVEN**: `negacyclicMulU32_eq_negacyclicMul` (unconditional) +
  `pairL2NormSqU32_eq_pairL2NormSq` (under UInt64 no-overflow `hn`) in `Concrete/Instance.lean`
  (~19 private helpers; forIn→foldl + Array.set! invariant, technique cribbed from `~/CompPoly` NTTFast,
  not imported). START review validated the plan + caught the doc's "unconditional" overstatement; mid-proof
  found the ∀n norm equality is **false** (UInt64 overflow at n≈2.4e11) → added the `hn` bound. Rewired
  `concrete_verify_eq_verify` **4→3 hyps** (removed `hmul`/`hnorm`, added numeric `hn_ovf`); all three
  theorems standard-axioms-only. END review (Verify): **GREEN, no regression** — independently re-ran
  `#print axioms`, confirmed both RHS chains target the genuine spec (not weakened), `hn_ovf` honest, same
  conclusion both branches; refuted its own tool's stale-GPV-lines finding. Full `LatticeCrypto` build green;
  sorry count 24 (unchanged — B6 cuts hyps, not sorries). **Next: discharge the codec round-trips**
  `hsigDecode`/`hpkDecode` (ENC-1/F7) to make the verify bridge end-to-end, or `verify_sign_correct`, or KG-quickwin.

- **s8** — **codec round-trips (partial; paused to avoid context overflow).** START review (Encoding):
  GREEN — both round-trips TRUE (reviewer ran a 200k+ random pack/unpack model, 0 mismatches), `hpkDecode`
  needs `4∣n`, ENC-2 false codec confirmed isolated to the orphan `Falcon/Encoding.lean`. **`hsigDecode`
  PROVEN** (`Concrete/Encoding.lean` `sigDecode_sigEncode`, standard-axioms-only). Discovered **`while`
  loops are unprovable** (opaque `partial Lean.Loop.forIn.loop`) → **refactored `pkEncode`/`pkDecode`
  `while`→`for b in [0:n/4]`** (byte-identical: pure-Lean `#eval` round-trip + exact iteration-count match).
  **`hpkDecode` IN PROGRESS:** hard crux already proven + banked in `docs/agents/falcon-hpkdecode-wip.lean`
  (per-group identity `group_roundtrip` + `pkEncode` characterization); remaining = decode `forIn` invariant
  + `publicKeyBytes_extract` + wiring (+`hn4`). Current tree builds clean; no new sorries. **Next (fresh
  session, bootstrap from the VER-1 resume plan + the WIP file): finish `hpkDecode`, then `verify_sign_correct`.**

- **s9** — **hpkDecode PROVEN; VER-1 CLOSED.** Lifted the s8 WIP scaffolding into `Concrete/Encoding.lean`
  and proved `pkDecode_pkEncode` (decode `forIn` invariant `decode_loop_invariant` + dead-reject
  `pkEncode_not_reject`) + `publicKeyBytes_extract` + `pkEncode_size`. Rewired
  `FPRBridge.concrete_verify_eq_verify` to drop `hsigDecode`/`hpkDecode` and discharge both inline (added
  `hn4 : 4 ∣ p.n`) — the byte-level verifier now provably equals the spec verifier with **no semantic hyps**.
  Heavy proof delegated to a background agent; output **adversarially re-verified** at HEAD: `#print axioms`
  = standard-only on all three theorems, full `LatticeCrypto` build green, sorry count **24** (unchanged —
  VER-1 discharges hyps, not sorries), lemma statements confirmed unweakened (`publicKeyBytes_extract`
  unconditional; `pkDecode_pkEncode` only the necessary `4∣n`; bridge conclusion unchanged),
  `decode_loop_invariant` confirmed non-vacuous. Cleaned 20 `show`→`change` lint warnings (no linter
  disabled). **Next: `verify_sign_correct` (needs F8 + ENC-1 compress/decompress `while`→`for`), or KG-quickwin
  (note: real FXR/PolyBigInt signatures differ from the stubs — not a clean drop-in).**

## 6. Drift-check snippet
```bash
cd "$(git rev-parse --show-toplevel)"
git branch --show-current      # expect falcon-faithfulness-review (verify LIVE)
# Authoritative live-sorry count (expect 24 = 19 Falcon + 4 GPV + 1 ToMathlib/RenyiDivergence):
lake build LatticeCrypto.Falcon.Security LatticeCrypto.Falcon.Concrete.FPRBridge \
  LatticeCrypto.Falcon.Concrete.NTRUSolver 2>&1 | grep -c "declaration uses"
grep -n "sorry" VCVio/CryptoFoundations/GPVHashAndSign.lean | cut -d: -f1   # 270 283 332 363
grep -c "hashToPoint_welldefined" LatticeCrypto/Falcon/Primitives.lean      # 0 (removed s1)
```

## 7. References
- Full original review Artifact (severity-ranked, all findings): `https://claude.ai/code/artifact/5e8ff7c5-dcb4-4ba1-94a4-6ec986f44b52`
- Sources: Falcon v1.2 PDF `https://falcon-sign.info/falcon.pdf` (frozen); default target **c-fn-dsa** `github.com/pornin/c-fn-dsa` @ `33026d4d` (submodule gitlink, compiled into `csrc/falcon/fndsa.c`, not source-diffable locally).
- **IPD watch** (re-check at milestones; pin B7 constants when live): `https://csrc.nist.gov/pubs/fips/206/ipd` — 404 as of 2026-06-25. FN-DSA submitted for approval 2025-08-28; final expected late-2026/2027.
- Memory pointer: `falcon-review-status`.

## 8. Spec-of-record matrix (M1–M9)
| # | Behavior | v1.2 | FN-DSA | c-fn-dsa | Code | Faithful to |
|---|---|---|---|---|---|---|
| M1 | HashToPoint preimage | `nonce‖msg` | `nonce‖SHAKE256(vk)[0:64]‖0x00‖len(ctx)‖ctx‖msg` | = FN-DSA raw | `salt‖SHAKE256(pk)[0:64]‖0x00 0x00‖msg` | FN-DSA/c-fn-dsa |
| M2 | Salt across retries | once | fresh | fresh | fresh per attempt | FN-DSA/c-fn-dsa |
| M3 | Acceptance norm | L2 | L2 + L∞ | L2 | L2 only | v1.2/c-fn-dsa (≠ FN-DSA) |
| M4 | LDL leaf-range gate | implicit | explicit `[σ_min,σ_max]` | absent | absent | v1.2/c-fn-dsa (≠ FN-DSA) |
| M5 | Base sampler budget | 72-bit | 79-bit | 72-bit | 72-bit | v1.2/c-fn-dsa (≠ FN-DSA) |
| M6 | Sig header byte | `0cc1nnnn` (cc=01 ⇒ 0x39/0x3A) | `0x30+logn` | `0x30+logn` | `0x30+logn` | all three |
| M7 | GS-norm threshold | `1.17√q` (72251709809335) | `0.9999·1.17√q` | `1.17√q` | 72251709809335 | v1.2/c-fn-dsa |
| M8 | Sign loop shape | nested do-while | single retry | single retry | single fuel loop | FN-DSA/c-fn-dsa |
| M9 | Verify float usage | int-only | int-only | int-only | int-only | all three |
