# Falcon Faithfulness & Soundness Remediation — Working Doc

Canonical state for the `falcon-faithfulness-review` branch. **This file is the bootstrap: a
fresh session must be able to resume from it alone, without chat history.** It is paired with a
re-runnable adversarial-review harness at [`scripts/falcon_review.mjs`](../../scripts/falcon_review.mjs).

Scope under review: `LatticeCrypto/Falcon/**` (+ the load-bearing `VCVio/CryptoFoundations/GPVHashAndSign.lean`).
Baselines, judged separately, no single authoritative spec:
**Falcon v1.2** (round-3 PDF, `r‖m` hash, salt-once, L2-only) ·
**FN-DSA / FIPS 206 IPD** (pk-bound domain-separated hash, fresh-salt-per-retry, L2 **and** L∞, leaf-range gate, 79-bit base sampler) ·
**Falcon+ / c-fn-dsa** (Pornin reference @ `33026d4d`; tracks FN-DSA but 72-bit sampler + L2-only).

---

## 0. Session protocol (bootstrapped, self-contained)

Every session **starts and ends** with a fresh adversarial review + document-refresh check.
Do not trust this doc blindly — the protocol re-validates it.

### START
1. `git status` — expect branch `falcon-faithfulness-review`, otherwise stop and reconcile.
2. **Drift check** (deterministic, no agents) — run the snippet in §6. Compare the live-`sorry`
   counts and anchor citations to the **Baseline (§4)**. Any mismatch ⇒ the code moved since last
   session; reconcile §3/§4 before doing anything else.
3. **Adversarial review** (agents) — run the harness scoped to the area you intend to touch:
   `Workflow scriptPath=scripts/falcon_review.mjs args={"dimensions":["…"],"full":false}`.
   Read its report. Anything it surfaces that is **not** already in §3 gets added there.
4. Pick the next **critical-path** item (§2), restate the plan, then work.

### END
1. Re-run the **drift check** (§6); update the **Baseline (§4)** numbers/citations to HEAD.
2. **Adversarial review** scoped to what changed (`args.changed="<summary>"`), focused on
   regressions: new `sorry`s, newly-vacuous/unsound statements, previously-`ok` items broken,
   citations that drifted.
3. **Refresh this doc**: tick §2, update §3 findings + code refs, append a **§5 Session Log** entry
   (date · what changed · what was validated · residual risk · next entry point).
4. Update the `falcon-review-status` memory pointer + the review Artifact if material.
   **Commit** (the doc must reflect HEAD).

> Cost note: the full 9-dimension + adversarial sweep is heavy (~20 agents). Use `full:false` with a
> `dimensions` subset for routine session bookends; reserve `full:true` (and `skipSources:false` to
> re-fetch FN-DSA/c-fn-dsa) for milestones or after large changes.

---

## 1. Status summary
- **Faithful?** v1.2: no (by design — FN-DSA target). FN-DSA: partial (omits L∞, leaf-range, 79-bit).
  Falcon+/c-fn-dsa: yes at the concrete/constant level.
- **Complete?** No — 20 live `sorry`s incl. 3 load-bearing primitives.
- **Sound?** No — 0/4 security theorems proven; 2 are unsound *as stated*; the generic GPV chain is `sorry`.
- This branch has made **no Falcon code edits yet** (review + scaffolding only).
- Full report (severity-ranked, all findings): see Artifact link in §7.

## 2. Critical path (status)
- [ ] **B8** — Integrity cleanup: delete/strengthen vacuous `hashToPoint_welldefined`; mark
  `verify_sign_correct` / `euf_cma_security` `stop`/conjectural. *(cheap; do first)*
- [ ] **B1** — Fix the abstract `ffSampling` leaf (root blocker; 2×2-aware base case).
- [ ] **B5** — Make `samplerZ_correct` satisfiable (ideal sampler + `SamplerQuality` Rényi).
- [ ] **B2** — Define `sign` + `keyGenFromSeed` (Option B / abstract PSF loop). *(enquirer goal)*
- [ ] **B3b** then **B3a** — conditional EUF-CMA via `euf_cma_split_bound`; then the generic GPV lemmas.
- [ ] **B6** — Kernel + codec equality lemmas (make `concrete_verify_eq_verify` unconditional). *(parallel)*
- [ ] **B4** — Finish NTRUSolve ascent + prove `solve_NTRU ⊨ ntruEquation`. *(refinement)*
- [ ] **B7** — FN-DSA decision + FIPS 206 IPD confirmation (L∞ value, 79-bit, 0.9999 factor). *(scoping)*

## 3. Validated findings (condensed — full detail in the Artifact, §7)
| ID | Sev | One-line | Key citation |
|---|---|---|---|
| B1 / SD-5 | divergence (correctness) | abstract `ffSampling` leaf has one σ + no `l01`; concrete deepest does full 2×2 LDL (2 stddevs + correction) ⇒ abstract `trapdoorSample` samples wrong distribution | `Primitives.lean:251-264` vs `FFT.lean:356-391` |
| UN-1 | unsound | `verify_sign_correct` quantifies over support of a `sorry`ed `sign` | `Security.lean:105-119`; `Scheme.lean:224-225` |
| UN-2 | unsound | `euf_cma_security` discards hypotheses (`let _ :=`) and asserts bound | `Security.lean:290-321` |
| UN-3 | unsound (generic) | GPV reductions + game-hops are `sorry`; the split-bound theorem is proved *modulo* them | `GPVHashAndSign.lean:270,283,332,363` |
| UN-4 | unsound | `hashToPoint_welldefined : … → True` is vacuous | `Primitives.lean:287` |
| UN-5 | unsound | no proof `solve_NTRU ⊨ ntruEquation`; `GenerableRelation` only assumed | `Security.lean:106,147` |
| B5 / IN-8/9 | incompleteness | `samplerZ_correct` demands *exact* PMF (RCDT only Rényi-close); concrete sampler runs over ℝ, distinct from FPR path | `Primitives.lean:281-283`; `Instance.lean:186-191` |
| B4 / IN-2..4 | incompleteness | NTRUSolve ascent (`solve_NTRU_intermediate`, `solve_NTRU_depth0`), `FXR.sqr`, `vect_*` stubs | `NTRUSolver.lean:73,86-98,395,413` |
| B6 / IN-5/6/11 | incompleteness | no `negacyclicMulU32=negacyclicMul` / `pairL2NormSqU32=pairL2NormSq`; codec roundtrips unproven; `concrete_verify_eq_verify` conditional | `FPRBridge.lean:117-153`; `Instance.lean:47-80` |
| SD-1 | divergence (vs v1.2, intended) | HashToPoint binds pk: `salt‖SHAKE256(pk)[0:64]‖0x00 0x00‖msg` | `Sampling.lean:40-43` |
| SD-2 | divergence (vs FN-DSA) | only L2 bound; no L∞ in sign/verify (`cInfNorm` exists but unused) | `Scheme.lean:191,241`; `Ring/Norms.lean:203` |
| SD-3 | divergence (vs FN-DSA) | no LDL leaf-range `[σ_min,σ_max]` gate | `FFT.lean:372,386` |
| SD-4 | divergence (vs FN-DSA slides) | 72-bit base sampler, not 79-bit | `SamplerZ.lean:112-123` |

**Verified-faithful (ok):** params vs Table 3.3 (`betaSquared` 34034726/70265242), centered-rep L2 norm
(q/2=6144), RCDT/FACCT/σ constants bit-exact, encoding bit-layout + unique-encoding checks, headers +
14-bit PK packing, `toFFTTarget` sign-folding, `concrete_verify_eq_verify` sound (conditional), no
`native_decide`/`axiom` in the Concrete layer.

## 4. Baseline — validated 2026-06-25 @ `main` HEAD `a41b514f`
- **Live `sorry`s in `LatticeCrypto/Falcon/` = 20**: NTRUSolver 11 · FPRBridge 5 · Scheme 2 · Security 2.
  (`ApproxArith.lean` has 5 `sorry` tokens but all comment-only: lines 241,257,258,263,264.)
- **Load-bearing generic `sorry`s** (`VCVio/CryptoFoundations/GPVHashAndSign.lean`): 270, 283, 332, 363.
- **Anchor citations** (must still resolve): `Scheme.lean:121` (`keyGenFromSeed`), `Scheme.lean:225`
  (`sign`), `Security.lean:119,321`, `Primitives.lean:287` (`…→ True`), `Primitives.lean:251-264` &
  `FFT.lean:356-391` (SD-5), `Instance.lean:186-191` (sampler ℝ path).

## 5. Session log
- **2026-06-25 — session 0 (review + bootstrap).** Three-way faithfulness/soundness audit (21-agent
  workflow, every finding adversarially verified, 0 refuted). Validated the baseline above directly.
  Created branch `falcon-faithfulness-review`, this doc, and `scripts/falcon_review.mjs`. **No Falcon
  code edited.** Residual risk: FN-DSA L∞/79-bit/0.9999 from unfrozen NIST slides, not the IPD;
  c-fn-dsa submodule not checked out (table equalities read from brief). Next entry point: **B8 → B1**.

## 6. Drift-check snippet
```bash
cd "$(git rev-parse --show-toplevel)"
git branch --show-current                     # expect falcon-faithfulness-review
grep -rho "sorry" LatticeCrypto/Falcon/ | wc -l            # expect 25 tokens (20 live + 5 comment)
grep -rcn "sorry" LatticeCrypto/Falcon/ | grep -v ':0' | sort -t: -k2 -rn
grep -n "sorry" VCVio/CryptoFoundations/GPVHashAndSign.lean # expect 270,283,332,363
grep -n "hashToPoint_welldefined" LatticeCrypto/Falcon/Primitives.lean   # expect "…→ True" still present
```

## 7. References
- Full review Artifact (severity-ranked findings, spec-of-record matrix, discharge plan):
  `https://claude.ai/code/artifact/5e8ff7c5-dcb4-4ba1-94a4-6ec986f44b52`
- Spec source of truth: Falcon v1.2 PDF (`https://falcon-sign.info/falcon.pdf`); FN-DSA = FIPS 206 IPD
  (confirm exact constants — see B7); c-fn-dsa = `github.com/pornin/c-fn-dsa` @ `33026d4d`.
- Memory pointer: `falcon-review-status`.

## 8. Spec-of-record matrix (M1–M9, condensed)
| # | Behavior | v1.2 | FN-DSA | c-fn-dsa | Code | Faithful to |
|---|---|---|---|---|---|---|
| M1 | HashToPoint preimage | `nonce‖msg` | `nonce‖SHAKE256(vk)[0:64]‖0x00‖len(ctx)‖ctx‖msg` | = FN-DSA raw | `salt‖SHAKE256(pk)[0:64]‖0x00 0x00‖msg` | FN-DSA/Falcon+ |
| M2 | Salt across retries | once | fresh | fresh | fresh per counter | FN-DSA/Falcon+ |
| M3 | Acceptance norm | L2 | L2 + L∞ | L2 | L2 only | v1.2/Falcon+ (≠ FN-DSA) |
| M4 | LDL leaf-range gate | implicit | explicit `[σ_min,σ_max]` | absent | absent | v1.2/Falcon+ (≠ FN-DSA) |
| M5 | Base sampler budget | 72-bit | 79-bit | 72-bit | 72-bit | v1.2/Falcon+ (≠ FN-DSA) |
| M6 | Sig header byte | `0cc1nnnn` | `0x30+logn` | `0x30+logn` | `0x30+logn` | all three |
| M7 | GS-norm threshold | `1.17√q` | `0.9999·1.17√q` | `1.17√q` | `72251709809335` | v1.2/Falcon+ |
| M8 | Sign loop shape | nested do-while | single retry | single retry | single counter loop | FN-DSA/Falcon+ |
| M9 | Verify float usage | int-only | int-only | int-only | int-only | all three |
