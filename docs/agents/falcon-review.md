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
- [x] **B8** — DONE (session 1): deleted vacuous `hashToPoint_welldefined`; added ⚠ CONJECTURAL
  markers above `verify_sign_correct` / `euf_cma_security`.
- [x] **B1** — DONE (session 1, abstract sampler): `FalconTree.leaf` now carries `(σ₀,σ₁,l01Re,l01Im)`
  and `ffSampling` κ=0 mirrors `ffsampFFTDeepest`. **Remaining (→ tracked under B4):** the tree-*builder*
  (`keyGenFromSeed`) that populates the leaf from the LDL, and an equivalence lemma
  `abstract ffSampling ≈ ffsampFFTDeepest`.
- [ ] **B5** — Make `samplerZ_correct` satisfiable (ideal sampler + `SamplerQuality` Rényi).
- [ ] **B2** — Define `sign` + `keyGenFromSeed` (Option B / abstract PSF loop). *(enquirer goal)*
- [ ] **B3b** then **B3a** — conditional EUF-CMA via `euf_cma_split_bound`; then the generic GPV lemmas.
- [ ] **B6** — Kernel + codec equality lemmas (make `concrete_verify_eq_verify` unconditional). *(parallel)*
- [ ] **B4** — Finish NTRUSolve ascent + prove `solve_NTRU ⊨ ntruEquation`. *(refinement)*
- [ ] **B9** — Signature canonical-encoding / malleability: `Decompress`/`sigDecode` accept over-length
  & non-canonical signatures (ENC-3 — the one genuine *wire-level* defect found in session 1). Enforce
  fixed-bitlength + trailing-zero checks. *(target-independent; surfaced by the session-1 full sweep)*
- [ ] **B7** — FN-DSA acceptance-region decision (L∞, leaf-range, 79-bit). **Decoupled from the rest:**
  parameterize `isShort`/norm bound over an *optional* L∞ (L2-only instance = today's c-fn-dsa behavior;
  L∞ instance ready to switch on) so adopting FN-DSA-final is a config flip. Default target = **c-fn-dsa**
  (freshest *retrievable* spec). FIPS 206 IPD is **not fetchable** as of 2026-06 (`csrc.nist.gov/pubs/fips/206/ipd`
  → 404; submitted for approval 2025-08-28, final expected late-2026/2027). Re-check IPD at milestones via the
  harness `full:true` watch; pin L∞/79-bit/0.9999 when it lands. *(scoping; does NOT block B1/B2/B5/B6/B8/B3a)*

## 3. Validated findings (condensed — full detail in the Artifact, §7)
| ID | Sev | One-line | Key citation |
|---|---|---|---|
| ~~B1 / SD-5~~ **RESOLVED s1** | was divergence (correctness) | leaf now carries `(σ₀,σ₁,l01)`; κ=0 mirrors `ffsampFFTDeepest`. Counting argument settled it (256 bottom-2×2 leaves vs 128 κ=1 nodes ⇒ `l01` must be at the leaf; START-review re-leveling was incorrect). Remaining: builder + equivalence lemma | `Primitives.lean:~91,251-271` ↔ `FFT.lean:356-391` |
| UN-1 | unsound (marked s1) | `verify_sign_correct` quantifies over support of a `sorry`ed `sign` — now carries a ⚠ CONJECTURAL marker; still `sorry` pending B2 | `Security.lean` (theorem ~109) |
| UN-2 | unsound (marked s1) | `euf_cma_security` discards hypotheses and asserts bound — now ⚠ CONJECTURAL; still `sorry` pending B3 | `Security.lean` (theorem ~300) |
| UN-3 | unsound (generic) | GPV reductions + game-hops are `sorry`; the split-bound theorem is proved *modulo* them | `GPVHashAndSign.lean:270,283,332,363` |
| ~~UN-4~~ **RESOLVED s1** | was unsound | vacuous `hashToPoint_welldefined : … → True` deleted from `Primitives.Laws` | (removed) |
| UN-5 | unsound | no proof `solve_NTRU ⊨ ntruEquation`; `GenerableRelation` only assumed | `Security.lean:106,147` |
| B5 / IN-8/9 | incompleteness | `samplerZ_correct` demands *exact* PMF (RCDT only Rényi-close); concrete sampler runs over ℝ, distinct from FPR path | `Primitives.lean:281-283`; `Instance.lean:186-191` |
| B4 / IN-2..4 | incompleteness | NTRUSolve ascent (`solve_NTRU_intermediate`, `solve_NTRU_depth0`), `FXR.sqr`, `vect_*` stubs | `NTRUSolver.lean:73,86-98,395,413` |
| B6 / IN-5/6/11 | incompleteness | no `negacyclicMulU32=negacyclicMul` / `pairL2NormSqU32=pairL2NormSq`; codec roundtrips unproven; `concrete_verify_eq_verify` conditional | `FPRBridge.lean:117-153`; `Instance.lean:47-80` |
| SD-1 | divergence (vs v1.2, intended) | HashToPoint binds pk: `salt‖SHAKE256(pk)[0:64]‖0x00 0x00‖msg` | `Sampling.lean:40-43` |
| SD-2 | divergence (vs FN-DSA) | only L2 bound; no L∞ in sign/verify (`cInfNorm` exists but unused) | `Scheme.lean:191,241`; `Ring/Norms.lean:203` |
| SD-3 | divergence (vs FN-DSA) | no LDL leaf-range `[σ_min,σ_max]` gate | `FFT.lean:372,386` |
| SD-4 | divergence (vs FN-DSA slides) | 72-bit base sampler, not 79-bit | `SamplerZ.lean:112-123` |
| ~~SIGN-3~~ **RESOLVED s1** | was unsound (introduced + caught same session) | the B1 leaf docstring described `σ` as the concrete `isigma` (`√d·1/σ`) while passing it as a true stddev to `samplerZ`; docstring corrected to `σ = σ/√d` with an explicit convention note | `Primitives.lean:~78-85` |
| ENC-3 (B9) | **spec-divergence (NEW s1)** | `Decompress`/`sigDecode` accept over-length / non-canonical signatures ⇒ wire-level malleability (the one genuine wire defect) | `Encoding.lean:74,109-111,186-191` |
| TS-5 | incompleteness (NEW s1) | `Correct (falconPSF)` is likely **false** as stated (ℝ `ifftRound` reconstruction need not give `eval = c` exactly) — a real risk for B2/B3, check before relying on it | `Scheme.lean` (`falconPSF`, `fromFFTPreimage`) |

**Verified-faithful (ok):** params vs Table 3.3 (`betaSquared` 34034726/70265242), centered-rep L2 norm
(q/2=6144), RCDT/FACCT/σ constants bit-exact, encoding bit-layout + unique-encoding checks, headers +
14-bit PK packing, `toFFTTarget` sign-folding, `concrete_verify_eq_verify` sound (conditional), no
`native_decide`/`axiom` in the Concrete layer.

## 4. Baseline — validated 2026-06-25 @ branch `falcon-faithfulness-review` (after session 1)
- **Live `sorry`s in `LatticeCrypto/Falcon/` = 20** (unchanged by session 1): NTRUSolver 11 · FPRBridge 5 ·
  Scheme 2 · Security 2. Authoritative signal = the build's `declaration uses 'sorry'` warnings, **not**
  a raw `grep`: as of session 1 the raw `grep -c sorry` over `Falcon/` returns **29** tokens (was 25)
  because the new ⚠ CONJECTURAL markers + leaf docstrings mention the word "sorry" in prose. `ApproxArith.lean`
  still contributes 5 comment-only tokens.
- **Load-bearing generic `sorry`s** (`VCVio/CryptoFoundations/GPVHashAndSign.lean`): decls at 266, 279, 316, 344
  (`sorry` tokens at 270, 283, 332, 363).
- **Anchor citations** (must still resolve): `Scheme.lean:121` (`keyGenFromSeed`), `Scheme.lean:~224` (`sign`),
  `Security.lean` theorems `verify_sign_correct` (~109) & `euf_cma_security` (~300),
  `Primitives.lean:~91` (`leaf σ₀ σ₁ l01Re l01Im`) & `~251-271` (`ffSampling` κ=0) ↔ `FFT.lean:356-391`
  (`ffsampFFTDeepest`), `Instance.lean:186-191` (sampler ℝ path). (`Primitives.lean:287` vacuous law — removed.)

## 5. Session log
- **2026-06-25 — session 0 (review + bootstrap).** Three-way faithfulness/soundness audit (21-agent
  workflow, every finding adversarially verified, 0 refuted). Validated the baseline above directly.
  Created branch `falcon-faithfulness-review`, this doc, and `scripts/falcon_review.mjs`. **No Falcon
  code edited.** Residual risk: FN-DSA L∞/79-bit/0.9999 from unfrozen NIST slides, not the IPD;
  c-fn-dsa submodule not checked out (table equalities read from brief). Next entry point: **B8 → B1**.

- **2026-06-25 — session 1 (B8 + B1).** START: drift clean (20 live sorrys). Landed **B8** (deleted
  vacuous `hashToPoint_welldefined`; ⚠ markers on the two unsound theorems) and **B1** (leaf carries
  `(σ₀,σ₁,l01)`; κ=0 `ffSampling` mirrors `ffsampFFTDeepest`). START review re-leveled B1 to incompleteness;
  **overturned by a counting argument** (256 bottom-2×2 leaves vs 128 κ=1 nodes ⇒ `l01` must live at the
  leaf). Build clean, no new live sorrys (still 20); fixed a 100-col lint. END review (full 9-dim sweep —
  `args` scoping didn't thread; **harness fixed** to parse stringified args) **caught SIGN-3**, a stddev/isigma
  docstring inversion I introduced — **fixed** (docstring now states true stddev `σ/√d` + convention note);
  re-confirmed no drift, refuted a false "Security=6 sorrys" (prose). Newly surfaced by the fuller sweep:
  **ENC-3** (wire-level signature malleability → new **B9**) and **TS-5** (`Correct (falconPSF)` likely false —
  risk for B2/B3). Residual: c-fn-dsa submodule empty locally (pin `33026d4d`), FN-DSA IPD still 404.
  **Next entry point: B2** (define `sign` + `keyGenFromSeed`); pin the σ convention (SIGN-3) when building
  the leaf; B6/B9 parallelizable.

## 6. Drift-check snippet
The **authoritative** live-`sorry` count is the build warnings (raw `grep` over-counts because comments
now mention "sorry" in prose — see §4). Quick deterministic check:
```bash
cd "$(git rev-parse --show-toplevel)"
git branch --show-current                     # expect falcon-faithfulness-review
# Authoritative live-sorry count (expect 20 in Falcon/, +4 in GPVHashAndSign):
lake build LatticeCrypto.Falcon.Security LatticeCrypto.Falcon.Concrete.FPRBridge \
  LatticeCrypto.Falcon.Concrete.NTRUSolver 2>&1 | grep -c "declaration uses"
grep -rcn "sorry" LatticeCrypto/Falcon/ | grep -v ':0' | sort -t: -k2 -rn  # per-file (incl. prose)
grep -n "sorry" VCVio/CryptoFoundations/GPVHashAndSign.lean | cut -d: -f1   # expect 270,283,332,363
grep -c "hashToPoint_welldefined" LatticeCrypto/Falcon/Primitives.lean      # expect 0 (removed session 1)
```

## 7. References
- Full review Artifact (severity-ranked findings, spec-of-record matrix, discharge plan):
  `https://claude.ai/code/artifact/5e8ff7c5-dcb4-4ba1-94a4-6ec986f44b52`
- Spec sources: Falcon v1.2 PDF (`https://falcon-sign.info/falcon.pdf`, frozen, oldest);
  **default executable target = c-fn-dsa** `github.com/pornin/c-fn-dsa` @ `33026d4d` (freshest *retrievable*).
- **IPD watch** (re-check at milestones; pin B7 constants when live): `https://csrc.nist.gov/pubs/fips/206/ipd`
  — 404 as of 2026-06-25 (not yet published). Status slides: `csrc.nist.gov/presentations/2025/fips-206-fn-dsa-falcon`.
  FN-DSA submitted for approval 2025-08-28; final expected late-2026/early-2027.
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
