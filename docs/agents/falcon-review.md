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
- **Complete?** No — **19** live `sorry`s (s4: `sign` implemented, was 20). `keyGenFromSeed` + NTRUSolve
  ascent + the security/correctness proofs remain.
- **Sound?** No — 0/4 security theorems proven; 2 are unsound *as stated*; the generic GPV chain is `sorry`.
  (s2-END) **TS-5 fixed + verified**: `fromFFTPreimage` now reconstructs `s₁ := c − s₂·h` (`Scheme.lean:163`),
  so `eval (trapdoorSample) = c` holds — **proven, re-audited sound** (`falconPSF_eval_trapdoorSample`,
  `Scheme.lean:202`); PSF `s₁` agrees with `verify` (`:269`). The `isShort` half of `Correct (falconPSF)`
  remains open (needs a rejection/retry sampler model — the remaining B2 work). New rider **SD-TS5b**:
  abstract `isShort` (verify-consistent `s₁`) vs the concrete signer's `rint(v₀)`-based norm gate diverge
  under independent rounding (benign for the verify identity).
- Branch edits so far: **session 1** (B8 + B1), **session 2** (TS-5 fix + eval lemma, re-audited s2-END §4c). No `sign`/`keyGenFromSeed` yet.
- **Next entry point: B2** (`isShort`-half + `sign` + `keyGenFromSeed`) — TS-5 eval-half is now done and B2 is unblocked. See §4c (4).
- Full report (severity-ranked, all findings): see Artifact link in §7.

## 2. Critical path (status)
- [x] **B8** — DONE (session 1): deleted vacuous `hashToPoint_welldefined`; added ⚠ CONJECTURAL
  markers above `verify_sign_correct` / `euf_cma_security`.
- [x] **B1** — DONE (session 1, abstract sampler): `FalconTree.leaf` now carries `(σ₀,σ₁,l01Re,l01Im)`
  and `ffSampling` κ=0 mirrors `ffsampFFTDeepest`. **Remaining (→ tracked under B4):** the tree-*builder*
  (`keyGenFromSeed`) that populates the leaf from the LDL, and an equivalence lemma
  `abstract ffSampling ≈ ffsampFFTDeepest`.
- [ ] **B5** — Make `samplerZ_correct` satisfiable (ideal sampler + `SamplerQuality` Rényi).
- [~] **B2** — **(s4) `sign` DONE** — implemented as the fuel-bounded `Option` rejection loop
  (`Scheme.lean:253`, `sign : … → ℕ → ProbComp (Option Signature)`); the `sign` sorry is **resolved**
  (original enquirer goal met). New helper `rqToIntPolyCentered` (`Scheme.lean:243`). **Remaining:**
  `keyGenFromSeed` (still sorry) + the `verify_sign_correct` proof. Define `sign` + `keyGenFromSeed`
  *(Option B / abstract PSF loop)*
  **(s2-END) Prerequisite TS-5 DONE + re-audited sound (§4c)** — `fromFFTPreimage` recomputes `s₁ := c − s₂·h`
  (`Scheme.lean:163`); `eval(trapdoorSample)=c` proven (`falconPSF_eval_trapdoorSample`, `:202`), PSF `s₁`
  agrees with `verify` (`:269`). **Remaining:** the `isShort` half (rejection/retry model —
  `ffSampling` can emit over-long vectors and ProbComp has no retry combinator. **DECISION (s3): make
  `trapdoorSample` a rejection sampler** (resample until `isShort`). **s3-START investigation RESOLVED the
  totality caveat:** the framework already models reject-and-retry signing in `VCVio/CryptoFoundations/FiatShamir/WithAbort.lean`
  — `fsAbortSignLoop : … → ℕ → m (Option …)` is a **fuel-bounded total recursion** (try ≤ n attempts; `none`
  if all abort), with **conditional** correctness (`fsAbortSignLoop_cache_invariant`: `some ⟹ verify accepts`).
  `Falcon.signAttempt` already returns `ProbComp (Option (Rq×Rq))` — the exact per-attempt shape.
  **LOCKED PLAN (implement next session):**
  (a) `sign : pk sk msg → (maxAttempts : ℕ) → ProbComp (Option Signature)` mirroring `fsAbortSignLoop`:
      each iter sample salt → `c := hashToPointForPublicKey pk.h salt msg` → `signAttempt`; on `some (_,s₂)`
      `compress (Rq→IntPoly s₂) p.sbytelen` (**F7: exact `slen = p.sbytelen`**, matching `verify`'s
      `decompress … p.sbytelen` so `compress_decompress` chains); on `some comp` `return some ⟨salt, comp⟩`;
      on `none`/compress-fail, recurse; `0 ⇒ none`.
      **F5 (s4-START): the `some`-branch is NOT compress-success-by-construction** — `compress` fails when a
      centered coeff `|x|>2047` (or overflows `dlen`), independent of the L2 sum, and such a vector can pass
      `isShort` (β²≈34M) yet fail `compress`. So loop *productivity* is **probabilistic, not constructive**;
      the `none`-on-exhaustion branch handles it. Do NOT try to prove the loop yields `some`.
  (b) Needs a helper `Rq → IntPoly` (centered, via `centeredRepr` per coeff; inverse of `IntPoly.toRq`) to
      feed `compress : IntPoly → ℕ → Option …`. (`Rq`/`IntPoly` are `Vector`-backed: cf. `Concrete/Sign.lean:241`
      `Vector.ofFn … : IntPoly n` and `rqToUInt16Array` using `.toArray`.)
  (c) Restate `verify_sign_correct` against `some sig ∈ support (sign … maxAttempts)`; the `some`-branch had
      **both** `isShort` and `compress = some` (so its norm bound + roundtrip are discharged on outputs).
      ⚠ Two-world gap (UN-1, reconfirmed s4): `Falcon.verify` (byte-level, `hashToPointForPublicKey`) is NOT
      the verify the security theorems use (`falconSignatureAlg = GPVHashAndSign (falconPSF …)` queries the
      RO; sig type `Salt × (Rq×Rq)`). So `verify_sign_correct` is about the executable/byte layer; reconciling
      the two worlds is separate. `keyGenFromSeed`
      still a constructive `validKeyPair` witness (real impl gated on B4). Mind expected build friction
      (bespoke `Rq` instances — `ext`/coeff-wise, not `ring`/`abel`; cf. s2 eval-lemma). Then
  `sign` (`Scheme.lean:254`, single-attempt over the rejection sampler, matching GPV's
  no-retry `sign`) + `keyGenFromSeed` (`Scheme.lean:121`, constructive `validKeyPair` witness; real impl
  gated on B4). Mind new rider **SD-TS5b** (abstract `isShort` vs concrete norm-gate rounding).
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
| ~~TS-5~~ **RESOLVED (eval-half) s2-END** | **FIX LANDED** at `bfcccbda` working tree: `fromFFTPreimage` now returns `(c − negacyclicMul s₂ pk.h, s₂)` (`Scheme.lean:163`), `v₀` dropped, `trapdoorSample` threads `pk`; `eval(trapdoorSample)=c` is **proven** (`falconPSF_eval_trapdoorSample`, `Scheme.lean:202`) and the PSF `s₁` now **agrees** with `verify`'s `s₁=c−s₂·h` (`:269`). **Remaining:** the `isShort`-half of `Correct(falconPSF)` (needs B2 retry/rejection model). See §4c | `Scheme.lean:158-164,187,202,269` |
| SD-TS5b | **spec-divergence (NEW s2-END)** | abstract `isShort`/`pairL2NormSq` is computed on the verify-consistent `s₁=c−s₂·h`, but the concrete signer's squared-norm gate uses an *independently* `rint(v₀)`-based `s₁`; the two agree only modulo rounding. Benign for the verify/EUF-CMA identity; must be quantified iff a future proof links abstract `isShort` to the concrete gate | `Scheme.lean:158-164,192`; `Concrete/Sign.lean:169-175,182-197` |

**Verified-faithful (ok):** params vs Table 3.3 (`betaSquared` 34034726/70265242), centered-rep L2 norm
(q/2=6144), RCDT/FACCT/σ constants bit-exact, encoding bit-layout + unique-encoding checks, headers +
14-bit PK packing, `toFFTTarget` sign-folding, `concrete_verify_eq_verify` sound (conditional), no
`native_decide`/`axiom` in the Concrete layer.

## 4. Baseline — validated 2026-06-25 @ branch `falcon-faithfulness-review` (after session 4)
- **Live `sorry`s in `LatticeCrypto/Falcon/` = 19** (s4: `sign` implemented, was 20): NTRUSolver 11 ·
  FPRBridge 5 · **Scheme 1** (`keyGenFromSeed` only — `sign` resolved) · Security 2. Authoritative signal =
  the build's `declaration uses 'sorry'` warnings (= **24** total: 19 Falcon + 4 GPV + 1 `ToMathlib/…/RenyiDivergence.lean:736`),
  **not** a raw `grep` (prose ⚠ markers + docstrings mention "sorry"). `ApproxArith.lean` = 5 comment-only.
- **Load-bearing generic `sorry`s** (`VCVio/CryptoFoundations/GPVHashAndSign.lean`): decls at 266, 279, 316, 344
  (`sorry` tokens at 270, 283, 332, 363).
- **Anchor citations** (must still resolve): `Scheme.lean:121` (`keyGenFromSeed`), `Scheme.lean:~253` (`sign`,
  now fuel-bounded `Option` loop) & `~243` (`rqToIntPolyCentered`),
  `Security.lean` theorems `verify_sign_correct` (~109) & `euf_cma_security` (~300),
  `Primitives.lean:~91` (`leaf σ₀ σ₁ l01Re l01Im`) & `~251-271` (`ffSampling` κ=0) ↔ `FFT.lean:356-391`
  (`ffsampFFTDeepest`), `Instance.lean:186-191` (sampler ℝ path). (`Primitives.lean:287` vacuous law — removed.)

## 4b. Session 2 synthesis (lead-reviewer report — 2026-06-25, HEAD `bfcccbda`)

Two-dimension adversarial sweep (Sign+ffSampling, Theorem-soundness), each finding re-verified.
Re-read this session: `Scheme.lean:155-163,186,234-241`; `GPVHashAndSign.lean:91-94`, sorry tokens
270/283/332/363; `git rev-parse HEAD` = `bfcccbda05…`; grep for L∞ / `Correct falconPSF` sites.

### (1) Drift verdict vs baseline of 20 live sorrys — **NO DRIFT**
- HEAD `bfcccbda` = Session 2 START. Live bodies: `Scheme.lean:121,225` (2), `Security.lean:123,331` (2),
  GPV `270/283/332/363` (4 load-bearing) — all confirmed. `sign`/`keyGenFromSeed` still `sorry`; B2 un-started.
- `Security.lean:105/106/294/297` are prose CONJECTURAL markers, not bodies (raw grep over-counts, per §4).
- *Residual (low):* NTRUSolver 11 / FPRBridge 5 / ApproxArith 5-comment split asserted, not re-counted this session.

**PRIORITY — TS-5: is `Correct(falconPSF)` actually false? YES (confirmed, not "likely").**
`Correct` (`GPVHashAndSign.lean:91-94`) demands `eval pk x = t` ∀ `x ∈ support`; `eval = x.1 + negacyclicMul x.2 pk.h`
(`:186`); `trapdoorSample` → `fromFFTPreimage` returns `(c − v₀, −v₁)` with `v₀,v₁` **independently** `ifftRound`-ed
(`Scheme.lean:161-163`). So `eval = c − (v₀ + v₁·h)`. Exact NTRU (`fG−gF=q`, `f·h=g`, `F·h≡G mod q`) gives
pre-rounding `v₀ ≡ −v₁·h`, but `round(v₀) + round(v₁)·h ≡ 0` fails — rounding does not commute with mult-by-`h`.
No `Primitives.Laws` field links `ifftRound` to `negacyclicMul` (`Primitives.lean:298-311`). **So `s₁` should be
recomputed as `c − s₂·h`, exactly matching `verify` (`Scheme.lean:240`) and all three baselines (v1.2 Alg 16,
FN-DSA/c-fn-dsa M9) which store only `s₂`.** The current PSF `s₁` (= `c − round(v₀)`) *disagrees* with verify's `s₁`.

*Severity-tag reconciliation (the one cross-audit disagreement):* Theorem-soundness tagged TS-5 unsound-statement;
Sign+ffSampling revised it to spec-divergence because `Correct(falconPSF)` is **never instantiated** (grep: no
`Correct falconPSF` / `falconPSF.Correct` site; it appears only as `hcorrect` at `GPVHashAndSign.lean:317,345,383,408`,
and `euf_cma_security` routes around it via `SamplerQuality.idealCorrect` about the *exact* `idealSampler`).
**Lead ruling: spec-divergence (primary) + unsound-statement (contingent).** The reachable signing path emits an
`s₁` inconsistent with verify (behavioral/region divergence); it becomes a false *statement* only when someone tries
to discharge `Correct(falconPSF)` for B2/B3 — which today nobody has. Load-bearing description = eval/verify `s₁`
disagreement, regardless of tag.

**B1 leaf re-confirmation: faithful, no drift.** `FalconTree.leaf (σ₀ σ₁ l01Re l01Im)` (`Primitives.lean:94`);
leaf samples `z₁` at `σ₁`, corrects `b = a·l01`, samples `z₀` at `σ₀` (`:262-284`) — structurally identical to
`ffsampFFTDeepest` (`FFT.lean:356-391`: `leaf_r=√d11·invSigma`, `leaf_l=√d00·invSigma`, `l01_im=−mu_im=conj(g01/g00)`).
Node case (`:285-293`) mirrors `ffsampFFTInner` (`FFT.lean:419-464`). **SD-5's "one sigma, no l01" premise is stale.**

### (2) Findings by severity
- **spec-divergence — TS-5** | `Scheme.lean:155-163,186,240`; `GPVHashAndSign.lean:91-94` | baseline v1.2 Alg 16 /
  FN-DSA-c-fn-dsa M9 (store `s₂`, recompute `s₁=c−s₂·h`) | evidence above; concrete signer mirrors the same
  independent rounding (`Concrete/Sign.lean:177-197`) so it is a faithful transcription of reference *signing* math,
  but the PSF must reconstruct `s₁` from `s₂` to agree with verify | **fix:** `s₁ := c − negacyclicMul s₂ pk.h`,
  thread `pk.h` into `fromFFTPreimage`; B2's `sign` must feed `compress` the same `s₂`.
- **unsound-statement — TS-1** | `Security.lean:109-123`; `Scheme.lean:225` | v1.2 Alg 10/16 | `verify_sign_correct`
  quantifies over `support (sign …)` where `sign:=sorry`; hypothesis neither provably inhabited nor empty; body
  `sorry`; `h_laws` discarded; CONJECTURAL marker present; docstring obligation "(b) eval=c" is the TS-5 defect |
  block on B2 + TS-5 fix.
- **unsound-statement — TS-2** | `Security.lean:300-331,338-364` | [FGdG+25] Thm 1 | body `let _ := …; sorry`
  discards `hSamplerLoss`; free `samplerLoss:ℝ≥0∞` (`:306`) appears additively in the bound (`:326`), trivially met
  with `samplerLoss=⊤`; `bytes40` is a direct specialization, its `2⁻¹⁹³` docstring untethered | tie `samplerLoss`
  into the derivation; discharge via the generic chain.
- **incompleteness — TS-3 / SIGN-1** | `GPVHashAndSign.lean:270,283,332,363` (+wrappers `382-394,407-424`);
  `Scheme.lean:121,225` | GPV08 Prop 6.1-6.2 | four load-bearing GPV sorrys; wrappers are term-mode `exact ⟨…⟩` only
  modulo them; both require `hcorrect` (unmeetable per TS-5); `sign`/`keyGenFromSeed` no body (`signAttempt` IS
  defined, `Scheme.lean:205-211`) | discharge `forgery_yields_collision` (`:332`) first.
- **ok (verified faithful / well-formed):** SD5-1/SD5-2 (B1 leaf+node; *caveat:* producer side unverified —
  `keyGenFromSeed` sorry); TGT-1 (`toFFTTarget` = Alg 10 = `fpolyApplyBasis`, `Scheme.lean:135-143` / `FFT.lean:301-312`);
  SALT-1 (fresh-salt + pk-bound hash = FN-DSA/c-fn-dsa, intended divergence from v1.2; medium conf — `sign` is sorry);
  NORM-1 (L2-only, `betaSquared` 34034726/70265242 = Table 3.3; grep confirms **no** L∞ this session — intended
  divergence from FN-DSA M3/M4); TS-4 (`SamplerQuality` well-formed; finite `HasUniformSamplerLoss` unsatisfiable for
  current `falconPSF` for the TS-5 reason); TS-6 (`ntruPSFCollisionProblem`/`ntruSISProblem` correct data defs).

### (3) Changes vs the §3 table (for refresh)
- **CHANGED (this doc, line 94):** TS-5 ⬆ from "incompleteness (NEW s1) / likely false" → **spec-divergence
  (CONFIRMED s2)**; both s2 audits prove it false-as-constructed and pin the `eval` vs `verify` `s₁` disagreement.
  (Edited in place.)
- **CONFIRMED CLOSED:** SD-5 (≡ §3 "B1 / SD-5 RESOLVED s1") — premise "one sigma, no l01" is stale at `bfcccbda`;
  leaf carries `(σ₀,σ₁,l01)` and matches `ffsampFFTDeepest`. New open follow-up (under B4/SD5-2): prove abstract leaf
  `σ₀,σ₁,l01 = σ/√d00, σ/√d11, conj(g01/g00)` once `keyGenFromSeed` (B2) builds the tree.
- **CLARIFIED (no count change):** UN-1≡TS-1 and UN-2≡TS-2 are now explicitly *also* blocked on the TS-5 redefinition
  (their "eval=c" obligations are unmeetable today), not only on completing the GPV chain (UN-3≡TS-3).
- **NO new sorrys; baseline §4 needs no count edit.** Anchors all still resolve.

### (4) Recommended next entry point on the critical path
**Fix TS-5 before writing any B2.** Order:
1. `Scheme.lean:155-163` — redefine `fromFFTPreimage` to return `(c − negacyclicMul s₂ pk.h, s₂)` with
   `s₂ = −IntPoly.toRq (ifftRound v₁FFT)`; thread `pk.h` in. Makes `eval = c` definitional, reduces `Correct` to
   `isShort`, and aligns the PSF `s₁` with `verify` (`:240`).
2. **Then B2** (`sign` `:225`, `keyGenFromSeed` `:121`) via the PSF loop; return `Signature = (salt, compress s₂)`
   feeding the *same* `s₂`. Pin the σ convention (SIGN-3) at the leaf builder.
3. **Only after:** revisit security — `forgery_yields_collision` (`GPVHashAndSign.lean:332`) is the highest-leverage
   obligation that turns TS-2 from conjectural into a real bound and unblocks finite-loss `SamplerQuality` (TS-4).

Rationale: TS-5 is upstream of TS-1/TS-2/TS-4 and of any meaningful B2 — defining `sign` on the current
`fromFFTPreimage` would bake the eval/verify `s₁` inconsistency into the on-the-wire signing path. The fix is small,
local, baseline-sorry-neutral. (B6/B9 remain parallelizable.)

*Residual uncertainty:* the exact-arithmetic NTRU identity behind TS-5 is reasoning about the reference (confirmed by
both auditors); the *failure under independent rounding* is the load-bearing claim and is unrescuable by any
`Primitives.Laws` field (`Primitives.lean:298-311`). SALT-1 / abstract-`sign` salt-refresh verifiable only via
docstring + concrete signer (`sign` is sorry). SD5-2 producer side gated on B2.

## 4c. Session 2 END synthesis (lead-reviewer report — 2026-06-25, working tree on `bfcccbda`)

**Scope of this report.** §4b above was the Session-2 *START* review, written when TS-5 was still a
*pending defect* (`fromFFTPreimage` returning `(c − round(v₀), −v₁)`). This §4c is the Session-2 *END*
lead-reviewer synthesis: the **TS-5 fix has now landed** in the working tree — `fromFFTPreimage`
(`Scheme.lean:158-164`) returns `(c − negacyclicMul s₂ pk.h, s₂)`, `v₀` is dropped, `s₁` is recomputed
from `s₂`, `falconPSF.trapdoorSample` threads `pk` (`Scheme.lean:188-191`), and a new fully-proven lemma
`falconPSF_eval_trapdoorSample` (`Scheme.lean:202-220`) establishes the **eval-half** of `Correct`.
Two adversarial dimensions (Sign+ffSampling, Theorem-soundness), 18 findings total, **all 18 verdicts
"confirmed", 0 refuted** (one severity-tag reconciliation on TS-5). Independently re-verified this
session: `git rev-parse HEAD` = `bfcccbda…`; the eval-lemma proof body (`Scheme.lean:202-220`); the
20-sorry breakdown (`Scheme` 121/254, `Security` 123/331, `FPRBridge` 82/88/94/100/110, `NTRUSolver`
73/87/89/90/91/93/94/96/98/395/413; `ApproxArith:241` is doc-prose, 257-264 commented); `verify`
recomputes `s₁=c−s₂·h` (`Scheme.lean:269`) matching the new `fromFFTPreimage`; no L∞ anywhere in
`Scheme.lean`; GPV sorrys at `GPVHashAndSign.lean:270/283/332/363`.

### (1) Drift verdict vs recorded baseline of 20 live sorrys — **NO DRIFT**
- **Live Falcon sorrys = 20, unchanged.** Per-file split confirmed this session by direct grep:
  `NTRUSolver` 11 · `FPRBridge` 5 · `Scheme` 2 (`121` keyGenFromSeed, `254` sign) · `Security` 2 (`123`,
  `331`). `ApproxArith.lean:241` is doc text; `:257-264` are commented-out — not live. GPV load-bearing
  sorrys (`GPVHashAndSign.lean:270/283/332/363`) intact. The Session-2 diff **adds a fully-proven lemma
  and modifies defs without adding any sorry**; build is green.
- This resolves the §4b §1 "residual (low)" note: the NTRUSolver-11 / FPRBridge-5 split **was** re-counted
  this session and holds.

**Adversarial verdicts on the five focus questions (all confirmed by both audits):**

1. **Is the eval lemma SOUND — does `eval(trapdoorSample)=c` truly hold, proof valid?** **YES.**
   `eval pk x = x.1 + negacyclicMul x.2 pk.h` (`Scheme.lean:187`); `fromFFTPreimage` returns
   `(c − negacyclicMul s₂ pk.h, s₂)` (`:162-164`); helper `eval_pair` reduces
   `(c − s₂·h) + s₂·h = c` coefficient-wise via `ext i; simp only [coeff_add, coeff_sub]; ring`
   (`:206-214`), where `coeff_add`/`coeff_sub` are correct `@[simp]` lemmas pushing equality to the
   `ZMod q` coefficient ring (`Ring/Kernel.lean:150-152,155-157`). Support extraction
   (`simp [falconPSF, support_bind, support_pure, …]; obtain ⟨z,_,rfl⟩; exact eval_pair _`, `:215-220`)
   is valid because `fromFFTPreimage … z` is **definitionally** `(c − s₂·h, s₂)`. **No sorry, no
   `decide`/`native_decide` shortcut, correct support handling, non-vacuous** (`trapdoorSample` ends in
   `return`, so support is non-empty for any `z ∈ support(ffSampling)`). [F2/TS-1 confirmed]
2. **Is `fromFFTPreimage` still a faithful `s₂ = round(f·z₀+F·z₁)`?** **For `s₂`: yes** —
   `s₂ = −IntPoly.toRq(ifftRound(−(mulFFT z.1 fft(f) + mulFFT z.2 fft(F))))` = `round(f·z₀+F·z₁)`,
   identical to concrete `computeSignature` `s₂ = −rint(v₁)` (`Concrete/Sign.lean:179,193-196`). The
   underlying `ifftRound`/`mulFFT` sign-convention/basis-pairing vs c-fn-dsa@`33026d4d` is uninterpreted
   and not bit-checked here (submodule not retrievable) — confidence medium. [F6/TS-8 confirmed]
3. **Did dropping `v₀` lose anything needed elsewhere?** **Eval-side: nothing** — `s₁` is *defined* to
   make eval hold, so the identity is exact (the whole point of the fix). **One residual divergence:** the
   abstract `isShort`/`pairL2NormSq` (`Scheme.lean:192`) is now computed on the verify-consistent
   `s₁=c−s₂·h`, whereas the concrete signer's norm gate uses an *independently* `rint(v₀)`-based `s₁`
   (`Concrete/Sign.lean:182-191`). These coincide in exact arithmetic but can differ under independent
   coefficient rounding — so the abstract norm quantity and the concrete signer's gate are not
   coefficient-for-coefficient identical. This is **correct for the EUF-CMA/verify identity** and must be
   quantified (or shown irrelevant) only if a future proof links abstract `isShort` to the concrete gate.
   [F6 spec-divergence, confirmed]
4. **Any NEW sorry/unsound?** **No new sorry.** One **new cosmetic style-lint** at `Scheme.lean:209`
   (`show` → `change` recommended) introduced by the eval-lemma proof; does not affect soundness. [TS-7]
5. **Is the isShort-half still NOT claimed?** **Correct — NOT claimed.** Grep confirms
   `falconPSF.Correct` (the eval∧isShort conjunction, `GPVHashAndSign.lean:91-94`) is **never**
   instantiated for Falcon; only the eval-half lemma exists. The docstring (`Scheme.lean:198-201`)
   explicitly states the isShort half is not provable for the raw sampler and needs a rejection/retry
   model. `signAttempt` (`Scheme.lean:234-240`) gates on `isShort` but returns `none` on failure rather
   than retrying — honest separation. **No over-claim.** [F3/TS-1 confirmed]

### (2) Findings by severity (merged audit + verdict)

**spec-divergence**
- **SD-TS5b** (`F6`) — `Scheme.lean:158-164,192,269` ↔ `Concrete/Sign.lean:169-175,182-197`.
  *Baseline:* v1.2 Alg 10 norm check on `(s₁,s₂)=invFFT(s)` vs Alg 16 verify `s₁=c−s₂h`; reference
  `computeSignature` rounds `v₀` independently. *Evidence:* after the TS-5 fix the abstract `s₁=c−s₂·h`
  matches verify exactly, but the concrete signer's squared-norm gate is fed an independently-rounded
  `rint(v₀)`-based `s₁`; the two `isShort` inputs agree only modulo rounding. *Recommendation:* document
  that abstract `isShort`/`pairL2NormSq` is the verify-consistent quantity, not the reference signer's
  gate; if a future correctness proof links them, quantify or dismiss the rounding mismatch.
- **SD-1 / M1** (`F7`) — `Concrete/Sampling.lean:37-44`; `Primitives.lean:145-147`; `Concrete/Sign.lean:233-234`.
  *Baseline:* v1.2 Alg 3 (`r‖m`, no pk) & Alg 10 (salt once). *Evidence:* hash input =
  `salt(40)‖SHAKE256(pk)[0:64]‖0x00 0x00‖msg` (pk-bound, FN-DSA/c-fn-dsa M1) and salt refreshes per
  counter (FN-DSA M2/M8). **Intended** FN-DSA-baseline divergence, not an error; flagged because the
  abstract `sign` docstring labels it "Falcon+" while the body is `sorry` (see IN-1). *Recommendation:*
  state the chosen baseline at the top of the signing modules; verify the `0x00 0x00` empty-context
  framing against FIPS 206 IPD when it is available.

**unsound-statement**
- **UN-1 / TS-2** (`F10`/`TS-2`) — `Security.lean:109-123`; `Scheme.lean:254`. `verify_sign_correct` has a
  `sorry` body and quantifies over `support (Falcon.sign …)` where `sign := sorry`; the statement is about
  an undefined computation and carries no content. ⚠ CONJECTURAL marker present (`:105-108`). The
  eval-half it needs is now available (the new lemma) but the isShort-half and the sign/verify roundtrip
  (compress/decompress, hash recompute) are not. *Recommendation:* give `sign` a real body before stating
  correctness; do not present the eval lemma as discharging this.
- **UN-2 / TS-3** (`F10`/`TS-3`) — `Security.lean:300-331,338-364`. `euf_cma_security` ends
  `let _ := …; sorry`, discarding all hypotheses (incl. `hQ`, `hSamplerLoss`); the conclusion's RHS
  includes a **free caller-supplied** `samplerLoss : ℝ≥0∞` (`:306`) appearing additively (`:326`), so a
  caller may pass `⊤` and the bound is information-free. Does **not** route through the generic
  `euf_cma_split_bound` chain — sorrys directly. `euf_cma_security_bytes40` (`:338`) inherits the vacuity.
  *Recommendation:* prove via the generic split bound and tie `samplerLoss` to `SamplerQuality.bound`
  rather than leaving it as free additive slack.

**incompleteness**
- **IN-1 / B2** (`F1`) — `Scheme.lean:253-254`. **Largest gap in this dimension.** Abstract `sign` is a
  `sorry`; the docstring (`:242-252`) asserts Algorithm-10 / Falcon+ fresh-salt-per-retry with no backing
  code or proof. Only the concrete `concreteSignLoop` (`Concrete/Sign.lean:230-244`) implements a loop.
  The eval lemma and `signAttempt` cover only the single-attempt core. *Recommendation:* implement `sign`
  as the retry over `signAttempt` with fresh `Salt` + `hashToPointForPublicKey` + `compress`, or relabel
  the docstring to stop claiming Alg-10 behavior the body lacks.
- **UN-3 / TS-4** (`TS-4`) — `GPVHashAndSign.lean:266/270, 279/283, 316/332, 344/363`. Four load-bearing
  generic GPV sorrys (`reduction`, `programmedPreimageReduction`, `forgery_yields_collision`,
  `forgery_yields_collision_or_exact_match`). `euf_cma_split_bound`/`euf_cma_collision_bound` (`:407`,
  `:382`) type-check by composition but rest transitively on these sorrys. *Note:* Falcon's
  `euf_cma_security` does not invoke them today (it sorrys directly), so they are load-bearing for the
  *intended* proof, not the current one. *Recommendation:* discharge `reduction` +
  `forgery_yields_collision` (distinct-preimage branch) first.
- **TS-5-residual** (`TS-5`) — `Security.lean:210-237`. `SamplerQuality`/`HasUniformSamplerLoss` are
  **non-vacuous** definitions (the `idealCorrect` field genuinely constrains: one cannot set
  `idealSampler := trapdoorSample` and dodge it, because that would re-demand the unproven isShort-half).
  Defect is only that `euf_cma_security` discards `hSamplerLoss` (UN-2), so this well-formed hypothesis
  currently contributes nothing. `ntruPSFCollisionProblem` (`:150`) samples valid keys (`gen_sound`,
  `HardRelation.lean:30`). *Recommendation:* once UN-2 is proven, consume `hSamplerLoss`; consider adding
  a `SamplerQuality` witness to demonstrate inhabitation.
- **TS-8-residual** (`F8`/`TS-8`) — `s₂` formula faithfulness (sign convention / basis pairing) and the
  intentional L∞ omission are not yet settled against c-fn-dsa@`33026d4d` (submodule unretrievable);
  medium confidence. None of it breaks the eval lemma. *Recommendation:* add a cross-reference comment;
  confirm L∞ omission is intentional (matches v1.2/c-fn-dsa, diverges from FN-DSA M3).

**nit**
- **NIT-1 / TS-7** — `Scheme.lean:209` new `linter.style.show` warning (use `change` not `show`),
  introduced by the eval-lemma proof. Cosmetic. *Recommendation:* replace `show` with `change`.
- **NIT-2 / TS-6** — the new lemma `falconPSF_eval_trapdoorSample` is **orphaned**: grep finds it
  referenced only at its own declaration/docstring (`Scheme.lean:156,202`); no downstream proof consumes
  it (all `Correct`-demanding GPV theorems are sorried). Sound but presently inert — a valid incremental
  step that does not yet move an end-to-end soundness needle. *Recommendation:* wire it toward
  `verify_sign_correct` via a partial `Correct`-eval-half consumer once `sign` has a body.
- **NIT-3 / TS-7** — baseline citation drift: §4 cites GPV sorry *body* lines `270/283/332/363` while the
  build reports *declaration* lines `266/279/316/344`. Same four declarations; normalize the doc.

**ok (verified faithful / well-formed)**
- **eval-lemma** (`F2`/`TS-1`) — proven, sound, non-vacuous, honestly scoped (focus Q1/Q5 above).
- **isShort-half correctly NOT claimed** (`F3`) — no `falconPSF.Correct` instantiation anywhere.
- **B1 leaf+node** (`F4`/`F8`) — `FalconTree.leaf (σ₀ σ₁ l01Re l01Im)` (`Primitives.lean:94`); leaf body
  (`:262-284`) mirrors `ffsampFFTDeepest` (`FFT.lean:356-391`); node (`:285-293`) mirrors `ffsampFFTInner`
  (`FFT.lean:419-462`). **The §3 SD-5 "one sigma, no l01" premise is stale** — re-confirmed. Medium
  confidence on exact σ values / bit-level twiddle equality (gated on the unwritten `keyGenFromSeed` tree
  builder, `Scheme.lean:121`).
- **toFFTTarget** (`F5`) — `Scheme.lean:135-143` = Alg 10 = concrete `fpolyApplyBasis` (`FFT.lean:301-312`);
  `invQ ≈ 1/12289` (not bit-exact-verified).

### (3) Changes vs the §3 table (for refresh)
- **TS-5 (§3 line 102): ⬆ RESOLVED (eval-half).** Was "spec-divergence (CONFIRMED s2) / false-as-constructed".
  The fix landed: `fromFFTPreimage` now returns `(c − s₂·h, s₂)`, `eval(trapdoorSample)=c` is **proven**
  (`falconPSF_eval_trapdoorSample`, `Scheme.lean:202`), and the PSF `s₁` now **agrees** with `verify`
  (`:269`). Mark §3 TS-5 as **RESOLVED (eval-half) s2**; the *remaining* open item is the **isShort-half**
  of `Correct(falconPSF)` (needs the rejection/retry model — B2) plus the new residual SD-TS5b (abstract
  `isShort` vs concrete norm-gate rounding mismatch).
- **NEW finding SD-TS5b** — abstract `isShort`/`pairL2NormSq` (verify-consistent `s₁`) vs the concrete
  signer's `rint(v₀)`-based norm gate diverge under independent rounding. Add to §3 as a spec-divergence
  rider on the (now-resolved) TS-5.
- **UN-1 / UN-2 clarification** — their eval-half obligation is now *available* (no longer blocked on
  TS-5); they remain unsound-as-stated purely because `sign` is `sorry` (UN-1) and the GPV chain +
  discarded hypotheses (UN-2). Update §3 lines 88-89 to drop "blocked on TS-5 redefinition" — only B2 / GPV
  remain.
- **SD-5 (§3 line 87): confirmed CLOSED** — leaf carries `(σ₀,σ₁,l01)`; the stale "one sigma" wording
  should be removed. Follow-up (producer-side σ values) tracked under B2/B4.
- **NEW nits** — NIT-1 (`Scheme.lean:209` show/change lint, a session-2 regression), NIT-3 (GPV
  decl-vs-body line normalization). Neither affects the sorry count.
- **No new sorrys; §4 baseline count needs no edit (still 20 + 4 GPV).** All anchors resolve. Note the §4
  anchor `Scheme.lean:~224 (sign)` is now `Scheme.lean:254`, and `Scheme.lean:~91`/`Primitives.lean:~91`
  for the leaf is `Primitives.lean:94`.

### (4) Recommended next entry point on the critical path
**TS-5 (eval-half) is done; B2 is now unblocked and is the critical path.** Order:
1. **`isShort`-half of `Correct(falconPSF)` + `sign` (B2)** — `Scheme.lean:254`, `:121`. Decide the
   rejection/retry model (fuel-bounded loop vs weakening `Correct` to probabilistic — `ffSampling` can
   emit over-long vectors and `ProbComp` has no retry combinator). Then implement `sign` as the retry over
   `signAttempt` (fresh `Salt`, `hashToPointForPublicKey`, feeding `compress` the same `s₂`), and
   `keyGenFromSeed` (constructive `validKeyPair` witness; real impl gated on B4). This is the prerequisite
   to making UN-1 (`verify_sign_correct`) non-vacuous.
2. **Wire the eval lemma toward `verify_sign_correct`** (close NIT-2's orphan status) once `sign` exists.
3. **Only after:** `forgery_yields_collision` (`GPVHashAndSign.lean:332`) is the highest-leverage GPV
   obligation — it turns UN-2 from conjectural into a real bound and lets `hSamplerLoss`/`SamplerQuality`
   carry weight (TS-5-residual).
4. **Quick wins (parallel):** fix NIT-1 (`show`→`change` at `Scheme.lean:209`); normalize §4 GPV citation
   lines (NIT-3); document the SD-TS5b abstract-vs-concrete `isShort` rounding caveat in `fromFFTPreimage`.

*Residual uncertainty:* (a) `s₂` sign-convention/basis-pairing faithfulness vs c-fn-dsa@`33026d4d` is
uninterpreted and unverifiable locally (submodule not retrievable) — medium confidence on F6/TS-8. (b) B1
leaf σ-value/twiddle bit-equality is gated on the unwritten `keyGenFromSeed` tree builder. (c) abstract
`sign` salt-refresh is verifiable only via docstring + concrete signer while the body is `sorry`. (d) The
SD-TS5b rounding mismatch is benign for the verify identity but unquantified for any future
abstract-`isShort`↔concrete-gate link.

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

- **2026-06-25 — session 2 START (review only, HEAD `bfcccbda`).** Two-dimension adversarial sweep
  (Sign+ffSampling, Theorem-soundness), every finding re-verified against source, 0 refuted (one
  severity-tag revision). **Drift: none** — 20 live Falcon sorrys + 4 GPV load-bearing intact; `sign`/
  `keyGenFromSeed` still `sorry`; B2 un-started. **PRIORITY validated: `Correct(falconPSF)` is false
  as constructed** (TS-5) — `fromFFTPreimage` independently `ifftRound`s `v₀,v₁` so `eval = c−(v₀+v₁·h) ≠ c`
  after rounding, and the PSF `s₁ = c−round(v₀)` disagrees with `verify`'s `s₁ = c−s₂·h` (`Scheme.lean:163`
  vs `:240`). Elevated TS-5 in §3 from "incompleteness/likely-false (s1)" to **spec-divergence (confirmed)**;
  lead ruling spec-divergence-primary + unsound-contingent (`Correct` never instantiated with `falconPSF`).
  **B1 leaf re-confirmed faithful** to `ffsampFFTDeepest` (SD-5 premise stale; closed). No Falcon code edited.
  Residual: NTRUSolver/FPRBridge per-file split not re-counted; producer-side leaf params unverified (B2).
  **Next entry point: fix TS-5 in `fromFFTPreimage` (s₁ := c − s₂·h), THEN B2** (`sign`+`keyGenFromSeed`).

- **2026-06-25 — session 2 END (TS-5 fix + eval lemma; lead-reviewer synthesis §4c).** The TS-5 fix
  landed (`fromFFTPreimage` → `(c − s₂·h, s₂)`, `v₀` dropped, `pk` threaded, `Scheme.lean:158-164,188-191`)
  plus the new fully-proven `falconPSF_eval_trapdoorSample` (`:202-220`). Two-dimension adversarial sweep
  (Sign+ffSampling, Theorem-soundness), **18 findings, all confirmed, 0 refuted**. Re-verified this session:
  HEAD `bfcccbda`; eval-lemma proof sound + non-vacuous (focus Q1); `s₂=round(f·z₀+F·z₁)` faithful (Q2);
  dropping `v₀` loses nothing eval-side but introduces **SD-TS5b** (abstract `isShort` on verify-consistent
  `s₁` vs concrete `rint(v₀)`-based norm gate — agree only mod rounding, Q3); **no new sorry** (Q4) — one
  new style-lint at `Scheme.lean:209` (`show`→`change`); **isShort-half correctly NOT claimed** (Q5).
  **Drift: none** — 20 live Falcon sorrys (per-file split re-counted this session) + 4 GPV intact. §3 TS-5
  ⬆ to **RESOLVED (eval-half)**; SD-5 confirmed closed; UN-1/UN-2 no longer blocked on TS-5 (only B2 / GPV
  chain). New nits: NIT-1 (`:209` lint regression), NIT-2 (eval lemma orphaned), NIT-3 (GPV decl-vs-body
  line normalization). **Next entry point: B2** (`isShort`-half + `sign` `:254` + `keyGenFromSeed` `:121`),
  now unblocked; then `forgery_yields_collision` (`GPVHashAndSign.lean:332`). Residual: `s₂` sign-convention
  vs c-fn-dsa@`33026d4d` uninterpreted (submodule not retrievable); leaf σ-values gated on `keyGenFromSeed`.

- **2026-06-25 — session 3 START + checkpoint (no code change).** Drift clean at `cd82fb3b`. Decisions locked:
  B2 uses a **rejection sampler** realized as a **fuel-bounded `Option`-valued loop** (user choices), mirroring
  `FiatShamir/WithAbort.fsAbortSignLoop` (prior art found this session — resolves the ProbComp totality caveat).
  `sign : … → (maxAttempts : ℕ) → ProbComp (Option Signature)`. Full implementation plan recorded in §2/B2
  (incl. the needed `Rq→IntPoly` centered helper + `verify_sign_correct` restatement). **Implementation
  deferred to a fresh session** to keep context clean (expected multi-iteration build friction from `Rq`'s
  bespoke instances). Next entry point: implement §2/B2 (a)(b)(c).

- **2026-06-25 — session 4 START (review + doc; pre-B2-implementation).** Drift clean at `b9277622`
  (20 live Falcon + 4 GPV + 1 ToMathlib; TS-5 fix + B1 leaf re-confirmed sound). Scoped review pressure-tested
  the B2 plan and surfaced two implementation constraints now folded into §2/B2: **F5** (some-branch not
  compress-success-by-construction ⇒ loop productivity is probabilistic, use `none`-on-exhaustion) and **F7**
  (`sign` must `compress … p.sbytelen` exactly). Refuted a false "Concrete files deleted" alarm (TS-4 →
  path-attribution nit). Next: implement §2/B2 (a)(b)(c).

- **2026-06-25 — session 4 (B2: `sign` implemented).** START: drift clean at `b9277622`; scoped review
  surfaced F5 (productivity probabilistic) + F7 (`compress … p.sbytelen`). Implemented `Falcon.sign`
  (`Scheme.lean:253`) as a fuel-bounded `Option` rejection loop mirroring `fsAbortSignLoop`, plus helper
  `rqToIntPolyCentered` (`:243`); restated `verify_sign_correct` against `some sig ∈ support (sign … maxAttempts)`.
  **The `sign` sorry is resolved — original enquirer goal met.** Live Falcon sorries **20→19**; build green.
  END review (Sign+ffSampling, Encoding, Theorem-soundness): **0 refuted**, confirmed `rqToIntPolyCentered`
  is the exact inverse of `IntPoly.toRq` (via `centeredRepr_intCast`), the loop faithful to M1/M2/M8, no new
  unsoundness, and `verify_sign_correct` now non-vacuous (still `sorry` = incompleteness). Persisting:
  **two-world gap (UN-1/TS-4)** — `Falcon.verify` (byte-level) ≠ the GPV/`falconPSF` verify `euf_cma` targets;
  needs a bridge lemma. Next entry point: **`keyGenFromSeed`** (constructive `validKeyPair` witness) and/or the
  `verify_sign_correct` proof (chain `falconPSF_eval_trapdoorSample` + `compress_decompress` + `isShort`), and
  the two-world bridge lemma. B3a/B6/B9 remain parallelizable.

## 6. Drift-check snippet
The **authoritative** live-`sorry` count is the build warnings (raw `grep` over-counts because comments
now mention "sorry" in prose — see §4). Quick deterministic check:
```bash
cd "$(git rev-parse --show-toplevel)"
git branch --show-current                     # expect falcon-faithfulness-review
# Authoritative live-sorry count (expect 24 = 19 Falcon + 4 GPV + 1 ToMathlib/RenyiDivergence):
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
