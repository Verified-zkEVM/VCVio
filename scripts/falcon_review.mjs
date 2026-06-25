// Falcon faithfulness/soundness adversarial-review harness (Claude Code Workflow).
// Re-runnable bookend for the bootstrapped sessions described in docs/agents/falcon-review.md.
//
// Run:  Workflow scriptPath=scripts/falcon_review.mjs args={...}
// args (all optional):
//   dimensions : string[]  subset of dimension keys to review (default: all 9)
//   full       : boolean   re-fetch FN-DSA + c-fn-dsa sources from the web (default: false → use embedded briefs)
//   changed    : string    summary of what changed this session → focuses verifiers on regressions
//   baseline   : number    expected live-sorry count in LatticeCrypto/Falcon/ (default: 20) — drift flag
//
// READ-ONLY by contract: agents must not edit files. Output is a severity-ranked markdown report.

export const meta = {
  name: 'falcon-review',
  description: 'Bootstrapped adversarial faithfulness/soundness review of LatticeCrypto/Falcon (three baselines; read-only)',
  phases: [
    { title: 'Sources', detail: 'Optional: re-fetch FN-DSA (FIPS 206) + c-fn-dsa briefs (full mode only)' },
    { title: 'Audit', detail: 'Per-dimension three-way faithfulness + soundness audit' },
    { title: 'Verify', detail: 'Adversarially refute each finding' },
    { title: 'Synthesize', detail: 'Severity-ranked report + drift verdict vs recorded baseline' },
  ],
}

// Robust against the runtime delivering `args` as a JSON string vs an object.
let A = args
if (typeof A === 'string') { try { A = JSON.parse(A) } catch (_e) { A = {} } }
if (typeof A !== 'object' || A === null) A = {}
const FULL = A.full === true
const BASELINE = typeof A.baseline === 'number' ? A.baseline : 20
const CHANGED = typeof A.changed === 'string' && A.changed.length ? A.changed : ''

const READONLY = `STRICT RULES: READ-ONLY review. Do NOT edit/write/fix any file. Only Read/Grep/Glob/Bash(read-only)/WebFetch/WebSearch. Cite every claim with file:line or a precise spec reference. NEVER assert "correct"/"faithful" without evidence; if unverifiable, mark confidence "low" and say what is missing. Severity: bytes-on-the-wire or security-region change ⇒ "spec-divergence"; a theorem that proves nothing / is vacuous / is about a sorry ⇒ "unsound-statement"; unfinished proof/def ⇒ "incompleteness"; cosmetic/doc ⇒ "nit"; verified-faithful ⇒ "ok".`

const DRIFT = `RECORDED BASELINE (docs/agents/falcon-review.md §4): ${BASELINE} live sorrys in LatticeCrypto/Falcon/ (NTRUSolver 11, FPRBridge 5, Scheme 2, Security 2; ApproxArith 5 = comment-only); generic load-bearing sorrys at GPVHashAndSign.lean:270,283,332,363. If your reading deviates, raise a finding "drift" (severity per impact) noting the new file:line.`

const FALCON_V12 = `=== FALCON v1.2 SPEC FACTS (validated from the spec PDF; ONE of three baselines) ===
PARAMS (Table 3.3): q=12289. F-512: n=512, sigma=165.736617183, sigma_min=1.277833697, floor(beta^2)=34034726, pk=897B, sig total=666B. F-1024: n=1024, sigma=168.388571447, sigma_min=1.298280334, floor(beta^2)=70265242, pk=1793B, sig=1280B. sigma_max=1.8205.
HASHTOPOINT (Alg 3): SHAKE256-Init; Inject(str=r||m, NO pk in v1.2); loop i<n: t=Extract16 big-endian; if t<k*q(=61445): c_i=t mod q, i++.
SIGN (Alg 10): r<-{0,1}^320 ONCE; c=HashToPoint(r||m); t=(-(1/q)FFT(c)*FFT(F),(1/q)FFT(c)*FFT(f)); do{do{z=ffSampling(t,T);s=(t-z)B_hat}while ||s||^2>floor(beta^2);(s1,s2)=invFFT(s);s=Compress(s2,8*sbytelen-328)}while s==BOTTOM. v1.2 does NOT refresh salt across retries.
FFSAMPLING (Alg 11): base n=1: sigma_lvl=T.value; z0=SamplerZ(t0,sigma_lvl); z1=SamplerZ(t1,sigma_lvl) (t0,t1 real scalars). node: split t1, recurse right, merge->z1; t0'=t0+(t1-z1)*ell; split t0', recurse left, merge->z0.
VERIFY (Alg 16): c=HashToPoint(r||m); s2=Decompress; if BOTTOM reject; s1=c-s2*h normalized [-q/2,q/2]; accept iff ||(s1,s2)||^2<=floor(beta^2).
SAMPLERZ (Alg 12-15): BaseSampler RCDT (Table 3.1, 19 entries, 2^72); ApproxExp poly C[] (13 consts); SamplerZ: r=mu-floor(mu); ccs=sigma_min/sigma'; z0=BaseSampler; b=UniformBits(8)&1; z=b+(2b-1)z0; x=(z-r)^2/(2sigma'^2)-z0^2/(2sigma_max^2); if BerExp(x,ccs)=1 return z+floor(mu). RCDT base sampler is only Renyi-close to ideal (1+2^-78), NOT exact.
KEYGEN (Alg 4-9): NTRUGen f,g~D_{1.17sqrt(q/2n)}; reject unless NTT(f) nonzero and gamma<=1.17sqrt(q). NTRUSolve recursion via field norm; fG-gF=q. Tree: ffLDL*/LDL*; normalize leaf<-sigma/sqrt(leaf).
ENCODING (Alg 17-18): Compress s2: sign bit + 7 low bits + unary high bits; unique-encoding checks (fixed bitlen 8*sbytelen-328, reject neg-zero, trailing zero). PK header 0000nnnn, 14 bits/coeff, ceil(14n/8)B. SIG header 0cc1nnnn + 40B nonce.`

// Embedded source briefs (validated 2026-06-25; the spec-of-record matrix M1-M9).
// In FULL mode these are replaced by fresh web fetches.
const EMBEDDED_SOURCES = `=== FN-DSA / c-fn-dsa DELTAS (spec-of-record matrix M1-M9; embedded baseline) ===
M1 HashToPoint: FN-DSA/c-fn-dsa bind pk -> nonce(40)||SHAKE256(vk)[0:64]||0x00||len(ctx)||ctx||msg (raw mode ctx empty -> 0x00 0x00). Diverges from v1.2 (r||m).
M2 Salt: FN-DSA/c-fn-dsa fresh nonce per retry (v1.2: once).
M3 Norm: FN-DSA adds an L-infinity bound on top of L2; v1.2 and c-fn-dsa are L2-only. [L∞ value: confirm vs FIPS 206 IPD]
M4 Leaf gate: FN-DSA gates LDL leaf stddev to [sigma_min,sigma_max] (BOTTOM otherwise); v1.2/c-fn-dsa do not.
M5 Base sampler: FN-DSA 79 bits/coeff (reuse sign byte); v1.2/c-fn-dsa 72 bits/coeff. [from unfrozen NIST slides — confirm vs IPD]
M6 Sig header: all three -> 0x30+logn.
M7 GS-norm threshold: FN-DSA applies a 0.9999 factor to 1.17sqrt(q); v1.2/c-fn-dsa use 1.17sqrt(q) (fixed-pt 72251709809335). [confirm vs IPD]
M8 Sign loop: FN-DSA/c-fn-dsa single retry loop with fresh nonce (v1.2 nested do-while, fixed salt).
M9 Verify: all three integer-only.
c-fn-dsa = github.com/pornin/c-fn-dsa @ 33026d4d (submodule under third_party/, may be uncheckedout locally).`

const FINDING_SCHEMA = {
  type: 'object', additionalProperties: false,
  properties: {
    dimension: { type: 'string' },
    summary: { type: 'string' },
    findings: { type: 'array', items: {
      type: 'object', additionalProperties: false,
      properties: {
        id: { type: 'string' },
        title: { type: 'string' },
        severity: { type: 'string', enum: ['spec-divergence', 'unsound-statement', 'incompleteness', 'nit', 'ok'] },
        confidence: { type: 'string', enum: ['high', 'medium', 'low'] },
        detail: { type: 'string' },
        spec_citation: { type: 'string' },
        code_citation: { type: 'string' },
        recommendation: { type: 'string' },
      },
      required: ['id', 'title', 'severity', 'confidence', 'detail', 'code_citation', 'recommendation'],
    } },
  },
  required: ['dimension', 'summary', 'findings'],
}

const VERDICT_SCHEMA = {
  type: 'object', additionalProperties: false,
  properties: { verdicts: { type: 'array', items: {
    type: 'object', additionalProperties: false,
    properties: {
      id: { type: 'string' },
      verdict: { type: 'string', enum: ['confirmed', 'refuted', 'revised', 'uncertain'] },
      corrected_severity: { type: 'string', enum: ['spec-divergence', 'unsound-statement', 'incompleteness', 'nit', 'ok'] },
      reasoning: { type: 'string' },
      evidence_citation: { type: 'string' },
    },
    required: ['id', 'verdict', 'corrected_severity', 'reasoning'],
  } } },
  required: ['verdicts'],
}

const DIMENSIONS = [
  { key: 'HashToPoint', files: 'Concrete/Sampling.lean; Primitives.lean:88-137; Concrete/Instance.lean; FFI/Hashing.lean; csrc/falcon/lean_falcon_ffi.c', focus: 'pk-binding & absorb order (salt, SHAKE256(pk,64), 0x00 0x00, msg); big-endian 16-bit; reject>=61445; mod q; whether hashToPoint_welldefined (Primitives.lean:287) is vacuous.' },
  { key: 'Verify', files: 'Scheme.lean:227-241; Arithmetic.lean (norms, centering); Concrete/Instance.lean (concreteVerify, negacyclicMulU32, pairL2NormSqU32); Concrete/FPRBridge.lean (concrete_verify_eq_verify)', focus: 'Alg 16 control flow; CENTERED-rep L2 norm; betaSquared; whether concrete_verify_eq_verify is complete or conditional; whether U32 kernels are proven equal to abstract.' },
  { key: 'Sign+ffSampling', files: 'Scheme.lean:112-225 (sign, signAttempt, toFFTTarget, falconPSF); Primitives.lean:125-275 (ffSampling, splitFFT, mergeFFT); Concrete/Sign.lean; Concrete/FFT.lean:340-440', focus: 'sign sorry (Scheme.lean:225); CRITICAL SD-5: abstract ffSampling leaf (Primitives.lean:251-264, one sigma, no l01) vs concrete ffsampFFTDeepest (FFT.lean:356-391, two stddevs + l01 correction); toFFTTarget vs Alg 10; salt-refresh; loop shape.' },
  { key: 'KeyGen+NTRUSolve', files: 'Scheme.lean:112-121 (keyGenFromSeed, validKeyPair, ntruEquation); Concrete/KeyGen.lean; Concrete/NTRUSolver.lean; Concrete/{PolyBigInt,BigInt31,SmallPrimeNTT}.lean', focus: 'keyGenFromSeed sorry; NTRUSolver sorrys (FXR.sqr:73, vect_* :86-98, solve_NTRU_intermediate:395, solve_NTRU_depth0:413); is poly_big_to_small shadowed; any proof of fG-gF=q or gamma bound.' },
  { key: 'SamplerZ', files: 'Concrete/SamplerZ.lean; Concrete/FPR.lean; Concrete/FloatLike.lean; DiscreteGaussian.lean; Primitives.lean:281-283 (samplerZ_correct); Concrete/Instance.lean:108-200', focus: 'RCDT/FACCT constants vs Table 3.1; whether samplerZ_correct (EXACT PMF) is satisfiable given RCDT is only Renyi-close; concretePrimitives.samplerZ runs over R not FPR; sigma vs 1/sigma convention; KAT coverage.' },
  { key: 'Encoding', files: 'Falcon/Encoding.lean; Concrete/Encoding.lean; Primitives.lean:111-117,288-292', focus: 'Compress/Decompress (Alg 17-18) bit layout + unique-encoding checks; PK 14-bit/coeff; SIG header; whether compress_decompress + Encoding.Laws are proven; sbytelen budget 8*625=5000=8*666-328.' },
  { key: 'Parameters', files: 'Falcon/Params.lean; Falcon/Arithmetic.lean', focus: 'every numeric vs Table 3.3; sbytelen naming (s2-only vs total); sigma_max presence; fftDepth=logn-1 consistency with the ffSampling base case.' },
  { key: 'Theorem-soundness', files: 'Security.lean (verify_sign_correct:119, euf_cma_security:321, ntruSISProblem, ntruPSFCollisionProblem, SamplerQuality, HasUniformSamplerLoss); VCVio/CryptoFoundations/GPVHashAndSign.lean (Correct:91, reductions:270/283, forgery lemmas:332/363, euf_cma_split_bound:407); Primitives.lean (Laws); Scheme.lean (falconPSF)', focus: 'soundness OF STATEMENTS: proven / sorry / vacuous / mis-stated. verify_sign_correct over support of sorried sign; euf_cma_security discards hyps; which GPV sorrys are load-bearing; is Correct falconPSF provable given SD-5; SamplerQuality non-vacuous.' },
  { key: 'Trust-boundary', files: 'Concrete/FFI.lean; csrc/falcon/*.c; Concrete/FPR.lean; Concrete/ApproxArith.lean; Concrete/FPRBridge.lean:82,88,94,100,110', focus: 'TCB map: 6 @[extern] FFI; SHAKE256; Float.ofBits/toRat0; the 5 FPR error-bound sorrys + disabled HasRealSemantics instance; whether bridges silently depend on these; any native_decide.' },
]

const want = Array.isArray(A.dimensions) && A.dimensions.length
  ? DIMENSIONS.filter((d) => A.dimensions.includes(d.key))
  : DIMENSIONS

// ---- Phase 1: sources ----
let SOURCES = EMBEDDED_SOURCES
if (FULL) {
  phase('Sources')
  const [fn, cf] = await parallel([
    () => agent(`Re-fetch FN-DSA / FIPS 206 facts for a Falcon review and report DELTAS vs Falcon v1.2.\n\n${FALCON_V12}\n\nUse WebSearch/WebFetch (load via ToolSearch). Confirm or correct each of these embedded claims, citing URLs and the document version:\n${EMBEDDED_SOURCES}\nFlag any item you cannot confirm against the published FIPS 206 IPD (esp. M3 L-infinity value, M5 79-bit, M7 0.9999). Do NOT edit files.`, { label: 'src:fn-dsa', phase: 'Sources' }),
    () => agent(`Re-confirm c-fn-dsa reference behavior (github.com/pornin/c-fn-dsa @ 33026d4d) for a Falcon review. First check local: ls third_party, read csrc/falcon/*.c. Then verify hash_to_point byte layout, sign retry/salt, sampler bit budget, verify norm, encoding against the embedded matrix:\n${EMBEDDED_SOURCES}\nCite file:line or URL. Do NOT edit files.`, { label: 'src:c-fn-dsa', phase: 'Sources' }),
  ])
  SOURCES = `=== FN-DSA (refetched) ===\n${fn || '(unavailable)'}\n\n=== c-fn-dsa (refetched) ===\n${cf || '(unavailable)'}`
}

const REGRESS = CHANGED
  ? `\nTHIS SESSION CHANGED: ${CHANGED}\nPrioritise regressions in/around that change: new sorrys, newly-vacuous or unsound statements, previously-faithful behavior now broken, drifted citations.`
  : ''

// ---- Phase 2+3: audit -> adversarial verify ----
phase('Audit')
const results = await pipeline(
  want,
  (d) => agent(`${READONLY}\n\nAudit ONE dimension of LatticeCrypto/Falcon (Lean 4) for a THREE-WAY (Falcon v1.2 / FN-DSA-FIPS206 / Falcon+ c-fn-dsa) faithfulness + soundness review. State which baseline(s) each finding diverges from; no single authoritative spec.\n\nDIMENSION: ${d.key}\nFILES (all paths under LatticeCrypto/Falcon/ unless rooted; read fully, grep for more): ${d.files}\nFOCUS: ${d.focus}\n\n${DRIFT}${REGRESS}\n\n${FALCON_V12}\n\n${SOURCES}\n\nRead the files, validate numbers/layouts by reading them (not assuming), compare to all three baselines. Include "ok" findings you positively verified. Return via StructuredOutput.`, { label: `audit:${d.key}`, phase: 'Audit', schema: FINDING_SCHEMA }),
  (audit, d) => {
    if (!audit || !audit.findings || audit.findings.length === 0) return audit
    return agent(`${READONLY}\n\nADVERSARIAL VERIFIER for the "${d.key}" dimension. Try to REFUTE each finding by re-reading the cited file:line yourself (do not trust the auditor's quote). Default to skepticism; downgrade inflated severities; confirm correct ones. Three baselines apply.${REGRESS}\n\n${FALCON_V12}\n\n${SOURCES}\n\nFINDINGS (JSON):\n${JSON.stringify(audit.findings, null, 2)}\n\nReturn a verdict per id via StructuredOutput.`, { label: `verify:${d.key}`, phase: 'Verify', schema: VERDICT_SCHEMA })
      .then((v) => ({ dimension: d.key, audit, verdicts: (v && v.verdicts) || [] }))
  },
)

const clean = results.filter(Boolean).map((r) => (r && r.audit) ? r : { dimension: (r && r.dimension) || 'unknown', audit: r, verdicts: [] })

// ---- Phase 4: synthesize ----
phase('Synthesize')
const report = await agent(`${READONLY}\n\nLead reviewer: synthesize the per-dimension audits + adversarial verdicts into ONE severity-ranked markdown report for the bootstrapped Falcon review (docs/agents/falcon-review.md). Merge each finding with its verdict; drop/downgrade refuted ones. Sections: (1) drift verdict vs recorded baseline of ${BASELINE} live sorrys${CHANGED ? ` (this session changed: ${CHANGED})` : ''}; (2) findings by severity (spec-divergence / unsound-statement / incompleteness / nit) each with id, file:line, baseline, evidence, recommendation; (3) what changed vs the doc's §3 table (new/closed/moved findings) so the doc can be refreshed; (4) recommended next entry point on the critical path. Cite file:line. Flag residual uncertainty.\n\nDATA (JSON):\n${JSON.stringify(clean, null, 2)}`, { label: 'synthesize', phase: 'Synthesize' })

return {
  report,
  mode: { full: FULL, baseline: BASELINE, dimensions: want.map((d) => d.key), changed: CHANGED || null },
  perDimension: clean.map((c) => ({ dimension: c.dimension, findings: (c.audit && c.audit.findings && c.audit.findings.length) || 0 })),
}
