# Accepted P5 shared-experiment checkpoint

P5 passed independent review and final evaluation at commit
`fb6f14cb425fa1819401656e6bd8ce80444f0bdd`, tree
`c653ed2df3d888f9e9b0e39a0f7770cdc66452ff`. Together with accepted P4/P6, this
allows canonical migration in independently reviewed units. R5 duplicate-body
delegation, the remaining R6c production reuse families, consumer guidance and
R8 final validation/review remain unfinished. No new numerical bound, security
exponent, changed-policy eligibility, completed refactor or PR is claimed.

## Accepted claims and production proof owners

The namespace below is `SLHDSA.SHAKE128s.Bridge.SharedExperiment`.

| Production source | Accepted claim |
|---|---|
| [Observation.lean](../../../../HashSig/SLHDSA/SHAKE128s/Bridge/SharedExperiment/Observation.lean) | `fullProgram` and `sharedContinuation` retain the actual outcome/raw signing log, five source-cost coordinates and final cache jointly, under the same handler/initial cache and arbitrary continuation. Rejections and final-loss branches remain observed and charged. |
| [Factory.lean](../../../../HashSig/SLHDSA/SHAKE128s/Bridge/SharedExperiment/Factory.lean) | `countedExperiment_pureShakeView_fips205` uses the actual FIPS key-generation free program, with its pair presentation restored and generated-key consistency derived internally. This particular unchanged keygen/sampler case joins the accepted six-witness evidence; separate marginals or a replacement sampler are not assumed. |
| [Wire.lean](../../../../HashSig/SLHDSA/SHAKE128s/Bridge/SharedExperiment/Wire.lean) | `countedExperiment_wire_eq_externalView` and `countedExperiment_wire_run_bind_eq_externalView` give the valid fixed-context full observation and arbitrary-handler/cache/continuation applications, with arbitrary additive policies. |
| [Joint.lean](../../../../HashSig/SLHDSA/SHAKE128s/Bridge/SharedExperiment/Joint.lean) and [Certificates.lean](../../../../HashSig/SLHDSA/SHAKE128s/Bridge/SharedExperiment/Certificates.lean) | `jointExperiment`, `jointBudget`, `lifetime`, `advantage_le_127`, the small-budget zero results, verifier intervals and accepted-outcome work retain their distinct actual experiment/resource premises. |

The 127-bit certificate requires actual joint work bounded with probability one,
`q >= 1`, and probability-one signing count at most `2^64`. Selected work counts
signing attempts, direct hashes and verifier hashes; keygen/signer hashes and
private draws still execute but are excluded from that selected sum. Keygen/signer
hashes remain separate source coordinates. The `q < 569` zero result has no
lifetime/positive-q premise. Supported/accepted verifier bounds retain their own
framing/acceptance conditions. The #766 structural, per-seed, seed-distribution,
randomizer, hedged, weak-seed and sharper minimum regimes remain available without
acquiring #912's lifetime restriction. EUF message freshness and SUF returned-pair
freshness stay distinct. A minimum needs both eligible certificates on the same
event/model/resource meaning; arbitrary additive observation gives no weighted
same-q 127 claim without scalar observation, original-work domination and budget transport.
Changes to keygen, its sampler/order, carriers/providers/seeds or the relevant
observer reopen the affected joint law; this checkpoint proves no arbitrary sampler replacement.

Historical external `Contracts`, `Supplement` and `P5CommonContextBinding` sources
compiled producer-first with default Lean limits and four threads, all with exit 0.
The last source applies both Wire theorems through ordinary production imports;
only its historical contract owner uses `import all`. A fresh flat output root
introduced no partial `HashSig` overlay. These are checked applications, not new
probability proofs or permanent public APIs. Their source hashes are respectively
`4b48e34713d25214de5538ed4894709090526b4cb445430646d673bea91640e8`,
`7d2fadd24d370f05140e2c65c5b5ad015157dd47aa989ed9f9c24d12cb11ca94`, and
`762244d10370928a7bded08783f762543ef94d512c8b15758f277d88e8991f04`.

## Validation and reproduction

The genuine same-clean-head full command below exited 0 in **21:28.74** with
`LEAN_NUM_THREADS=4`. Source/head/tree/index and all eleven clean locked dependencies
were unchanged before/after. The registered runtime actions, 18-row CSV and R0 chain
ran; lint/init/axiom baselines did not increase. The final axiom sweep reported the
existing six sorry-tainted declarations and zero nonstandard-axiom taint, with no new taint.

```sh
LEAN_NUM_THREADS=4 python3 docs/design/slh-dsa-pr766-pr912-evidence/validate-recorded-head.py \
  --report-dir /tmp/vcvio-p5-reproduction -- \
  /usr/bin/time -v ./scripts/validate.sh --lint --test --axioms
```

Run from an owned checkout of the recorded commit with the exact locks and no
concurrent writable-cache builder. Normal imports of the linked production modules
expose the intrinsic proofs; the external flat-contract audit is historical evidence,
not a required downstream interface. Later code changes require their own appropriate
checks and final recorded-head validation.

Lean: `leanprover/lean4:v4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
Manifest SHA-256: `68e3e9f60f635be3e88e676b871b3419004f882626da3ab85523cb2b374da8d2`.

| Locked dependency | Revision |
|---|---|
| mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` |
| PolyFun | `ecac686fd8a3b4763d3df2e738c91947bdec40d6` |
| plausible | `dfa4f38190d07c37e315953e08b90fe2d95b3c24` |
| LeanSearchClient | `d6b4c7be5be75ec4917c873ac50c756dc1436372` |
| importGraph | `a41f0e9a4dea23188ea9cc1c41ac9f8bbafe0b93` |
| proofwidgets | `df72b022e558978a1c50264cfc4d7fec86fa8e04` |
| aesop | `4a174c490d8707121c4a9290800489f105d85e07` |
| Qq | `dce0ad79c486cb1fb504af04f953c3466b0c6db8` |
| batteries | `66e469188fe07963e5cf666c7d4433f45b8131c5` |
| cslib | `5b56df99362532c46e1175381fbbdd755bd56030` |
| Cli | `c24fe6078c630e89b489bffe59b3e20ac30d12c8` |

Audit receipt SHA-256 values identify the original reports without relying on a
temporary workspace path as the proof's meaning:

| Receipt | SHA-256 |
|---|---|
| Final P5 decision | `87891288895a89d42f3f3cf530aa67fca026e5e95f5190e1ba71e641f688adf1` |
| Independent P5 actual closeout | `ded80cd0ce13df8f6926d8a3a217415b65b96b83e50540590cfbe183b3e6b401` |
| Actual three-source application summary | `a524b891d86a764f58c87a416e18ffd8b32df0cd443dac425d6806865a545fe9` |
| Eligibility/particular-keygen/readiness review | `79919e523290899421caa34a1d608feab3ab2d1baaa896a1bf25465ed8d70f4a` |
| Functional six-layer change-impact map | `da4cb3fb337496c87ca302eb347c635f34d31954539ab47bdf5b7a2042a2d48b` |
| Full `validation.json` | `d1340f5215b548369fe3974c63256feec7a769ad45f0fbed80cc43a590a8c053` |
| Full artifact summary | `b66c54b153f2bb5b4a53f0ea8eee86794b2e0285263a56ec76ce5f88e59fbffe` |
| Full `command.log` | `0bcd73f23b9728b41ecaf4e0fc2a9425ed6b2a6a1745df213b3519194e207bbc` |
