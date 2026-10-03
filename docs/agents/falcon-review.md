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
  pk-bound hash path is cross-validated by the FFI differential tests. **Caveat (s13):** the
  `third_party/c-fn-dsa` submodule is **uninitialized in-tree** (`git submodule status` → `-33026d4d…`), so
  `kgen_*.c` byte-faithfulness of the keygen path (`poly_big_to_small` layout, depth-0 buffer, gauss CDT
  tables) is **not source-verifiable here** — it rests on the FFI differential tests, whose keygen-path
  coverage is itself unaudited. Run `git submodule update --init third_party/c-fn-dsa` before the next
  keygen-faithfulness pass (also required for the FFI/test build to compile).
- **Complete?** No — **9 live Falcon sorries** (+4 GPV +1 ToMathlib; **14 total** after s12). `sign` done (s4);
  **`verify_sign_correct` done (s10)**; **KG-quickwin done (s12)** (NTRUSolver 11→2); `keyGenFromSeed` +
  NTRUSolve ascent + EUF-CMA remain.
- **Sound?** Partial — **`verify_sign_correct` PROVEN (s10)**, standard-axioms-only (the abstract correctness
  theorem: a non-aborting signature always verifies, conditional on `h_laws.compress_decompress`).
  `euf_cma_security` + the generic GPV chain are still `sorry`. The pieces built (B1, TS-5,
  `falconPSF_eval_trapdoorSample`, `sign`, B9, **B6 kernel equalities**, **F8**, **VER-1**) were re-audited
  sound at HEAD (could not refute); all standard-axioms-only.
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
- [x] **B2′ `verify_sign_correct`** (s10) — PROVEN, standard-axioms-only. Induction on `maxAttempts`
  (vacuous base; success-vs-retry decomposition via `mem_support_bind_iff`); chains
  `h_laws.compress_decompress` → **F8** `toRq_rqToIntPolyCentered` (proven, `Scheme.lean`) →
  `falconPSF_eval_trapdoorSample` (`s₁=c−s₂·h`) → `isShort` = the `ℓ₂` check. `_hvalid` unused (conditional
  correctness). Stays conditional on the abstract `h_laws.compress_decompress` only (NOT the concrete codec).
- [x] **KG-quickwin** (DONE s12) — replaced `NTRUSolver`'s 9 local stub-`sorry`s (`FXR.sqr`, `vect_*`,
  `poly_big_to_small`) with the real, fully-implemented `Concrete/FXR.lean` + `PolyBigInt.lean` (imports +
  `open Falcon.Concrete.FXR` / `open …PolyBigInt (poly_big_to_small)`; deleted the local `namespace FXR` and
  9 stubs). Removed 9 sorries (NTRUSolver 11→2; **total 23→14**); `check_ortho_norm` now sorry-free
  (`#print axioms` = `propext, Quot.sound` only) and executable (KG-6 vacuity gone). `solve_NTRU` tail
  rewritten for the real 3-arg `poly_big_to_small` (offset→`buf.extract 0 n`/`buf.extract n (2*n)`,
  `Array Int8 × Bool` → `if !ok then none`); `check_ortho_norm` uses `vect_set logn (f.map (·.toInt32))`.
  END adversarial review (s12 + s13): 0 regressions (claims CONFIRMED-OK; the real `fxr_of`
  `j.toInt64.toUInt64 <<< 32` sign-extends correctly on negatives — and IS exercised on the routinely-negative
  NTRU secrets `f,g` via `vect_set ∘ (·.toInt32)`, so it is not "unexercised"; it is bit-identical to the
  deleted `ofInt` stub for the constant 12289 and strictly more correct for negatives). NOT a
  correctness proof — the 2 ascent sorries (`solve_NTRU_intermediate` 365 / `solve_NTRU_depth0` 383 =
  KG-2/KG-3) stay. Standard-axioms-only preserved (no `native_decide`).
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

**Resolved (s10):**
- UN-1/TS-B `verify_sign_correct` — **PROVEN s10** (`Security.lean`, standard-axioms-only); see §2 B2′.
  `_hvalid` unused (conditional correctness). **Two-world gap (TS-4) STILL OPEN:** this is byte-level
  `Falcon.verify`; the GPV verify the EUF-CMA theorems use is a different predicate — no bridge lemma yet.
- F8/ENC-7 `toRq_rqToIntPolyCentered = id` — **PROVEN s10** (`Scheme.lean`, coeff-wise via
  `Poly.ext_get_eq` + `mapCoeffs`/`vectorBackend` reduction + `centeredRepr_intCast.symm`).

**Incompleteness (unfinished, statement sound-in-shape):**
- ENC-1 `compress_decompress` only ever the assumed `h_laws` — no `Primitives.Laws (concretePrimitives)` instance.
- VER-1 (B6 done s7; codecs done s8/s9): **CLOSED** — `concrete_verify_eq_verify` has NO semantic hyps.
  - `hsigDecode` (sig framing round-trip): **PROVEN s8** (`Concrete/Encoding.lean` `sigDecode_sigEncode`,
    standard-axioms-only).
  - `hpkDecode` (14-bit pk pack/unpack round-trip): **PROVEN s9** — `pkDecode_pkEncode` (under `4∣n`) +
    `publicKeyBytes_extract` (unconditional) in `Concrete/Encoding.lean`; standard-axioms-only. The bridge
    drops both `hsigDecode`/`hpkDecode` params and discharges them inline (adds `hn4 : 4 ∣ p.n`).
  - `hn_ovf`: trivially dischargeable numeric bound. Bridge now conditional only on structural/numeric
    side-conditions (`hn`, `hsbytelen`, `hn_ovf`, `hn4 : 4 ∣ p.n`).
- **TB-5 (s13) — verify bridge is LATENT.** `concrete_verify_eq_verify` (`FPRBridge.lean:121-150`) is sorry-free
  and the strongest result in the verify dimension, but `grep` finds it referenced **only in a docstring**
  (`Instance.lean:112`) — no theorem/def/test consumes it, so the integer-only verify guarantee is not yet
  propagated to any end-to-end claim. Fix: wire it into the concrete security/correctness chain (or a
  regression test exercising `hn_ovf`/`hn4`) so it becomes load-bearing.
- **TB-3 (s13 re-confirmed) — FPR precision gap.** The 5 `FPRBridge.lean` sorries (`add/mul/div/sqrt/expm_p63_error`,
  82/88/94/100/110) are consumed **only** by the disabled `HasRealSemantics` instance (`ApproxArith.lean`,
  commented); the live `concrete_verify_eq_verify` is integer-only and does NOT depend on them. They block any
  future sign-side/sampler-quality proof, not verifier-equivalence. Canonical FPR-precision gap (needs a
  verified/axiomatized IEEE-754 model).

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
**KG-quickwin — DONE (s12; verified against live code + END adversarial review):** swapped `NTRUSolver`'s
9 stub-`sorry`s for the real `Concrete/FXR.lean` + `Concrete/PolyBigInt.lean`. NTRUSolver 11→2; **total 23→14**.
`check_ortho_norm` now sorry-free + executable (KG-6 closed); the 2 real ascent sorries
(`solve_NTRU_intermediate` 365 / `solve_NTRU_depth0` 383 = KG-2/KG-3, B4) remain. Standard-axioms-only
(no `native_decide`). What landed:
- Imports `…Concrete.FXR` + `…Concrete.PolyBigInt`; `open Falcon.Concrete.FXR` +
  `open Falcon.Concrete.PolyBigInt (poly_big_to_small)`; deleted the local `namespace FXR` (abbrev +
  `zero/ofInt/add/sqr/lt/ofScaled32`) and the 9 stub defs.
- `solve_NTRU` tail: real `poly_big_to_small (logn)(s : Array UInt32)(lim : Int32) : Array Int8 × Bool`
  reads `s[0:n]`, so `off`→slice: `buf.extract 0 n` / `buf.extract n (2*n)`; pair-return → `if !okF/okG then none`.
  (`buf` holds F at words [0:n], G at [n:2n] — documented depth-0 single-word postcondition, review-confirmed.)
- `check_ortho_norm`: `fxr_zero/fxr_add/fxr_sqr/fxr_lt/fxr_of/fxr_of_scaled32`; `vect_set` wants `Array Int32`
  → `vect_set logn (f.map (·.toInt32))` (Int8→Int32 sign-extends); `vect_invnorm_fft … (0 : UInt64)`.
- KG-4/KG-5 (shadow stubs) **RESOLVED**; KG-6 (`check_ortho_norm` vacuous) **FIXED**. Divergence note
  (s13-corrected): real `fxr_of` (`j.toInt64.toUInt64 <<< 32`, sign-extends) vs the deleted `ofInt` stub
  (`j.toUInt32.toUInt64 <<< 32`) differ only on negative inputs. `fxr_of` IS hit on negatives — `vect_set`
  maps it over the (signed) `f,g` coeffs, and NTRU secrets are routinely negative — so the earlier
  "unexercised negative regime" framing was WRONG; the real impl is simply correct on negatives
  (matches C `(int64_t)j << 32`) and bit-identical to the stub for the positive constant 12289.
- KG-1 `keyGenFromSeed` sorry; KG-2 NTRUSolve ascent sorry; KG-3 no keygen correctness theorem — all still open
  (this was plumbing, NOT `solve_NTRU ⊨ ntruEquation`).
- SZ-2 `concretePrimitives.samplerZ` runs over ℝ (≠ FPR path); SZ-3 5 FPR error bounds `sorry`. TS-F transitive ToMathlib Rényi `sorry`.

**B4 ascent resume plan (s13 bootstrap — validated against live `kgen_ntru.c` @ `33026d4d` + every Lean
helper signature re-checked):** replace the 2 NTRUSolver ascent `sorry`s. Submodule prerequisite DONE
(`git submodule update --init third_party/c-fn-dsa`). C refs (NON-AVX2 only): `solve_NTRU_depth0`
`kgen_ntru.c:1575-1772`, `solve_NTRU_intermediate` `:532-1006`; layout exemplar = local `solve_NTRU_deepest`
(`NTRUSolver.lean:270-327`). **Style:** pure-functional `Id.run do` + `mut` arrays named via
`extractRange`/`writeRange` (NTRUSolver.lean:86-110); FXR arrays are fresh `Array UInt64` (ignore the C's
`uint32_t*`→`fxr*` byte-aliasing); `return none` on failure. `FXR := UInt64`, `mp_mmul`→`SmallPrimeNTT.mp_montymul`.
- **`solve_NTRU_depth0` — s13 ATTEMPT FAILED, reverted to `sorry`.** A full line-by-line port of
  `kgen_ntru.c:1575-1766` was written + compiles, but **fails end-to-end validation** at logn=1: the lift
  leaves `(F,G)` un-reduced (raw coeffs ±2048/±4096 ≫ 127) and/or the internal `f·G−g·F≡q` gate rejects
  (`solved=0` over all 7⁴ small inputs). Safe (gate ⇒ no wrong key escapes) but non-functional. **Bug most
  likely the deeper-(F,G) convention from `solve_NTRU_deepest`** (itself NEVER runtime-validated — succeeds
  476/2401× but its degree-1 output Fd=4·q/Gd=0 for `[1,2]/[0,1]` satisfies no naive scalar relation; 31-bit-limb
  sign-bit-30 vs `poly_mp_set`'s `.toInt32` sign-bit-31 mismatch for negatives is a prime suspect). C driver
  (`kgen_ntru.c:2003`) confirms deepest→depth0 is DIRECT for logn=1 (empty intermediate loop), so the test path
  is faithful. **Full implementation + diagnostics banked in `docs/agents/falcon-ntru-depth0-wip.lean`.**
  **Next step: build the C backend (submodule now init'd) + differential-trace `solve_NTRU_deepest` AND
  `solve_NTRU_depth0` word-for-word on one fixed (f,g) at logn=2 to localise the divergence.** Original plan
  (still valid, all sigs verified s13):
- **`solve_NTRU_depth0` plan — (zero helper gaps, ~90-120 LOC, single-session, all sigs verified s13).**
  `pr := PRIMES[0]` (single prime), `n=1<<<logn`, `hn=n>>>1`. Buf entry: deeper `(F,G)` at `[0:hn]`/`[hn:n]`
  (degree `hn`, single word). Exit: `F=[0:n]`, `G=[n:2n]` single-word (matches `solve_NTRU`'s
  `buf.extract 0 n`/`n (2*n)`). Steps (C lines): A load f,g,Fd,Gd → RNS+NTT (extract Fd/Gd BEFORE
  overwrite; `mp_NTT (logn-1)` for the degree-`hn` Fd/Gd, reusing full `gm`) :1600-1611; B build unreduced
  `(F,G)` butterfly into ft,gt :1613-1625; C name `Fp:=ft,Gp:=gt`, alloc t1..t4 :1627-1640; D
  `t1←F·adj f+G·adj g`, `t3←f·adj f+g·adj g` (note `t4[(n-1)-i]`) :1646-1668; E iNTT t1,t3 + `mp_norm`
  (`.toUInt32`, keep raw) :1670-1679; F FXR division: `rt3[i]=fxr_of_scaled32((t2[i]).toInt32.toInt64.toUInt64<<<22)`,
  `vect_FFT`, `rt2:=rt3.extract 0 hn`, same for t1, `vect_div_selfadj_fft`, `vect_iFFT`, `t1[i]=mp_set (fxr_round …) p`
  :1687-1721; G k→NTT+Mont :1731-1736; H subtract k·f,k·g + **verify `f·G−g·F ≡ q·R` per slot, `return none`
  on mismatch** (compute `x` from the just-`set!` Fp/Gp — ordering!) :1738-1757; I iNTT, `poly_mp_norm`,
  assemble via `writeRange` into `ensureSize buf (6*n)` :1759-1766. Verified sigs: `mp_set(v:Int32)(p)`,
  `mp_NTT/iNTT(logn)(a)(gm)(p p0i)`, `poly_mp_norm/set(logn)(a:Array UInt32)(p)`, `fxr_round:FXR→Int32`,
  `fxr_of_scaled32:UInt64→FXR`, `vect_FFT/iFFT/div_selfadj_fft`, `mkigm logn pr`, `Q=12289` (NTRUSolver.lean:45).
- **`solve_NTRU_intermediate` — LARGER (~200-280 LOC, separate effort).** Multi-prime RNS + CRT + iterative
  Babai loop + save/restore of `(f,g)` via `MIN_SAVE_FG`. Reuses `make_fg_intermediate` (NTRUSolver.lean:241),
  `zint_rebuild_CRT`, `zint_mod_small_signed` (:116), `poly_max_bitlength`/`poly_big_to_fixed`/`poly_sub_scaled`/
  `poly_sub_scaled_ntt` (PolyBigInt), `vect_norm_fft`/`vect_mul_fft`/`divrem31`. **ONE GAP:**
  `poly_sub_kfg_scaled_depth1` (`kgen_poly.c:976-1095`, ~80-120 LOC) — used ONLY in the `depth==1` branch
  (:900-902); port into `PolyBigInt.lean`, or stub `depth==1` first and land `depth>1` (which already has its
  helpers). The `f·G−g·F≡q` verify is SKIPPED for `depth==1` (:943-944).
- **Verify gates:** in-function NTT `q·R` check (the correctness gate, keep as `return none`); `#eval` integer
  round-trip `f·G−g·F=q` in `ℤ[x]/(xⁿ+1)` for small `logn` (no `LatticeCryptoTest` refs NTRUSolver yet);
  escalate to FFI differential vs C `solve_NTRU` once depth0 green. Build `LatticeCrypto.Falcon.Concrete.NTRUSolver`;
  no new `sorry`; standard-axioms preserved. Full plan in the s13 recon transcript.

**Verified-faithful (ok):** params vs Table 3.3 (`betaSquared` 34034726/70265242), centered-rep L2 norm,
RCDT/FACCT/σ constants bit-exact, compress internal unique-encoding checks, headers + 14-bit PK packing,
`toFFTTarget` sign-folding, GS-norm threshold 72251709809335 (v1.2/c-fn-dsa), no `native_decide`/`axiom` in Concrete.

## 4. Baseline — verified 2026-06-30 @ `falcon-faithfulness-review` (s12, KG-quickwin landed; build-warning total 14)
**9 live Falcon sorries** (authoritative = build `declaration uses 'sorry'` warnings, NOT raw `grep` which
over-counts prose/comments). s12 removed 9 NTRUSolver shadow-stub sorries (KG-quickwin; NTRUSolver 11→2):
- `Concrete/NTRUSolver.lean` ×2 (decls `solve_NTRU_intermediate` 365 / `solve_NTRU_depth0` 383 = KG-2/KG-3
  ascent, B4). The 9 stub sorries (`FXR.sqr`, `poly_big_to_small`, 7×`vect_*`) are GONE (real impls imported).
- `Concrete/FPRBridge.lean` ×5 (79,85,91,97,105). `Security.lean` ×1 (351 `euf_cma_security`;
  `verify_sign_correct` PROVEN s10). `Scheme.lean` ×1 (121 `keyGenFromSeed`).
  `ApproxArith.lean` = 0 live (241 prose; 257–264 commented).
- Non-Falcon load-bearing: `GPVHashAndSign.lean` ×4 (270/283/332/363) + `ToMathlib/…/RenyiDivergence.lean:736` ×1.
  **Build-warning total = 14.** (Build reports *decl* lines; older notes cited *token* lines — same decls.)
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

- **s10** — **`verify_sign_correct` PROVEN; F8 PROVEN.** START review GREEN: drift clean (24); independent
  skeptic validated the proof plan (all identity checks — salt, `s₂`, norm arg-order, eval — confirmed;
  `_hvalid` unused; only gap was F8-needs-proving, which was the plan). Correction banked: `verify_sign_correct`
  is ABSTRACT-level — needs only the `h_laws.compress_decompress` law, NOT the concrete codec / ENC-1 refactor.
  Proved **F8** `toRq_rqToIntPolyCentered` (`Scheme.lean`) + **`verify_sign_correct`** (`Security.lean`):
  induction on `maxAttempts` (vacuous base; success-vs-retry via `mem_support_bind_iff`) chaining
  `compress_decompress` → F8 → `falconPSF_eval_trapdoorSample` → `isShort` norm check. Heavy proof delegated
  to a background agent; **adversarially re-verified** at HEAD: `#print axioms` standard-only on both,
  signature UNCHANGED (not weakened/vacuous — success branch does real work), full `LatticeCrypto` build green,
  sorry count **24→23**. Cleaned the `let _ := hvalid` antipattern → `_hvalid` binder + fixed line-length.
  **Next: EUF-CMA (UN-2/UN-3: the generic GPV chain `GPVHashAndSign.lean` ×4 + `euf_cma_security` + the
  TS-4 two-world bridge), or KG (B4/keyGenFromSeed), or KG-quickwin (signature reconciliation).**

- **s11** (checkpoint/bootstrap — NO code) — chose **KG-quickwin** as next (guaranteed sorry reduction +
  makes NTRUSolver executable/differential-testable; de-risks the keygen path; lower risk than the
  multi-session GPV chain). Scoped the reconciliation against live code and banked the full **"KG-quickwin
  resume plan"** in §3. Corrected the doc: `fxr_sqr` DOES exist (FXR.lean:87); real fns are `fxr_`-prefixed;
  all local-`FXR` uses confined to `check_ortho_norm`, `poly_big_to_small` only in `solve_NTRU`; no import
  cycle. **Next session: execute the §3 KG-quickwin resume plan (target 23→14 sorries).**

- **s12** — **KG-quickwin DONE** (executed the §3 resume plan). Imported real `Concrete/FXR.lean` +
  `Concrete/PolyBigInt.lean`, deleted the local `namespace FXR` + 9 stub-sorry defs, rewired `solve_NTRU`
  tail (3-arg `poly_big_to_small`, `off`→`Array.extract`, pair→`if !ok then none`) and `check_ortho_norm`
  (`fxr_*` names, `vect_set ∘ map ·.toInt32`). **23→14 sorries** (NTRUSolver 11→2; only the 2 KG-2/KG-3
  ascent sorries 365/383 left). START drift clean (23, branch live); full `LatticeCrypto` build green;
  `#print axioms`: `check_ortho_norm` now `propext, Quot.sound` only (sorry-free, KG-6 closed, `#eval`
  executable), `solve_NTRU` `sorryAx` only from the 2 ascent sorries; no `native_decide`. END adversarial
  review (3 semantic claims — `buf.extract` offset faithfulness, `Int8→Int32` sign-extension, FXR renames):
  **0 regressions**, all CONFIRMED-OK; real `fxr_of` is correct on the (routinely-negative) NTRU secrets it
  is actually called on, bit-identical to the stub for the positive constant 12289. **Next: EUF-CMA (UN-2/UN-3
  GPV chain + TS-4 two-world bridge), or B4 keyGenFromSeed/ascent.**

- **s13** (END adversarial review of s12 + doc fixes — NO proof code) — ran the harness scoped to
  `KeyGen+NTRUSolve` + `Trust-boundary` (`baseline:14`, `changed=s12`). **No drift** (14 confirmed exactly),
  **no regression, no new spec-divergence, no unsound statement**: s12 plumbing verified faithful by two
  independent audits (9 stubs gone/not shadowed; `check_ortho_norm` axioms re-confirmed `{propext, Quot.sound}`
  two-source; no `native_decide`/new axiom in the FXR/PolyBigInt closure; the 2 remaining sorries are exactly
  the ascent stubs). Acted on the findings: (1) **corrected** the doc's wrong "`fxr_of` unexercised-negative"
  claim (KG-5/N-1 — it IS hit on negative `f,g` via `vect_set`, and is correct there); (2) **fixed** the stale
  `fndsa_native.c` citation → `fndsa.c` in `FFI.lean:22` + `gen_testvectors.c` (N-2); (3) recorded **TB-5**
  (verify bridge `concrete_verify_eq_verify` is sound but LATENT — referenced only in a docstring) and
  re-confirmed **TB-3** (FPR error sorries feed only the disabled `HasRealSemantics`, not the live verifier);
  (4) flagged the **uninitialized `third_party/c-fn-dsa` submodule** as a hard prerequisite. **Then bootstrapped
  B4 ascent** (user picked it): ran `git submodule update --init third_party/c-fn-dsa` (DONE, `33026d4d`
  checked out — `kgen_*.c` now source-visible); recon agent produced + I validated (every helper sig re-checked
  live) the §3 "B4 ascent resume plan" — key finding: `solve_NTRU_depth0` has ZERO helper gaps. **Attempted
  `solve_NTRU_depth0`**: full port written + compiles, but **FAILED end-to-end validation** (lift un-reduced /
  verify-gate reject, `solved=0`; bug most likely `solve_NTRU_deepest`'s deeper-(F,G) convention, which was
  never runtime-validated). **Reverted to `sorry`** (honest — non-functional ≠ done); banked the implementation
  + diagnostics in `docs/agents/falcon-ntru-depth0-wip.lean`. Count back to **14**. **Next: differential-trace
  `solve_NTRU_deepest`+`solve_NTRU_depth0` vs the C backend (now buildable) on a fixed (f,g) at logn=2 to
  localise the divergence; then fix depth0 from the WIP file; then `solve_NTRU_intermediate`.**

## 6. Drift-check snippet
```bash
cd "$(git rev-parse --show-toplevel)"
git branch --show-current      # expect falcon-faithfulness-review (verify LIVE)
# Authoritative live-sorry count (expect 14 = 9 Falcon + 4 GPV + 1 ToMathlib/RenyiDivergence, since s12):
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
