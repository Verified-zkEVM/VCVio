/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/
import LatticeCrypto.Falcon.Security
import LatticeCrypto.Falcon.Concrete.Instance

/-!
# Falcon EUF-CMA: non-vacuity witness

`Falcon.euf_cma_security` is a conditional theorem.  Its hypotheses bundle the GPV laws on
honestly generated keys (`hCorrect`/`hReg`/`hNeverFail`), the shared deterministic `eval`/`isShort`
of the ideal and concrete PSFs (`hEval`/`hShort`), and a finite-precision transport hypothesis
(`hTransport`).  A conditional theorem asserts nothing if its hypotheses are jointly
uninhabitable; this file rules that out with a concrete, **genuine valid-key** instance for which
every hypothesis holds simultaneously, so the headline bound is not vacuous.

The witness uses the degree-one parameter set `n = 1` with a huge squared-norm bound
`betaSquared = 2 · ⌊q/2⌋² = 75497472`, so the verifier's shortness predicate accepts every pair
`(s₁, s₂) ∈ R_q²`.  The ideal PSF shares Falcon's deterministic `eval`/`isShort` and uses the
trapdoor sampler `trapdoorSample _ _ c := pure (c, 0)`.  The honest key relation `toyHr` generates a
single genuinely valid NTRU key (`f = 1`, `g = 0`, `F = 0`, `G = q`, `h = 0`), discharging
`validKeyPair` from the bridge `intPolyMul = negacyclicMulPure` at `n = 1`.  The transport
adversary `toyAdv'` queries the random oracle once at the fixed point `((), [])` and forges there,
witnessing `ForgesQueriedPoint` and `signHashQueryBound 0 1`; the advantage bound holds with
`samplerLoss = 1` since every advantage is a probability `≤ 1`.

* `toy_validKeyPair` — the single generated key pair is genuinely NTRU-valid.
* `toy_isShort` / `toy_eval_pair_zero` — the shared `isShort`/`eval` facts (`hShort`/`hEval`).
* `toy_correctAt` / `toy_hReg` / `toy_neverFail` — the GPV laws on honest keys.
* `toy_ForgesQueriedPoint` / `toy_signHashQueryBound` / `toy_advantage_bound` — the transport data.
* `falcon_eufcma_hyps_inhabited` — all hypotheses hold for the single instance.
-/

open OracleComp OracleSpec Falcon LatticeCrypto

namespace Examples.FalconNonVacuity

/-! ## Degree-one parameters, primitives, and the negacyclic-multiplication bridge -/

/-- Toy Falcon parameters: ring degree `n = 1`, with a squared-norm bound large enough that the
verifier's shortness predicate accepts every pair `(s₁, s₂) ∈ R_q²`.  Concretely
`betaSquared = 2 · ⌊q/2⌋² = 2 · 6144² = 75497472`. -/
noncomputable def toyP : Params :=
  { n := 1, sigma := 0, sigmaMin := 0, betaSquared := 75497472, sbytelen := 0 }

/-- A concrete primitive bundle at `toyP` (only used to type the Falcon PSF; its sampler
fields are never executed by the witness). -/
noncomputable def toyPrims : Primitives toyP :=
  Falcon.Concrete.concretePrimitives toyP (by decide)

/-- The imperative reference multiplier `schoolbookNegacyclicMul` agrees with the proof-level
`negacyclicMulPure` on the degree-one integer ring. -/
theorem schoolbook_eq_pure_n1 (f g : Poly ℤ 1) :
    schoolbookNegacyclicMul (vectorKernel ℤ 1) f g =
      negacyclicMulPure (vectorKernel ℤ 1) f g := by
  apply Poly.ext_get_eq
  intro i
  fin_cases i
  simp only [schoolbookNegacyclicMul, Id.run, negacyclicMulPure]
  simp only [Vector.get, vectorBackend, Fin.val_cast, Fin.val_eq_zero, Vector.getElem_toArray,
    Array.replicate_one, Order.lt_one_iff, Nat.add_eq_zero_iff, Array.getD_eq_getD_getElem?,
    vectorKernel, Vector.getElem?_toArray, Array.set!_eq_setIfInBounds, bind_pure_comp, map_pure,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, tsub_zero, Nat.reduceAdd,
    Nat.add_one_sub_one, Nat.div_self, List.range'_one, List.forIn_cons, and_true, add_zero,
    getElem?_pos, Option.getD_some, List.forIn_nil, map_bind, ↓reduceIte, Nat.mod_succ,
    List.size_toArray, List.length_cons, List.length_nil, zero_add, List.getElem_toArray,
    List.getElem_cons_zero, List.setIfInBounds_toArray, List.set_cons_zero, pure_bind, Fin.zero_eta,
    Fin.isValue, negacyclicConvCoeff, Vector.toArray_ofFn, Array.getElem_ofFn]
  change f[0] * g[0] = _
  have h : (∑ _x : Fin 1 × Fin 1, f[0] * g[0]) = f[0] * g[0] := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]; simp
  exact h.symm

/-- Falcon's integer-polynomial multiplication coincides with `negacyclicMulPure` at `n = 1`. -/
theorem intPolyMul_eq_pure (a b : IntPoly 1) :
    intPolyMul a b = negacyclicMulPure (vectorKernel ℤ 1) a b := by
  unfold intPolyMul
  simp only [integralLift, vectorIntegralLift]
  exact schoolbook_eq_pure_n1 a b

/-- The single coefficient of a degree-one negacyclic product is the product of coefficients. -/
theorem negacyclicMulPure_get_n1 (a b : Poly ℤ 1) :
    (negacyclicMulPure (vectorKernel ℤ 1) a b).get 0 = a.get 0 * b.get 0 := by
  have hc := negacyclicMulPure_coeff (vectorKernel ℤ 1) a b (0 : Fin 1)
  simp only [vectorBackend, vectorKernel] at hc ⊢
  rw [hc]
  unfold negacyclicConvCoeff
  rw [Fintype.sum_prod_type, Fin.sum_univ_one, Fin.sum_univ_one]
  simp

/-- The single coefficient of a constant integer polynomial at `n = 1`. -/
theorem intPolyConst_get_n1 (c : ℤ) : (intPolyConst (n := 1) c).get 0 = c := by
  unfold intPolyConst
  simp [integralLift, vectorIntegralLift, constPoly, Vector.get]

/-- The single coefficient of a degree-one polynomial difference. -/
theorem poly_sub_get_n1 (a b : Poly ℤ 1) : (a - b).get 0 = a.get 0 - b.get 0 := by
  change (a - b)[0]'(by norm_num) = a[0]'(by norm_num) - b[0]'(by norm_num)
  exact Vector.getElem_sub a b 0 (by norm_num)

/-- The product of two constant integer polynomials at `n = 1`. -/
theorem intPolyMul_const_const (a b : ℤ) :
    intPolyMul (intPolyConst (n := 1) a) (intPolyConst b) = intPolyConst (a * b) := by
  apply Poly.ext_get_eq
  intro i
  rw [Subsingleton.elim i 0]
  rw [intPolyMul_eq_pure, negacyclicMulPure_get_n1, intPolyConst_get_n1, intPolyConst_get_n1,
    intPolyConst_get_n1]

/-- Reducing the constant integer polynomial `0` modulo `q` gives `0` in `R_q`. -/
theorem toRq_intPolyConst_zero : (IntPoly.toRq (intPolyConst (n := 1) (0 : ℤ)) : Rq 1) = 0 := by
  apply Poly.ext_get_eq
  intro i
  fin_cases i
  simp only [IntPoly.toRq, integralLift, vectorIntegralLift, intPolyConst, constPoly,
    PolyBackend.mapCoeffs, vectorBackend, Vector.get]
  exact (Poly.get_zero (n := 1) ⟨0, by norm_num⟩).symm

/-- Left multiplication by `0` in `R_q` is `0`. -/
theorem negacyclicMul_zero_left {n : ℕ} (h : Rq n) : negacyclicMul (0 : Rq n) h = 0 := by
  apply Poly.ext_get_eq
  intro i
  have hc := negacyclicMulPure_coeff (vectorKernel (ZMod modulus) n) (0 : Rq n) h i
  simp only [vectorBackend] at hc
  refine hc.trans ?_
  unfold negacyclicConvCoeff
  have hz : ∀ j : Fin n, Vector.get (0 : Rq n) j = 0 := fun j => Poly.get_zero j
  rw [hz i]
  apply Finset.sum_eq_zero
  intro x _
  dsimp only
  rw [hz x.1, zero_mul, neg_zero, ite_self, ite_self]

/-- Right multiplication by `0` in `R_q` is `0`. -/
theorem negacyclicMul_zero_right {n : ℕ} (a : Rq n) : negacyclicMul a (0 : Rq n) = 0 := by
  apply Poly.ext_get_eq
  intro i
  have hc := negacyclicMulPure_coeff (vectorKernel (ZMod modulus) n) a (0 : Rq n) i
  simp only [vectorBackend] at hc
  refine hc.trans ?_
  unfold negacyclicConvCoeff
  have hz : ∀ j : Fin n, Vector.get (0 : Rq n) j = 0 := fun j => Poly.get_zero j
  rw [hz i]
  apply Finset.sum_eq_zero
  intro x _
  dsimp only
  rw [hz x.2, mul_zero, neg_zero, ite_self, ite_self]

/-! ## The honest key, the ideal PSF, and the GPV laws -/

/-- The honest public key `h = 0`. -/
noncomputable def toyPk : PublicKey toyP := { h := 0 }

/-- The (trivial) Falcon tree at FFT depth `0`. -/
noncomputable def toyTree : FalconTree toyP.fftDepth := by
  rw [show toyP.fftDepth = 0 from rfl]; exact FalconTree.leaf 0

/-- The honest secret key: the genuinely NTRU-valid basis `(f, g, F, G) = (1, 0, 0, q)`. -/
noncomputable def toySk : SecretKey toyP :=
  { f := intPolyConst 1, g := intPolyConst 0, capF := intPolyConst 0,
    capG := intPolyConst (modulus : ℤ), tree := toyTree }

/-- The generated key pair is genuinely NTRU-valid: `fG − gF = q` and `f · h = g` in `R_q`. -/
theorem toy_validKeyPair : validKeyPair toyP toyPk toySk = true := by
  rw [validKeyPair_eq_true_iff]
  refine ⟨?_, ?_⟩
  · change (intPolyMul (intPolyConst (n := 1) 1) (intPolyConst (modulus : ℤ))
        - intPolyMul (intPolyConst (n := 1) 0) (intPolyConst 0) : IntPoly 1)
      = intPolyConst (modulus : ℤ)
    rw [intPolyMul_const_const, intPolyMul_const_const]
    apply Poly.ext_get_eq
    intro i
    rw [Subsingleton.elim i 0]
    rw [poly_sub_get_n1, intPolyConst_get_n1, intPolyConst_get_n1, intPolyConst_get_n1]
    ring
  · change negacyclicMul (IntPoly.toRq (intPolyConst (n := 1) 1)) (0 : Rq 1)
      = IntPoly.toRq (intPolyConst (n := 1) 0)
    rw [negacyclicMul_zero_right]
    exact toRq_intPolyConst_zero.symm

/-- The ideal preimage-sampleable function: Falcon's deterministic `eval`/`isShort`, with the
deterministic trapdoor sampler `trapdoorSample _ _ c := pure (c, 0)`. -/
noncomputable def toyIdealPSF :
    PreimageSampleableFunction (PublicKey toyP) (SecretKey toyP)
      (Rq toyP.n × Rq toyP.n) (Rq toyP.n) where
  eval := (falconPSF toyP toyPrims).eval
  isShort := (falconPSF toyP toyPrims).isShort
  trapdoorSample := fun _pk _sk c => pure (c, 0)

/-- `hEval`: the ideal `eval` equals Falcon's `eval` (definitionally). -/
theorem toy_hEval (pk : PublicKey toyP) (x : Rq toyP.n × Rq toyP.n) :
    toyIdealPSF.eval pk x = (falconPSF toyP toyPrims).eval pk x := rfl

/-- `hShort`: the ideal `isShort` equals Falcon's `isShort` (definitionally). -/
theorem toy_hShort (x : Rq toyP.n × Rq toyP.n) :
    toyIdealPSF.isShort x = (falconPSF toyP toyPrims).isShort x := rfl

/-- Every `R_q` polynomial has squared `ℓ₂` norm at most `⌊q/2⌋² = 37748736`. -/
theorem toy_l2NormSq_le (s : Rq toyP.n) : LatticeCrypto.l2NormSq s ≤ 37748736 := by
  have h := LatticeCrypto.l2NormSq_le_of_cInfNorm_le
    (LatticeCrypto.cInfNorm_le_halfq (q := modulus) s)
  simpa using h

/-- The shortness predicate accepts every pair, since `betaSquared` exceeds the maximal norm. -/
theorem toy_isShort (x : Rq toyP.n × Rq toyP.n) : toyIdealPSF.isShort x = true := by
  change decide (Falcon.pairL2NormSq x.1 x.2 ≤ toyP.betaSquared) = true
  rw [decide_eq_true_eq]
  change LatticeCrypto.l2NormSq x.1 + LatticeCrypto.l2NormSq x.2 ≤ 75497472
  have h1 := toy_l2NormSq_le x.1
  have h2 := toy_l2NormSq_le x.2
  omega

/-- `eval pk (c, 0) = c`, since the second component is `0` and `h · 0 = 0`. -/
theorem toy_eval_pair_zero (pk : PublicKey toyP) (c : Rq toyP.n) :
    toyIdealPSF.eval pk (c, 0) = c := by
  change c + negacyclicMul (0 : Rq toyP.n) pk.h = c
  rw [negacyclicMul_zero_left]
  exact add_zero c

/-- `hCorrect`: the PSF is correct at every key pair — the trapdoor preimage `(t, 0)` hashes back
to `t` and is accepted by `isShort`. -/
theorem toy_correctAt (pk : PublicKey toyP) (sk : SecretKey toyP) :
    toyIdealPSF.CorrectAt pk sk := by
  intro t x hx
  have hx' : x ∈ support (pure (t, (0 : Rq toyP.n)) : ProbComp _) := hx
  rw [support_pure, Set.mem_singleton_iff] at hx'
  subst hx'
  exact ⟨toy_eval_pair_zero pk t, toy_isShort (t, 0)⟩

/-- `hNeverFail`: the deterministic `pure`-trapdoor sampler never fails. -/
theorem toy_neverFail (pk : PublicKey toyP) (sk : SecretKey toyP) (c : Rq toyP.n) :
    NeverFail (toyIdealPSF.trapdoorSample pk sk c) :=
  inferInstanceAs (NeverFail (pure _))

/-- The regularity domain sampler: a uniform target paired with `0`. -/
noncomputable def toyDomainSample (_pk : PublicKey toyP) : ProbComp (Rq toyP.n × Rq toyP.n) :=
  do let c ← ($ᵗ (Rq toyP.n)); pure (c, 0)

/-- `hReg`: the GPV regularity equation holds for `toyDomainSample`. -/
theorem toy_hReg (pk : PublicKey toyP) (sk : SecretKey toyP) :
    𝒟[(do let s ← toyDomainSample pk; pure (toyIdealPSF.eval pk s, s)
          : ProbComp (Rq toyP.n × (Rq toyP.n × Rq toyP.n)))] =
    𝒟[(do let c ← ($ᵗ (Rq toyP.n)); let s ← toyIdealPSF.trapdoorSample pk sk c; pure (c, s)
          : ProbComp (Rq toyP.n × (Rq toyP.n × Rq toyP.n)))] := by
  have key : (do let s ← toyDomainSample pk; pure (toyIdealPSF.eval pk s, s)
        : ProbComp (Rq toyP.n × (Rq toyP.n × Rq toyP.n)))
      = (do let c ← ($ᵗ (Rq toyP.n)); let s ← toyIdealPSF.trapdoorSample pk sk c; pure (c, s)) := by
    unfold toyDomainSample
    change (($ᵗ (Rq toyP.n)) >>= fun c => pure (c, (0 : Rq toyP.n)))
            >>= (fun s => pure (toyIdealPSF.eval pk s, s))
         = (($ᵗ (Rq toyP.n)) >>= fun c => (pure (c, (0 : Rq toyP.n)) >>= fun s => pure (c, s)))
    rw [bind_assoc]
    apply bind_congr
    intro c
    rw [pure_bind, pure_bind, toy_eval_pair_zero]
  rw [key]

/-! ## The honest key relation and the transport adversary -/

/-- The honest generable relation: deterministically generate the single valid key pair. -/
noncomputable def toyHr :
    GenerableRelation (PublicKey toyP) (SecretKey toyP) (validKeyPair toyP) where
  gen := pure (toyPk, toySk)
  gen_sound := by
    intro x w hx
    rw [support_pure, Set.mem_singleton_iff] at hx
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hx
    exact toy_validKeyPair

/-- The headline CMA adversary: a trivial no-query forger for the Falcon scheme. -/
noncomputable def toyAdv :
    SignatureAlg.unforgeableAdv (falconSignatureAlg toyP toyPrims Unit toyHr) where
  main := fun _pk => pure ([], ((), (0, 0)))

/-- The transport adversary for the ideal GPV scheme: query the random oracle once at the fixed
point `((), [])`, then forge at that same `(salt, message)`. -/
noncomputable def toyAdv' :
    SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Unit × List Byte →ₒ Rq toyP.n)))
        toyIdealPSF toyHr (List Byte) Unit) where
  main := fun _pk => do
    let _c ← (OracleComp.lift (OracleSpec.query
      (spec := (unifSpec + (Unit × List Byte →ₒ Rq toyP.n))
        + (List Byte →ₒ (Unit × (Rq toyP.n × Rq toyP.n))))
      (.inl (.inr ((), [])))))
    pure ([], ((), (0, 0)))

/-- The fresh-flag random-oracle handler caches the queried point `((), [])`: after running the
read step, the cache at that point is non-`none`, for every initial state. -/
lemma toy_step_caches (ds : PublicKey toyP → ProbComp (Rq toyP.n × Rq toyP.n))
    (pk : PublicKey toyP)
    (s : ((Unit × List Byte →ₒ Rq toyP.n).QueryCache × Finset (List Byte)) × Bool)
    (z : (Rq toyP.n) ×
      (((Unit × List Byte →ₒ Rq toyP.n).QueryCache × Finset (List Byte)) × Bool))
    (hz : z ∈ support ((GPVHashAndSign.progGameRunImplNoRecFlagFresh toyIdealPSF (List Byte) Unit
      ds pk (.inl (.inr ((), [])))).run s)) :
    z.2.1.1 ((), []) ≠ none := by
  rw [GPVHashAndSign.progGameRunImplNoRecFlagFresh_run_inl,
    GPVHashAndSign.progGameRunImplNoRec_run_read] at hz
  cases h : s.1.1 ((), []) with
  | some v =>
      rw [h] at hz
      dsimp only at hz
      simp only [support_map, support_pure, Set.image_singleton] at hz
      have hz : z = (v, (s.1.1, s.1.2), s.2) := hz
      subst hz
      simp only [h, ne_eq, reduceCtorEq, not_false_eq_true]
  | none =>
      rw [h] at hz
      dsimp only at hz
      simp only [support_map] at hz
      obtain ⟨_, ⟨sd, _, rfl⟩, rfl⟩ := hz
      simp only
      rw [QueryCache.cacheQuery_self]
      exact Option.some_ne_none _

/-- The transport adversary forges at a queried random-oracle point: for every run in the support,
the cache at the (constant) forged key `((), [])` is non-`none`. -/
theorem toy_ForgesQueriedPoint (ds : PublicKey toyP → ProbComp (Rq toyP.n × Rq toyP.n)) :
    GPVHashAndSign.ForgesQueriedPoint toyIdealPSF toyHr (List Byte) Unit toyAdv' ds := by
  unfold GPVHashAndSign.ForgesQueriedPoint
  intro pk z hz
  rw [show toyAdv'.main pk = (liftM (OracleSpec.query
      (spec := (unifSpec + (Unit × List Byte →ₒ Rq toyP.n))
        + (List Byte →ₒ (Unit × (Rq toyP.n × Rq toyP.n))))
      (.inl (.inr ((), []))))) >>= fun _ =>
        pure ([], ((), ((0 : Rq toyP.n), (0 : Rq toyP.n)))) from rfl] at hz
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at hz
  rw [support_bind] at hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨⟨c, smid⟩, hmid, hrest⟩ := hz
  have hcache : smid.1.1 ((), []) ≠ none := toy_step_caches ds pk _ _ hmid
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hrest
  subst hrest
  exact hcache

/-- The transport adversary makes exactly one random-oracle query and zero signing queries. -/
theorem toy_signHashQueryBound (pk : PublicKey toyP) :
    GPVHashAndSign.signHashQueryBound
      (M := List Byte) (Salt := Unit) (Range := Rq toyP.n)
      (S' := Unit × (Rq toyP.n × Rq toyP.n))
      (α := List Byte × (Unit × (Rq toyP.n × Rq toyP.n))) (oa := toyAdv'.main pk)
      (qSign := 0) (qHash := 1) := by
  refine ⟨?_, ?_⟩
  · rw [show toyAdv'.main pk = (liftM (OracleSpec.query
        (spec := (unifSpec + (Unit × List Byte →ₒ Rq toyP.n))
          + (List Byte →ₒ (Unit × (Rq toyP.n × Rq toyP.n))))
        (.inl (.inr ((), []))))) >>= fun _ =>
          pure ([], ((), ((0 : Rq toyP.n), (0 : Rq toyP.n)))) from rfl]
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by decide), fun _ => trivial⟩
  · rw [show toyAdv'.main pk = (liftM (OracleSpec.query
        (spec := (unifSpec + (Unit × List Byte →ₒ Rq toyP.n))
          + (List Byte →ₒ (Unit × (Rq toyP.n × Rq toyP.n))))
        (.inl (.inr ((), []))))) >>= fun _ =>
          pure ([], ((), ((0 : Rq toyP.n), (0 : Rq toyP.n)))) from rfl]
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inr Nat.one_pos, fun _ => trivial⟩

/-- The advantage bound holds with `samplerLoss = 1`, since every advantage is a probability. -/
theorem toy_advantage_bound :
    toyAdv.advantage (GPVHashAndSign.runtime (Range := Rq toyP.n) (List Byte) Unit)
      ≤ toyAdv'.advantage (GPVHashAndSign.runtime (Range := Rq toyP.n) (List Byte) Unit) + 1 := by
  have h1 : toyAdv.advantage
      (GPVHashAndSign.runtime (Range := Rq toyP.n) (List Byte) Unit) ≤ 1 := by
    unfold SignatureAlg.unforgeableAdv.advantage
    exact probOutput_le_one
  calc toyAdv.advantage _ ≤ 1 := h1
    _ = 0 + 1 := (zero_add 1).symm
    _ ≤ toyAdv'.advantage _ + 1 := by gcongr; exact zero_le'

/-! ## The non-vacuity certificate -/

/-- **Non-vacuity witness for the `Falcon.euf_cma_security` hypotheses.** For the degree-one toy
parameters `toyP`, primitives `toyPrims`, salt `Unit`, honest relation `toyHr`, query counts
`0`/`1`, sampler loss `1`, headline adversary `toyAdv`, and ideal PSF `toyIdealPSF`, every
hypothesis of `Falcon.euf_cma_security` holds simultaneously: the shared deterministic
`eval`/`isShort` (`hEval`/`hShort`), the GPV laws on honest keys (`hCorrect`/`hReg`/`hNeverFail`),
and the finite-precision transport package (`hTransport`).  So the headline EUF-CMA bound is not
vacuous. -/
theorem falcon_eufcma_hyps_inhabited :
    -- hEval
    (∀ pk x, toyIdealPSF.eval pk x = (falconPSF toyP toyPrims).eval pk x) ∧
    -- hShort
    (∀ x, toyIdealPSF.isShort x = (falconPSF toyP toyPrims).isShort x) ∧
    -- hCorrect
    (∀ pk sk, (pk, sk) ∈ support toyHr.gen → toyIdealPSF.CorrectAt pk sk) ∧
    -- hReg
    (∃ domainSample : PublicKey toyP → ProbComp (Rq toyP.n × Rq toyP.n),
      ∀ pk sk, (pk, sk) ∈ support toyHr.gen →
        𝒟[(do let s ← domainSample pk; pure (toyIdealPSF.eval pk s, s)
              : ProbComp (Rq toyP.n × (Rq toyP.n × Rq toyP.n)))] =
        𝒟[(do let c ← ($ᵗ (Rq toyP.n)); let s ← toyIdealPSF.trapdoorSample pk sk c; pure (c, s)
              : ProbComp (Rq toyP.n × (Rq toyP.n × Rq toyP.n)))]) ∧
    -- hNeverFail
    (∀ pk sk, (pk, sk) ∈ support toyHr.gen →
      ∀ c, NeverFail (toyIdealPSF.trapdoorSample pk sk c)) ∧
    -- hTransport
    (∃ adv' : SignatureAlg.unforgeableAdv
        (GPVHashAndSign toyIdealPSF toyHr (List Byte) Unit),
      toyAdv.advantage (GPVHashAndSign.runtime (Range := Rq toyP.n) (List Byte) Unit) ≤
          adv'.advantage (GPVHashAndSign.runtime (Range := Rq toyP.n) (List Byte) Unit) + 1 ∧
        (∀ ds, GPVHashAndSign.ForgesQueriedPoint toyIdealPSF toyHr (List Byte) Unit adv' ds) ∧
        (∀ pk, GPVHashAndSign.signHashQueryBound
          (M := List Byte) (Salt := Unit) (Range := Rq toyP.n)
          (S' := Unit × (Rq toyP.n × Rq toyP.n))
          (α := List Byte × (Unit × (Rq toyP.n × Rq toyP.n))) (oa := adv'.main pk)
          (qSign := 0) (qHash := 1))) := by
  refine ⟨toy_hEval, toy_hShort, ?_, ⟨toyDomainSample, ?_⟩, ?_,
    ⟨toyAdv', toy_advantage_bound, toy_ForgesQueriedPoint, toy_signHashQueryBound⟩⟩
  · intro pk sk _; exact toy_correctAt pk sk
  · intro pk sk _; exact toy_hReg pk sk
  · intro pk sk _ c; exact toy_neverFail pk sk c

end Examples.FalconNonVacuity
