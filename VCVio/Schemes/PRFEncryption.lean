/-
Copyright (c) 2026 Minhyuk Hwang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Minhyuk Hwang
-/

module

public import VCVio.CryptoFoundations.SymmEncAlg
public import VCVio.CryptoFoundations.SymmEncAlg.INDCPA
public import VCVio.CryptoFoundations.PRF
public import VCVio.OracleComp.SimSemantics.StateT.UntilBad
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection
public import VCVio.OracleComp.SimSemantics.Measure
public import VCVio.OracleComp.QueryTracking.QueryBound.Hazard
public import VCVio.OracleComp.QueryTracking.ListCache
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import ToMathlib.Data.ENNReal.Gauss

/-!
# CPA-secure encryption from a pseudorandom function

A pseudorandom function `F : K → R → M` into an additive group `M` gives the private-key
encryption scheme `Enc_k(m) = (r, F_k(r) + m)` for a fresh uniform `r : R`, with decryption
`Dec_k(r, c) = c - F_k(r)` (Katz–Lindell, 3rd ed., §3.5.2; Boneh–Shoup, Example 5.2). The
textbook case is `M = {0,1}ⁿ` with exclusive or, the additive group `Fin n → ZMod 2`. The scheme
is CPA-secure for multiple encryptions: against an adversary with at most `q` left-or-right
queries,

  `Adv_CPA ≤ prfAdvantage (prfReduction A true) + prfAdvantage (prfReduction A false)
      + q (q - 1) / |R|`.

## Proof

Fix the hidden bit `b`. The PRF distinguisher `prfReduction leak A b` runs `A`, answering each
admissible pair by sampling `r` and querying its function oracle at `r`.

* In the real PRF world it is the CPA experiment at `b` (`prfRealExperiment_prfReduction`).
* In the ideal world it is the game `rfImpl` in which a lazily sampled random function is kept as
  the log of the pairs `(r, F(r))` answered so far (`prfIdealExperiment_prfReduction`).
* `rfImpl` agrees with the game `freshImpl`, which draws a fresh uniform value for every
  encryption, until two encryptions use the same `r` (`agreeUntilBad_rfImpl_freshImpl`). The
  `j`-th encryption repeats an earlier `r` with probability at most `j / |R|`, so with at most `q`
  encryptions the bad event has probability at most `q (q - 1) / (2 |R|)`
  (`prEvent_freshImpl_repeatsNonce_le`).
* In `freshImpl` every ciphertext is `(r, y + m_b)` for fresh uniform `r` and `y`, which is
  uniform whatever `m_b` is, so its output does not depend on `b`
  (`evalDist_run'_freshImpl_eq`).

The triangle inequality over the five games gives the bound.

## Main definitions

* `PRFEncryption.scheme`: the encryption scheme.
* `PRFEncryption.prfReduction`: the PRF distinguisher at a hidden bit.

## Main statements

* `PRFEncryption.decrypt_encrypt`: decryption inverts encryption.
* `PRFEncryption.complete`: the scheme is complete (`SymmEncAlg.Complete`).
* `PRFEncryption.IND_CPA_Advantage_le`: the CPA bound.

## References

* Jonathan Katz and Yehuda Lindell. *Introduction to Modern Cryptography*, 3rd ed., §3.5.2
  (CPA-security from a pseudorandom function).
* [Boneh, Shoup, *A Graduate Course in Applied Cryptography*, v0.6, §5.4.1, Example 5.2 and
  Theorem 5.2](https://crypto.stanford.edu/~dabo/cryptobook/BonehShoup_0_6.pdf)
-/

public section

open OracleSpec OracleComp ENNReal PRFScheme

namespace PRFEncryption

variable {K R M : Type}

/-! ## The scheme -/

/-- The encryption scheme `Enc_k(m) = (r, F_k(r) + m)` for a fresh uniform `r`, with decryption
`Dec_k(r, c) = c - F_k(r)`. -/
@[expose] def scheme [SampleableType R] [AddCommGroup M] (prf : PRFScheme K R M) :
    SymmEncAlg ProbComp M K (R × M) where
  keygen := prf.keygen
  encrypt k msg := do
    let r ← $ᵗ R
    return (r, prf.eval k r + msg)
  decrypt k c := return some (c.2 - prf.eval k c.1)

/-- Decryption inverts encryption. -/
theorem decrypt_encrypt [SampleableType R] [AddCommGroup M] (prf : PRFScheme K R M) (k : K)
    (msg : M) :
    ((scheme prf).encrypt k msg >>= (scheme prf).decrypt k) =
      ((scheme prf).encrypt k msg >>= fun _ => pure (some msg)) := by
  simp [scheme]

/-- Decryption recovers every message (`SymmEncAlg.Complete`). -/
theorem complete [SampleableType R] [AddCommGroup M] (prf : PRFScheme K R M) :
    (scheme prf).Complete := by
  let : MeasurableSpace M := ⊤
  intro msg
  have h : (scheme prf).completenessExperiment msg =
      (fun _ => some msg) <$>
        (do let k ← prf.keygen; let r ← ($ᵗ R : ProbComp R); pure (k, r)) := by
    simp [SymmEncAlg.completenessExperiment, scheme, monad_norm]
  rw [h]
  exact OracleComp.evalDist_map_const _ _

/-! ## Logs of encryptions -/

/-- Two logged encryptions share their `r`. -/
@[expose] def RepeatsNonce (log : List (R × M)) : Prop :=
  ¬(log.map Prod.fst).Nodup

/-- A log has no value at `r` exactly when `r` is not logged. -/
private lemma lookup_eq_none_iff [DecidableEq R] (log : List (R × M)) (r : R) :
    log.lookup r = none ↔ r ∉ log.map Prod.fst := by
  induction log with
  | nil => simp
  | cons e log ih =>
    obtain ⟨r', y⟩ := e
    by_cases h : r = r'
    · subst h
      simp [List.lookup]
    · simp [List.lookup, beq_false_of_ne h, h, ih]

/-- Logging a pair keeps a repetition. -/
private lemma repeatsNonce_cons {log : List (R × M)} (h : RepeatsNonce log) (e : R × M) :
    RepeatsNonce (e :: log) := by
  simp only [RepeatsNonce, List.map_cons, List.nodup_cons, not_and_or] at h ⊢
  exact Or.inr h

/-- Logging a pair at a logged `r` makes the log repeat. -/
private lemma repeatsNonce_cons_of_mem {log : List (R × M)} {r : R} (h : r ∈ log.map Prod.fst)
    (y : M) :
    RepeatsNonce ((r, y) :: log) := by
  simp [RepeatsNonce, h]

/-! ## The PRF reduction -/

variable [SampleableType R] [AddCommGroup M] {Λ : Type} [DecidableEq Λ]

/-- Encryption with the PRF replaced by the function oracle of a PRF distinguisher. -/
@[expose] def oracleEncrypt (msg : M) : OracleComp (PRFOracleSpec R M) (R × M) := do
  let r ← ($ᵗ R : ProbComp R)
  let y ← functionQuery r
  return (r, y + msg)

/-- The handler of the PRF distinguisher: ambient uniform queries pass through, and the
left-or-right oracle at bit `b` encrypts with `oracleEncrypt`. -/
@[expose] def reductionImpl (leak : M → Λ) (b : Bool) :
    QueryImpl (unifSpec + LeftOrRight.spec M (R × M)) (OracleComp (PRFOracleSpec R M)) :=
  unifSpec.passthrough + LeftOrRight.oracle (oracleEncrypt (R := R)) leak b

/-- The PRF distinguisher at hidden bit `b`: run the CPA adversary with its left-or-right queries
at bit `b` answered through the function oracle, and output the adversary's guess. -/
@[expose] def prfReduction (prf : PRFScheme K R M) (leak : M → Λ)
    (adversary : (scheme prf).IND_CPA_Adversary) (b : Bool) : PRFAdversary R M :=
  simulateQ (reductionImpl leak b) adversary

/-- In the real PRF world, the distinguisher at bit `b` is the CPA experiment at `b`. -/
theorem prfRealExperiment_prfReduction (prf : PRFScheme K R M) (leak : M → Λ)
    (adversary : (scheme prf).IND_CPA_Adversary) (b : Bool) :
    prf.prfRealExperiment (prfReduction prf leak adversary b) =
      (scheme prf).IND_CPA_Experiment leak adversary b := by
  unfold prfRealExperiment prfReduction SymmEncAlg.IND_CPA_Experiment
  refine bind_congr fun k => QueryImpl.simulateQ_simulateQ_eq_of_apply (fun t => ?_) adversary
  have hlift : simulateQ (prf.prfRealQueryImpl k)
      (liftM ($ᵗ R : ProbComp R) : OracleComp (PRFOracleSpec R M) R) = $ᵗ R := by
    rw [← OracleComp.liftComp_eq_liftM]
    exact simulateQ_prfRealQueryImpl_liftComp prf k _
  rcases t with n | ⟨m₀, m₁⟩
  · simp [reductionImpl, prfRealQueryImpl, QueryImpl.simulateQ_add_liftM_left]
  · simp [reductionImpl, LeftOrRight.oracle_apply, oracleEncrypt, scheme, hlift]

/-! ## The random-function game -/

variable [SampleableType M]

/-- The value of the random function at `r`: the logged value, or a fresh uniform sample. -/
@[expose] def rfAnswer [DecidableEq R] (log : List (R × M)) (r : R) : ProbComp M :=
  match log.lookup r with
  | some y => pure y
  | none => $ᵗ M

/-- Encryption under the random function kept as the log: draw `r`, read or sample the value `y`
at `r`, log `(r, y)` and return `(r, y + msg)`. -/
@[expose] def rfEncrypt [DecidableEq R] (msg : M) : StateT (List (R × M)) ProbComp (R × M) := do
  let r ← ($ᵗ R : ProbComp R)
  let log ← get
  let y ← (rfAnswer log r : ProbComp M)
  set ((r, y) :: log)
  return (r, y + msg)

/-- The CPA game under the random function at bit `b`, with the random function kept as the log
of the encryptions. -/
@[expose] def rfImpl [DecidableEq R] (leak : M → Λ) (b : Bool) :
    QueryImpl (unifSpec + LeftOrRight.spec M (R × M)) (StateT (List (R × M)) ProbComp) :=
  unifSpec.passthrough + LeftOrRight.oracle (rfEncrypt (R := R)) leak b

/-- In the ideal PRF world, the distinguisher at bit `b` is the random-function game `rfImpl` at
`b` from the empty log. -/
theorem prfIdealExperiment_prfReduction [DecidableEq R] (prf : PRFScheme K R M) (leak : M → Λ)
    (adversary : (scheme prf).IND_CPA_Adversary) (b : Bool) :
    prfIdealExperiment (prfReduction prf leak adversary b) =
      (simulateQ (rfImpl leak b) adversary).run' [] := by
  have hlift : ∀ c : (R →ₒ M).QueryCache, (simulateQ (prfIdealQueryImpl (D := R) (R := M))
      (liftM ($ᵗ R : ProbComp R) : OracleComp (PRFOracleSpec R M) R)).run c =
        (fun r => (r, c)) <$> ($ᵗ R : ProbComp R) := by
    intro c
    rw [← OracleComp.liftComp_eq_liftM, simulateQ_prfIdealQueryImpl_liftComp]
    simp [map_eq_bind_pure_comp]
  unfold prfIdealExperiment prfReduction
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.ListCache.decode_nil]
  refine (OracleComp.run'_simulateQ_eq_of_query_map_eq (rfImpl leak b) _
    QueryImpl.ListCache.decode
    (fun t log => ?_) adversary []).symm
  rcases t with n | ⟨m₀, m₁⟩
  · simp [rfImpl, reductionImpl, prfIdealQueryImpl, OracleSpec.romImpl_eq_passthrough_add,
      QueryImpl.simulateQ_add_liftM_left]
  · by_cases h : leak m₀ = leak m₁
    · simp only [rfImpl, reductionImpl, QueryImpl.passthrough_add, QueryImpl.add_apply_inr,
        LeftOrRight.oracle_apply_of_leak_eq _ _ _ h, QueryImpl.apply_compose, oracleEncrypt,
        rfEncrypt, simulateQ_map, simulateQ_bind, StateT.run_map, StateT.run_bind, hlift,
        simulateQ_prfIdealQueryImpl_functionQuery, simulateQ_pure, randomOracle.run_eq]
      simp only [StateT.run_monadLift, StateT.run_get, StateT.run_set, StateT.run_pure,
        bind_assoc, pure_bind, map_bind, bind_map_left, map_pure]
      refine bind_congr fun r => ?_
      simp only [QueryImpl.ListCache.decode, QueryCache.ofFn_apply]
      cases hr : log.lookup r with
      | none =>
        simp only [rfAnswer, hr, bind_pure_comp, monadLift_self, Functor.map_map]
        refine congrArg (· <$> ($ᵗ M : ProbComp M)) (funext fun y => ?_)
        simp only [Prod.map, id, QueryImpl.ListCache.decode_cons]
        rfl
      | some y =>
        simp only [rfAnswer, hr, pure_bind, monadLift_self, Prod.map, id]
        congr 2
        rw [QueryImpl.ListCache.decode_cons]
        ext r'
        by_cases h' : r' = r
        · subst h'
          simp [QueryImpl.ListCache.decode, hr]
        · simp [h', QueryImpl.ListCache.decode]
    · simp [rfImpl, reductionImpl, h]

/-! ## The fresh game and the nonce-repetition event -/

/-- Encryption with a fresh uniform value: draw `r` and `y`, log `(r, y)` and return
`(r, y + msg)`. -/
@[expose] def freshEncrypt (msg : M) : StateT (List (R × M)) ProbComp (R × M) := do
  let r ← ($ᵗ R : ProbComp R)
  let y ← ($ᵗ M : ProbComp M)
  modify ((r, y) :: ·)
  return (r, y + msg)

/-- The CPA game at bit `b` in which every encryption uses a fresh uniform value, with the log of
the encryptions as state. -/
@[expose] def freshImpl (leak : M → Λ) (b : Bool) :
    QueryImpl (unifSpec + LeftOrRight.spec M (R × M)) (StateT (List (R × M)) ProbComp) :=
  unifSpec.passthrough + LeftOrRight.oracle (freshEncrypt (R := R)) leak b

/-- An ambient query of `rfImpl` leaves the log unchanged. -/
private lemma rfImpl_run_inl [DecidableEq R] (leak : M → Λ) (b : Bool) (n : ℕ)
    (log : List (R × M)) :
    ((rfImpl leak b) (Sum.inl n)).run log =
      (fun u => (u, log)) <$> (liftM (unifSpec.query n) : ProbComp _) := by
  simp [rfImpl]

/-- A left-or-right query of `rfImpl`. -/
private lemma rfImpl_run_inr [DecidableEq R] (leak : M → Λ) (b : Bool) (m₀ m₁ : M)
    (log : List (R × M)) :
    ((rfImpl leak b) (Sum.inr (m₀, m₁))).run log =
      if leak m₀ = leak m₁ then (do
        let r ← ($ᵗ R : ProbComp R)
        let y ← rfAnswer log r
        return (some (r, y + if b then m₁ else m₀), (r, y) :: log))
      else pure (none, log) := by
  by_cases h : leak m₀ = leak m₁
  · simp [rfImpl, h, rfEncrypt]
  · simp [rfImpl, h]

/-- An ambient query of `freshImpl` leaves the log unchanged. -/
private lemma freshImpl_run_inl (leak : M → Λ) (b : Bool) (n : ℕ) (log : List (R × M)) :
    ((freshImpl leak b) (Sum.inl n)).run log =
      (fun u => (u, log)) <$> (liftM (unifSpec.query n) : ProbComp _) := by
  simp [freshImpl]

/-- A left-or-right query of `freshImpl`. -/
private lemma freshImpl_run_inr (leak : M → Λ) (b : Bool) (m₀ m₁ : M) (log : List (R × M)) :
    ((freshImpl leak b) (Sum.inr (m₀, m₁))).run log =
      if leak m₀ = leak m₁ then (do
        let r ← ($ᵗ R : ProbComp R)
        let y ← ($ᵗ M : ProbComp M)
        return (some (r, y + if b then m₁ else m₀), (r, y) :: log))
      else pure (none, log) := by
  by_cases h : leak m₀ = leak m₁
  · simp [freshImpl, h, freshEncrypt]
  · simp [freshImpl, h]

/-- `rfImpl` and `freshImpl` agree until an `r` repeats: at a fresh `r` both draw a uniform value,
and a logged `r` makes the log repeat. -/
theorem agreeUntilBad_rfImpl_freshImpl [DecidableEq R] (leak : M → Λ) (b : Bool) :
    QueryImpl.AgreeUntilBad (rfImpl leak b) (freshImpl leak b)
      (RepeatsNonce (R := R) (M := M)) := by
  intro t log _ Q
  rcases t with n | ⟨m₀, m₁⟩
  · rw [rfImpl_run_inl, freshImpl_run_inl]
  · rw [rfImpl_run_inr, freshImpl_run_inr]
    by_cases h : leak m₀ = leak m₁
    · rw [ite_eq_left h, ite_eq_left h]
      refine prEvent_bind_congr _ _ _ _ _ fun r => ?_
      by_cases hr : r ∈ log.map Prod.fst
      · simp [repeatsNonce_cons_of_mem hr]
      · simp [rfAnswer, (lookup_eq_none_iff log r).2 hr]
    · rw [ite_eq_right h, ite_eq_right h]

/-- `freshImpl` never repairs a repetition. -/
theorem preservesInv_freshImpl (leak : M → Λ) (b : Bool) :
    QueryImpl.PreservesInv (freshImpl (R := R) leak b) (RepeatsNonce (R := R) (M := M)) := by
  intro t log hlog z hz
  rcases t with n | ⟨m₀, m₁⟩
  · rw [freshImpl_run_inl] at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨_, _, rfl⟩ := hz
    exact hlog
  · rw [freshImpl_run_inr] at hz
    by_cases h : leak m₀ = leak m₁
    · rw [ite_eq_left h] at hz
      simp only [mem_support_bind_iff, mem_support_pure_iff] at hz
      obtain ⟨r, _, y, _, rfl⟩ := hz
      exact repeatsNonce_cons hlog _
    · rw [ite_eq_right h, mem_support_pure_iff] at hz
      exact hz ▸ hlog

/-- **The nonce-repetition bound.** In the fresh game from the empty log, a computation with at
most `q` left-or-right queries repeats an `r` with probability at most `q (q - 1) / (2 |R|)`: the
`j`-th encryption draws a fresh uniform `r`, which is one of the `j` logged ones with probability
at most `j / |R|` (`OracleComp.prEvent_simulateQ_run_le_sum_of_isQueryBoundP`). -/
theorem prEvent_freshImpl_repeatsNonce_le [Fintype R] (leak : M → Λ) (b : Bool) {α : Type}
    (oa : OracleComp (unifSpec + LeftOrRight.spec M (R × M)) α)
    {charged : (unifSpec + LeftOrRight.spec M (R × M)).Domain → Prop} [DecidablePred charged]
    (hcharged : ∀ mm, charged (.inr mm)) {q : ℕ} (hq : oa.IsQueryBoundP charged q) :
    Pr{let z ← (simulateQ (freshImpl leak b) oa).run []}[RepeatsNonce z.2] ≤
      ((q * (q - 1) : ℕ) : ℝ≥0∞) / (2 * Fintype.card R) := by
  refine (OracleComp.prEvent_simulateQ_run_le_sum_of_isQueryBoundP (freshImpl leak b)
    charged List.length (fun _ => True) RepeatsNonce
    (fun j => (j : ℝ≥0∞) * (Fintype.card R : ℝ≥0∞)⁻¹)
    (fun i j hij => mul_le_mul_left (by exact_mod_cast hij) _)
    (fun _ _ _ _ _ => trivial) (fun t log ht _ hb z hz => ?_) (fun t log _ _ _ z hz => ?_)
    (fun t log ht _ hb => ?_) oa hq [] trivial (by simp [RepeatsNonce])).trans
    (le_of_eq ?_)
  · rcases t with n | mm
    · rw [freshImpl_run_inl] at hz
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨_, _, rfl⟩ := hz
      exact ⟨rfl, hb⟩
    · exact absurd (hcharged _) ht
  · rcases t with n | ⟨m₀, m₁⟩
    · rw [freshImpl_run_inl] at hz
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨_, _, rfl⟩ := hz
      exact Nat.le_succ _
    · rw [freshImpl_run_inr] at hz
      by_cases h : leak m₀ = leak m₁
      · rw [ite_eq_left h] at hz
        simp only [mem_support_bind_iff, mem_support_pure_iff] at hz
        obtain ⟨r, _, y, _, rfl⟩ := hz
        exact le_rfl
      · rw [ite_eq_right h, mem_support_pure_iff] at hz
        exact hz ▸ Nat.le_succ _
  · rcases t with n | ⟨m₀, m₁⟩
    · rw [freshImpl_run_inl, prEvent_map]
      simp [hb]
    · rw [freshImpl_run_inr]
      by_cases h : leak m₀ = leak m₁
      · rw [ite_eq_left h]
        refine (prEvent_bind_le_prEvent_of_support _ _ (fun r => r ∈ log.map Prod.fst) _
          fun r _ hr => ?_).trans ?_
        · simp only [RepeatsNonce, not_not] at hb ⊢
          simp [hr, hb]
        · refine (le_of_eq (prEvent_congr _ _ _ fun r => ?_)).trans
            ((SampleableType.prEvent_uniformSample_exists_eq_le (log.map Prod.fst).get).trans ?_)
          · exact List.mem_iff_get.trans (exists_congr fun _ => Iff.rfl)
          · rw [List.length_map, div_eq_mul_inv]
      · rw [ite_eq_right h]
        simp [hb]
  · rw [← ENNReal.gauss_sum_inv_eq]
    simp

/-! ## The fresh game does not depend on the bit -/

/-- The fresh game without its log: each admissible pair is answered by `(r, y + m_b)` for fresh
uniform `r` and `y`. -/
@[expose] def freshPlainImpl (leak : M → Λ) (b : Bool) :
    QueryImpl (unifSpec + LeftOrRight.spec M (R × M)) ProbComp :=
  unifSpec.passthrough + LeftOrRight.oracle (fun msg => (do
    let r ← ($ᵗ R : ProbComp R)
    let y ← ($ᵗ M : ProbComp M)
    return (r, y + msg) : ProbComp (R × M))) leak b

/-- Forgetting its log, the fresh game is `freshPlainImpl`. -/
theorem run'_simulateQ_freshImpl (leak : M → Λ) (b : Bool) {α : Type}
    (oa : OracleComp (unifSpec + LeftOrRight.spec M (R × M)) α) (log : List (R × M)) :
    (simulateQ (freshImpl leak b) oa).run' log = simulateQ (freshPlainImpl leak b) oa := by
  induction oa using OracleComp.inductionOn generalizing log with
  | pure x => simp
  | query_bind t k ih =>
    have hstep : ∀ log : List (R × M),
        Prod.fst <$> ((freshImpl leak b) t).run log = freshPlainImpl leak b t := by
      intro log
      rcases t with n | ⟨m₀, m₁⟩
      · rw [freshImpl_run_inl]
        simp [freshPlainImpl]
      · rw [freshImpl_run_inr]
        by_cases h : leak m₀ = leak m₁
        · simp [freshPlainImpl, h]
        · simp [freshPlainImpl, h]
    simp only [StateT.run'_eq] at ih
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run'_eq, StateT.run_bind, map_bind, ih]
    rw [← hstep log, bind_map_left]

/-- The fresh game outputs the same distribution at both bits: `y + m` is uniform whatever `m`
is. -/
theorem evalDist_run'_freshImpl_eq (leak : M → Λ) {α : Type} [MeasurableSpace α]
    (oa : OracleComp (unifSpec + LeftOrRight.spec M (R × M)) α) :
    𝒟[(simulateQ (freshImpl leak true) oa).run' []] =
      𝒟[(simulateQ (freshImpl leak false) oa).run' []] := by
  rw [run'_simulateQ_freshImpl, run'_simulateQ_freshImpl]
  refine OracleComp.evalDist_simulateQ_congr _ _ (fun t => ?_) oa
  have hunif : ∀ m : M, (fun y => y + m) <$> ($ᵗ M : ProbComp M) =ᵈ ($ᵗ M : ProbComp M) :=
    fun m => SampleableType.map_uniformSample_evalDistEq_of_bijective
      ⟨add_left_injective m, fun z => ⟨z - m, sub_add_cancel z m⟩⟩
  have henc : ∀ m m' : M, (do
      let r ← ($ᵗ R : ProbComp R)
      let y ← ($ᵗ M : ProbComp M)
      return (r, y + m) : ProbComp (R × M)) =ᵈ (do
      let r ← ($ᵗ R : ProbComp R)
      let y ← ($ᵗ M : ProbComp M)
      return (r, y + m') : ProbComp (R × M)) := by
    intro m m'
    refine EvalDistEq.bind_right _ fun r => ?_
    have h₁ := (hunif m).map (Prod.mk r)
    have h₂ := (hunif m').map (Prod.mk r)
    simp only [Functor.map_map] at h₁ h₂
    simpa only [bind_pure_comp] using h₁.trans h₂.symm
  rcases t with n | ⟨m₀, m₁⟩
  · exact EvalDistEq.rfl
  · by_cases h : leak m₀ = leak m₁
    · simp only [freshPlainImpl, QueryImpl.passthrough_add, QueryImpl.add_apply_inr,
        LeftOrRight.oracle_apply_of_leak_eq _ _ _ h, ite_true, Bool.false_eq_true, ite_false]
      exact (henc m₁ m₀).map some
    · simp only [freshPlainImpl, QueryImpl.passthrough_add, QueryImpl.add_apply_inr,
        LeftOrRight.oracle_apply_of_leak_ne _ _ _ h]
      exact EvalDistEq.rfl

/-! ## Security -/

/-- At each bit, the random-function game and the fresh game are within the nonce-repetition
bound of each other. -/
theorem boolDist_rfImpl_freshImpl_le [Fintype R] [DecidableEq R] (leak : M → Λ) (b : Bool)
    (oa : OracleComp (unifSpec + LeftOrRight.spec M (R × M)) Bool)
    {charged : (unifSpec + LeftOrRight.spec M (R × M)).Domain → Prop} [DecidablePred charged]
    (hcharged : ∀ mm, charged (.inr mm)) {q : ℕ} (hq : oa.IsQueryBoundP charged q) :
    𝒟[(simulateQ (rfImpl leak b) oa).run' []].boolDist
        𝒟[(simulateQ (freshImpl leak b) oa).run' []] ≤
      ((q * (q - 1) : ℕ) : ℝ≥0∞) / (2 * Fintype.card R) := by
  have h := agreeUntilBad_rfImpl_freshImpl (R := R) leak b
  have hbad := prEvent_freshImpl_repeatsNonce_le leak b oa hcharged hq
  have e : ∀ impl : QueryImpl (unifSpec + LeftOrRight.spec M (R × M))
      (StateT (List (R × M)) ProbComp), 𝒟[(simulateQ impl oa).run' []] {true} =
        Pr{let z ← (simulateQ impl oa).run []}[z.1 = true] := by
    intro impl
    rw [← prEvent_eq_evalDist_singleton, StateT.run'_eq, prEvent_map]
  rw [MeasureTheory.Measure.boolDist, ENNReal.absDiff_le_iff, e, e]
  exact ⟨(h.prEvent_simulateQ_run_le_add_bad_right (preservesInv_freshImpl leak b) oa [] _).trans
      (by gcongr),
    (h.symm.prEvent_simulateQ_run_le_add_bad_left (preservesInv_freshImpl leak b) oa [] _).trans
      (by gcongr)⟩

/-- **CPA security from a pseudorandom function**, for multiple encryptions. Against an adversary
with at most `q` left-or-right queries, the CPA advantage against `scheme prf` is at most the PRF
advantages of the two distinguishers `prfReduction prf leak adversary b` plus `q (q - 1) / |R|`:
for each hidden bit, the bound `q (q - 1) / (2 |R|)` on the probability that two encryptions share
their randomness. -/
theorem IND_CPA_Advantage_le [Fintype R] [DecidableEq R] (prf : PRFScheme K R M) (leak : M → Λ)
    (adversary : (scheme prf).IND_CPA_Adversary) {q : ℕ}
    (hq : adversary.MakesAtMostQueries q) :
    (scheme prf).IND_CPA_Advantage ProbCompRuntime.probComp leak adversary ≤
      prf.prfAdvantage (prfReduction prf leak adversary true) +
        prf.prfAdvantage (prfReduction prf leak adversary false) +
          ((q * (q - 1) : ℕ) : ℝ≥0∞) / Fintype.card R := by
  set ε : ℝ≥0∞ := ((q * (q - 1) : ℕ) : ℝ≥0∞) / (2 * Fintype.card R)
  have hε : ε + ε = ((q * (q - 1) : ℕ) : ℝ≥0∞) / Fintype.card R := by
    rw [ENNReal.div_add_div_same, ← two_mul, ENNReal.mul_div_mul_left _ _ two_ne_zero
      ENNReal.ofNat_ne_top]
  have hG : ∀ b, 𝒟[(scheme prf).IND_CPA_Experiment leak adversary b].boolDist
      𝒟[(simulateQ (rfImpl leak b) adversary).run' []] =
        prf.prfAdvantage (prfReduction prf leak adversary b) := by
    intro b
    rw [prfAdvantage, prfRealExperiment_prfReduction, prfIdealExperiment_prfReduction]
  have hI := fun b => boolDist_rfImpl_freshImpl_le leak b adversary (fun _ => rfl) hq
  have hF := evalDist_run'_freshImpl_eq (R := R) leak adversary
  rw [SymmEncAlg.IND_CPA_Advantage_eq_boolDist]
  set G := fun b => 𝒟[(scheme prf).IND_CPA_Experiment leak adversary b]
  set I := fun b => 𝒟[(simulateQ (rfImpl leak b) adversary).run' []]
  set F := fun b => 𝒟[(simulateQ (freshImpl (R := R) leak b) adversary).run' []]
  have h₁ := MeasureTheory.Measure.boolDist_triangle (G true) (I true) (G false)
  have h₂ := MeasureTheory.Measure.boolDist_triangle (I true) (F true) (G false)
  have h₃ := MeasureTheory.Measure.boolDist_triangle (F false) (I false) (G false)
  rw [show F true = F false from hF] at h₂
  rw [MeasureTheory.Measure.boolDist_comm (F false) (I false),
    MeasureTheory.Measure.boolDist_comm (I false) (G false), hG false] at h₃
  rw [hG true] at h₁
  calc (G true).boolDist (G false)
      ≤ prf.prfAdvantage (prfReduction prf leak adversary true) + (ε + (ε +
          prf.prfAdvantage (prfReduction prf leak adversary false))) := by
        refine h₁.trans (add_le_add le_rfl (h₂.trans (add_le_add ?_ (h₃.trans ?_))))
        · rw [show F false = F true from hF.symm]
          exact hI true
        · exact add_le_add (hI false) le_rfl
    _ = _ := by rw [← hε]; ring

end PRFEncryption
