/-
Copyright (c) 2026 Minhyuk Hwang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Minhyuk Hwang
-/

module

public import VCVio.CryptoFoundations.SymmEncAlg.INDCCA
public import VCVio.CryptoFoundations.MacAlg
public import VCVio.OracleComp.SimSemantics.StateT.UntilBad
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection
public import VCVio.OracleComp.QueryTracking.QueryBound.Simulation

/-!
# Encrypt-then-MAC

A private-key encryption scheme `enc` with ciphertexts `C` and a MAC `mac` on `C` give the
encrypt-then-MAC scheme: the key is a pair `(kₑ, kₘ)`, a message is encrypted to `c` under `kₑ`
and sent with the tag `t` of `c` under `kₘ`, and decryption of `(c, t)` returns `none` unless the
tag verifies (Katz–Lindell, 3rd ed., §5.3.1).

If `enc` is CPA-secure and `mac` is strongly unforgeable, the scheme is CCA-secure. The MAC is
assumed to verify deterministically, `mac.verify k c t = pure (vf k c t)`, which covers canonical
verification by recomputing a deterministic tag. No correctness assumption on `enc` or `mac` is
needed, because the CCA game refuses every ciphertext its challenge oracle returned, including
those of encryption queries `(m, m)` (`SymmEncAlg.IND_CCA_decryptImpl`). The forgers output a
default pair when the guessed decryption query does not exist, so `C` and `T` are assumed
inhabited.

## Proof

The CCA game at bit `b` runs the CCA handler with an extra log of the decryption queries, each
with a bit recording whether it was fresh, that is, not a challenge ciphertext (`ccaLogImpl`). The
game `rejectImpl` answers every decryption query with `none`. The two agree until a fresh
decryption query verifies (`ForgeryLogged`, `agreeUntilBad_ccaLogImpl_rejectImpl`).

In `rejectImpl` the adversary can be run by a CPA adversary that samples its own MAC key and tags
the challenge ciphertexts it receives (`cpaReduction`, `rejectExperiment_eq_IND_CPA_Experiment`).

A fresh verifying decryption query is a forgery. The forger `forger enc mac leak A b j` runs the
game, stops asking for tags at the `j`-th decryption query and outputs that query. The `j`-th
query has the same distribution in the rejecting game and in the game stopped at it
(`prEvent_rejectImpl_freshValidAt_eq`, by
`OracleComp.map_run_simulateQ_evalDistEq_of_eq_until_stopped`).
In the stopped game it is fresh against the final tagging log (`preservesInv_stopImpl`), so the
forger's SUF-CMA advantage bounds the probability that the `j`-th decryption query is a fresh
valid forgery (`map_run_simulateQ_stopImpl`). With at most `q_d` decryption queries, summing
over `j < q_d` (`forgeryExperiment_le_sum`) costs the factor `q_d` of guessing the query, as in
Katz–Lindell's proof.

## Main definitions

* `EncryptThenMac.scheme`: the encrypt-then-MAC scheme.
* `EncryptThenMac.cpaReduction`: the CPA adversary against `enc`.
* `EncryptThenMac.forger`: the SUF-CMA forger against `mac` at bit `b` and decryption query `j`.

## Main statements

* `EncryptThenMac.IND_CCA_Advantage_le`: the CCA bound.

## References

* Jonathan Katz and Yehuda Lindell. *Introduction to Modern Cryptography*, 3rd ed., §5.3.1.
* [Boneh, Shoup, *A Graduate Course in Applied Cryptography*, v0.6, §9.4.1]
  (https://crypto.stanford.edu/~dabo/cryptobook/BonehShoup_0_6.pdf)
-/

public section

open OracleSpec OracleComp ENNReal

namespace EncryptThenMac

variable {M Ke C Km T : Type}

/-! ## The scheme -/

/-- The encrypt-then-MAC scheme: encrypt under `kₑ`, tag the ciphertext under `kₘ`, and decrypt
only pairs whose tag verifies. -/
@[expose] def scheme (enc : SymmEncAlg ProbComp M Ke C) (mac : MacAlg ProbComp C Km T) :
    SymmEncAlg ProbComp M (Ke × Km) (C × T) where
  keygen := do
    let ke ← enc.keygen
    let km ← mac.keygen
    return (ke, km)
  encrypt key msg := do
    let c ← enc.encrypt key.1 msg
    let t ← mac.tag key.2 c
    return (c, t)
  decrypt key ct := do
    let v ← mac.verify key.2 ct.1 ct.2
    if v then enc.decrypt key.1 ct.1 else return none

/-! ## Game states and forgery events -/

/-- The oracles of a CCA adversary against `scheme`. -/
abbrev ccaSpec (M C T : Type) := unifSpec + LeftOrRight.spec M (C × T) + (C × T →ₒ Option M)

/-- The state of the games: the challenge log, and the log of decryption queries, each with
whether it was fresh when asked. -/
abbrev GameState (C T : Type) := List (C × T) × List ((C × T) × Bool)

/-- A fresh decryption query whose tag verifies under `vf km` has been logged. -/
@[expose] def ForgeryLogged (vf : C → T → Bool) (s : GameState C T) : Prop :=
  ∃ e ∈ s.2, e.2 = true ∧ vf e.1.1 e.1.2 = true

instance (vf : C → T → Bool) : DecidablePred (ForgeryLogged vf) := fun s => by
  unfold ForgeryLogged
  infer_instance

/-- Appending to the decryption log keeps a logged forgery. -/
private lemma forgeryLogged_append {vf : C → T → Bool} {s : GameState C T} (h : ForgeryLogged vf s)
    (l : List (C × T)) (e : List ((C × T) × Bool)) : ForgeryLogged vf (l, s.2 ++ e) := by
  obtain ⟨x, hx, hx'⟩ := h
  exact ⟨x, List.mem_append_left _ hx, hx'⟩

/-- The `j`-th logged decryption query was fresh and its tag verifies under `vf`. -/
@[expose] def FreshValidAt (vf : C → T → Bool) (j : ℕ) (s : GameState C T) : Prop :=
  ∃ x, s.2[j]? = some (x, true) ∧ vf x.1 x.2 = true

/-- In the stopped game, a fresh `j`-th decryption query is not a challenge ciphertext. -/
@[expose] def StopInv (j : ℕ) (s : GameState C T) : Prop :=
  ∀ x, s.2[j]? = some (x, true) → x ∉ s.1

/-- The `j`-th logged decryption query is not a challenge ciphertext and its tag verifies under
`vf`. -/
@[expose] def ForgeryAt (vf : C → T → Bool) (j : ℕ) (s : GameState C T) : Prop :=
  ∃ x, (s.2.map Prod.fst)[j]? = some x ∧ x ∉ s.1 ∧ vf x.1 x.2 = true

/-- Under `StopInv`, a fresh valid `j`-th decryption query is a forgery against the final
challenge log. -/
private lemma forgeryAt_of_freshValidAt {vf : C → T → Bool} {j : ℕ} {s : GameState C T}
    (hinv : StopInv j s) (h : FreshValidAt vf j s) : ForgeryAt vf j s := by
  obtain ⟨x, hx, hv⟩ := h
  exact ⟨x, by simp [hx], hinv x hx, hv⟩

/-! ## The games with a decryption log -/

variable {Λ : Type} [DecidableEq Λ]

/-- The left-or-right oracle of the games at bit `b`: encrypt-then-MAC the selected message and
log the challenge ciphertext. -/
@[expose, simps]
def challengeImpl (enc : SymmEncAlg ProbComp M Ke C) (mac : MacAlg ProbComp C Km T)
    (ke : Ke) (km : Km) (leak : M → Λ) (b : Bool) :
    QueryImpl (LeftOrRight.spec M (C × T)) (StateT (GameState C T) ProbComp) where
  toFun mm := do
    let c? ← (LeftOrRight.oracle ((scheme enc mac).encrypt (ke, km)) leak b mm :
      ProbComp (Option (C × T)))
    modify fun s => match c? with
      | some c => (c :: s.1, s.2)
      | none => s
    return c?

/-- The challenge oracle changes only the challenge log. -/
private lemma snd_of_mem_support_challengeImpl (enc : SymmEncAlg ProbComp M Ke C)
    (mac : MacAlg ProbComp C Km T) (ke : Ke) (km : Km) (leak : M → Λ) (b : Bool)
    (mm : M × M) (s : GameState C T) {z : Option (C × T) × GameState C T}
    (hz : z ∈ support ((challengeImpl enc mac ke km leak b mm).run s)) : z.2.2 = s.2 := by
  simp only [challengeImpl_apply, StateT.run_bind, StateT.run_monadLift, StateT.run_modify,
    StateT.run_pure, bind_assoc, pure_bind, monadLift_self, mem_support_bind_iff,
    mem_support_pure_iff] at hz
  obtain ⟨c?, _, rfl⟩ := hz
  cases c? <;> rfl

variable [DecidableEq C] [DecidableEq T]

/-- The decryption oracle of the CCA game with the decryption queries logged: a decryption query
is logged with its freshness, rejected if it is a challenge ciphertext, and decrypted otherwise. -/
@[expose, simps]
def ccaDecryptImpl (enc : SymmEncAlg ProbComp M Ke C) (mac : MacAlg ProbComp C Km T)
    (ke : Ke) (km : Km) :
    QueryImpl (C × T →ₒ Option M) (StateT (GameState C T) ProbComp) where
  toFun ct := do
    let s ← get
    set (s.1, s.2 ++ [(ct, decide (ct ∉ s.1))])
    if ct ∈ s.1 then return none else ((scheme enc mac).decrypt (ke, km) ct : ProbComp (Option M))

/-- The decryption oracle that logs every decryption query with its freshness and answers it with
`none`. -/
@[expose, simps] def rejectDecryptImpl :
    QueryImpl (C × T →ₒ Option M) (StateT (GameState C T) ProbComp) where
  toFun ct := do
    let s ← get
    set (s.1, s.2 ++ [(ct, decide (ct ∉ s.1))])
    return none

/-- The CCA game at bit `b` with the decryption queries logged. -/
@[expose] def ccaLogImpl (enc : SymmEncAlg ProbComp M Ke C) (mac : MacAlg ProbComp C Km T)
    (ke : Ke) (km : Km) (leak : M → Λ) (b : Bool) :
    QueryImpl (ccaSpec M C T) (StateT (GameState C T) ProbComp) :=
  unifSpec.passthrough + challengeImpl enc mac ke km leak b + ccaDecryptImpl enc mac ke km

/-- The game at bit `b` in which every decryption query is answered with `none`. -/
@[expose] def rejectImpl (enc : SymmEncAlg ProbComp M Ke C) (mac : MacAlg ProbComp C Km T)
    (ke : Ke) (km : Km) (leak : M → Λ) (b : Bool) :
    QueryImpl (ccaSpec M C T) (StateT (GameState C T) ProbComp) :=
  unifSpec.passthrough + challengeImpl enc mac ke km leak b +
    rejectDecryptImpl (M := M) (C := C) (T := T)

/-! ## The CCA game is the logged game -/

/-- Forgetting the decryption log, the logged game is the CCA game of `scheme`. -/
theorem IND_CCA_Experiment_eq (enc : SymmEncAlg ProbComp M Ke C) (mac : MacAlg ProbComp C Km T)
    (leak : M → Λ) (adversary : (scheme enc mac).IND_CCA_Adversary) (b : Bool) :
    (scheme enc mac).IND_CCA_Experiment leak adversary b = (do
      let k ← (scheme enc mac).keygen
      (simulateQ (ccaLogImpl enc mac k.1 k.2 leak b) adversary).run' ([], [])) := by
  unfold SymmEncAlg.IND_CCA_Experiment
  refine bind_congr fun k => ?_
  refine (OracleComp.run'_simulateQ_eq_of_query_map_eq _ _ Prod.fst (fun t s => ?_)
    adversary ([], [])).symm
  rcases t with (n | mm) | ct
  · simp [ccaLogImpl, SymmEncAlg.IND_CCA_impl]
  · simp only [ccaLogImpl, SymmEncAlg.IND_CCA_impl, challengeImpl_apply,
      SymmEncAlg.IND_CCA_challengeImpl_apply, QueryImpl.passthrough_add, QueryImpl.add_apply_inl,
      QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_monadLift, StateT.run_modify,
      StateT.run_pure, bind_assoc, pure_bind, map_bind, map_pure, monadLift_self]
    refine bind_congr fun c? => ?_
    cases c? <;> rfl
  · by_cases h : ct ∈ s.1
    · simp [ccaLogImpl, SymmEncAlg.IND_CCA_impl, ccaDecryptImpl_apply,
      SymmEncAlg.IND_CCA_decryptImpl_apply, h]
    · simp [ccaLogImpl, SymmEncAlg.IND_CCA_impl, ccaDecryptImpl_apply,
      SymmEncAlg.IND_CCA_decryptImpl_apply, h]

/-! ## Identical until a forgery -/

/-- The CCA game and the rejecting game agree until a fresh decryption query verifies: they
answer a decryption query differently only when it is fresh and its tag verifies, and then the
logged query is a forgery. -/
theorem agreeUntilBad_ccaLogImpl_rejectImpl (enc : SymmEncAlg ProbComp M Ke C)
    (mac : MacAlg ProbComp C Km T) (vf : Km → C → T → Bool)
    (hvf : ∀ k c t, mac.verify k c t = pure (vf k c t)) (ke : Ke) (km : Km) (leak : M → Λ)
    (b : Bool) :
    QueryImpl.AgreeUntilBad (ccaLogImpl enc mac ke km leak b) (rejectImpl enc mac ke km leak b)
      (ForgeryLogged (vf km)) := by
  refine QueryImpl.AgreeUntilBad.of_run_eq_or_bad fun t s _ => ?_
  rcases t with t | ct
  · exact Or.inl rfl
  · by_cases hmem : ct ∈ s.1
    · exact Or.inl (by simp [ccaLogImpl, rejectImpl, ccaDecryptImpl_apply, rejectDecryptImpl_apply,
      hmem])
    · by_cases hv : vf km ct.1 ct.2 = true
      · refine Or.inr ⟨fun z hz => ?_, fun z hz => ?_⟩
        · simp only [ccaLogImpl, QueryImpl.add_apply_inr, ccaDecryptImpl_apply, hmem, ite_false,
            StateT.run_bind, StateT.run_get, StateT.run_set, pure_bind, StateT.run_monadLift,
            mem_support_bind_iff, mem_support_pure_iff] at hz
          obtain ⟨_, _, rfl⟩ := hz
          exact ⟨(ct, true), List.mem_append_right _ (by simp), rfl, hv⟩
        · simp only [rejectImpl, QueryImpl.add_apply_inr, rejectDecryptImpl_apply, StateT.run_bind,
            StateT.run_get, StateT.run_set, pure_bind, StateT.run_pure, mem_support_pure_iff] at hz
          subst hz
          exact ⟨(ct, true), List.mem_append_right _ (by simp [hmem]), rfl, hv⟩
      · exact Or.inl (by
          simp [ccaLogImpl, rejectImpl, ccaDecryptImpl_apply, rejectDecryptImpl_apply, hmem,
            scheme, hvf, hv])

/-- An ambient query of the rejecting game leaves the state unchanged. -/
private lemma rejectImpl_run_inl_inl (enc : SymmEncAlg ProbComp M Ke C)
    (mac : MacAlg ProbComp C Km T)
    (ke : Ke) (km : Km) (leak : M → Λ) (b : Bool) (n : ℕ) (s : GameState C T) :
    ((rejectImpl enc mac ke km leak b) (Sum.inl (Sum.inl n))).run s =
      (fun u => (u, s)) <$> (liftM (unifSpec.query n) : ProbComp _) := by
  simp [rejectImpl]

/-- The rejecting game never removes a logged forgery. -/
theorem preservesInv_rejectImpl (enc : SymmEncAlg ProbComp M Ke C)
    (mac : MacAlg ProbComp C Km T) (vf : C → T → Bool) (ke : Ke) (km : Km) (leak : M → Λ)
    (b : Bool) : QueryImpl.PreservesInv (rejectImpl enc mac ke km leak b) (ForgeryLogged vf) := by
  intro t s hs z hz
  rcases t with (n | mm) | ct
  · rw [rejectImpl_run_inl_inl] at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨_, _, rfl⟩ := hz
    exact hs
  · have h := snd_of_mem_support_challengeImpl enc mac ke km leak b mm s hz
    obtain ⟨e, he, he'⟩ := hs
    exact ⟨e, h ▸ he, he'⟩
  · simp only [rejectImpl, QueryImpl.add_apply_inr, rejectDecryptImpl_apply, StateT.run_bind,
      StateT.run_get, StateT.run_set, pure_bind, StateT.run_pure, mem_support_pure_iff] at hz
    subst hz
    exact forgeryLogged_append hs _ _

/-- The rejecting game at bit `b`, from a key of `scheme`. -/
@[expose] def rejectExperiment (enc : SymmEncAlg ProbComp M Ke C) (mac : MacAlg ProbComp C Km T)
    (leak : M → Λ) (adversary : (scheme enc mac).IND_CCA_Adversary) (b : Bool) : ProbComp Bool := do
  let k ← (scheme enc mac).keygen
  (simulateQ (rejectImpl enc mac k.1 k.2 leak b) adversary).run' ([], [])

/-- Whether the rejecting game at bit `b` logs a fresh decryption query that verifies. -/
@[expose] def forgeryExperiment (enc : SymmEncAlg ProbComp M Ke C)
    (mac : MacAlg ProbComp C Km T) (vf : Km → C → T → Bool) (leak : M → Λ)
    (adversary : (scheme enc mac).IND_CCA_Adversary) (b : Bool) : ProbComp Bool := do
  let k ← (scheme enc mac).keygen
  let z ← (simulateQ (rejectImpl enc mac k.1 k.2 leak b) adversary).run ([], [])
  return decide (ForgeryLogged (vf k.2) z.2)

/-- The CCA game and the rejecting game at the same bit are within the probability that the
rejecting game logs a forgery. -/
theorem boolDist_IND_CCA_Experiment_rejectExperiment_le (enc : SymmEncAlg ProbComp M Ke C)
    (mac : MacAlg ProbComp C Km T) (vf : Km → C → T → Bool)
    (hvf : ∀ k c t, mac.verify k c t = pure (vf k c t)) (leak : M → Λ)
    (adversary : (scheme enc mac).IND_CCA_Adversary) (b : Bool) :
    𝒟[(scheme enc mac).IND_CCA_Experiment leak adversary b].boolDist
        𝒟[rejectExperiment enc mac leak adversary b] ≤
      𝒟[forgeryExperiment enc mac vf leak adversary b] {true} := by
  have e : ∀ mx : ProbComp (Bool × GameState C T),
      𝒟[Prod.fst <$> mx] {true} = Pr{let z ← mx}[z.1 = true] := by
    intro mx
    rw [← prEvent_eq_evalDist_singleton, prEvent_map]
  have ebad : ∀ (mx : ProbComp (Bool × GameState C T)) (P : GameState C T → Prop)
      [DecidablePred P], 𝒟[mx >>= fun z => pure (decide (P z.2))] {true} =
        Pr{let z ← mx}[P z.2] := by
    intro mx P _
    rw [← prEvent_eq_evalDist_singleton, bind_pure_comp, prEvent_map]
    simp
  rw [IND_CCA_Experiment_eq, MeasureTheory.Measure.boolDist, ENNReal.absDiff_le_iff]
  constructor
  · refine OracleComp.evalDist_bind_apply_le_add_of_support _ _ _ _
      (measurableSet_singleton true) fun k _ => ?_
    rw [StateT.run'_eq, StateT.run'_eq, e, e, ebad]
    exact (agreeUntilBad_ccaLogImpl_rejectImpl enc mac vf hvf k.1 k.2 leak b
      ).prEvent_simulateQ_run_le_add_bad_right
      (preservesInv_rejectImpl enc mac (vf k.2) k.1 k.2 leak b) adversary _ _
  · refine OracleComp.evalDist_bind_apply_le_add_of_support _ _ _ _
      (measurableSet_singleton true) fun k _ => ?_
    rw [StateT.run'_eq, StateT.run'_eq, e, e, ebad]
    exact (agreeUntilBad_ccaLogImpl_rejectImpl enc mac vf hvf k.1 k.2 leak b
      ).symm.prEvent_simulateQ_run_le_add_bad_left
      (preservesInv_rejectImpl enc mac (vf k.2) k.1 k.2 leak b) adversary _ _

/-! ## The rejecting game is a CPA game -/

/-- The challenge oracle of the CPA adversary: forward the pair to the CPA challenge oracle and tag
the ciphertext it returns. -/
@[expose, simps] def cpaChallengeImpl (mac : MacAlg ProbComp C Km T) (km : Km) :
    QueryImpl (LeftOrRight.spec M (C × T)) (OracleComp (unifSpec + LeftOrRight.spec M C)) where
  toFun mm := do
    let c? ← (unifSpec + LeftOrRight.spec M C).query (Sum.inr mm)
    match c? with
    | some c => do
      let t ← (mac.tag km c : ProbComp T)
      return some (c, t)
    | none => return none

/-- The decryption oracle of the CPA adversary, which answers every query with `none`. -/
@[expose, simps] def cpaDecryptImpl :
    QueryImpl (C × T →ₒ Option M) (OracleComp (unifSpec + LeftOrRight.spec M C)) where
  toFun _ := return none

/-- The handler of the CPA adversary under its own MAC key `km`. -/
@[expose] def cpaReductionImpl (mac : MacAlg ProbComp C Km T) (km : Km) :
    QueryImpl (ccaSpec M C T) (OracleComp (unifSpec + LeftOrRight.spec M C)) :=
  unifSpec.passthrough + cpaChallengeImpl (M := M) mac km +
    cpaDecryptImpl (M := M) (C := C) (T := T)

/-- **The CPA adversary against `enc`.** Sample a MAC key, run the CCA adversary with its challenge
queries forwarded to the CPA challenge oracle and the returned ciphertexts tagged, and answer every
decryption query with `none`. -/
@[expose] def cpaReduction (enc : SymmEncAlg ProbComp M Ke C) (mac : MacAlg ProbComp C Km T)
    (adversary : (scheme enc mac).IND_CCA_Adversary) : enc.IND_CPA_Adversary := do
  let km ← (mac.keygen : ProbComp Km)
  simulateQ (cpaReductionImpl mac km) adversary

/-- Forgetting its state, the rejecting game is the CPA challenger at bit `b` composed with the
handler of the CPA adversary. -/
theorem run'_simulateQ_rejectImpl (enc : SymmEncAlg ProbComp M Ke C)
    (mac : MacAlg ProbComp C Km T) (ke : Ke) (km : Km) (leak : M → Λ) (b : Bool) {α : Type}
    (oa : OracleComp (ccaSpec M C T) α) (s : GameState C T) :
    (simulateQ (rejectImpl enc mac ke km leak b) oa).run' s =
      simulateQ (QueryImpl.id' unifSpec + LeftOrRight.oracle (enc.encrypt ke) leak b)
        (simulateQ (cpaReductionImpl mac km) oa) := by
  rw [← QueryImpl.simulateQ_compose]
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t k ih =>
    have hstep : ∀ s : GameState C T, Prod.fst <$> ((rejectImpl enc mac ke km leak b) t).run s =
        ((QueryImpl.id' unifSpec + LeftOrRight.oracle (enc.encrypt ke) leak b) ∘ₛ
          cpaReductionImpl mac km) t := by
      intro s
      rcases t with (n | ⟨m₀, m₁⟩) | ct
      · rw [rejectImpl_run_inl_inl]
        simp [cpaReductionImpl, QueryImpl.simulateQ_add_liftM_left]
      · by_cases h : leak m₀ = leak m₁
        · simp [rejectImpl, challengeImpl_apply, cpaReductionImpl, cpaChallengeImpl_apply, h,
          scheme,
            QueryImpl.simulateQ_add_liftM_left]
        · simp [rejectImpl, challengeImpl_apply, cpaReductionImpl, cpaChallengeImpl_apply, h]
      · simp [rejectImpl, rejectDecryptImpl_apply, cpaReductionImpl, cpaDecryptImpl_apply]
    simp only [StateT.run'_eq] at ih
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run'_eq, StateT.run_bind, map_bind, ih]
    rw [← hstep s, bind_map_left]

/-- The rejecting game at bit `b` is the CPA game of `cpaReduction` at `b`. -/
theorem rejectExperiment_eq_IND_CPA_Experiment (enc : SymmEncAlg ProbComp M Ke C)
    (mac : MacAlg ProbComp C Km T) (leak : M → Λ)
    (adversary : (scheme enc mac).IND_CCA_Adversary) (b : Bool) :
    rejectExperiment enc mac leak adversary b =
      enc.IND_CPA_Experiment leak (cpaReduction enc mac adversary) b := by
  simp only [rejectExperiment, SymmEncAlg.IND_CPA_Experiment, cpaReduction, scheme, bind_assoc,
    pure_bind, simulateQ_bind, run'_simulateQ_rejectImpl]
  refine bind_congr fun ke => ?_
  rw [QueryImpl.simulateQ_add_liftM_left, simulateQ_id']

/-! ## Guessing the forging decryption query -/

/-- The challenge oracle of the rejecting game stopped at the `j`-th decryption query: once `j`
decryption queries have been logged before it, it answers `none` and changes nothing. -/
@[expose, simps]
def stopChallengeImpl (enc : SymmEncAlg ProbComp M Ke C) (mac : MacAlg ProbComp C Km T)
    (ke : Ke) (km : Km) (leak : M → Λ) (b : Bool) (j : ℕ) :
    QueryImpl (LeftOrRight.spec M (C × T)) (StateT (GameState C T) ProbComp) where
  toFun mm := do
    let s ← get
    if j < s.2.length then return none else challengeImpl enc mac ke km leak b mm

/-- The rejecting game stopped after the `j`-th decryption query: from then on challenge queries
are answered with `none`. -/
@[expose] def stopImpl (enc : SymmEncAlg ProbComp M Ke C) (mac : MacAlg ProbComp C Km T)
    (ke : Ke) (km : Km) (leak : M → Λ) (b : Bool) (j : ℕ) :
    QueryImpl (ccaSpec M C T) (StateT (GameState C T) ProbComp) :=
  unifSpec.passthrough + stopChallengeImpl enc mac ke km leak b j +
    rejectDecryptImpl (M := M) (C := C) (T := T)

/-- A decryption query of the rejecting game appends its logged entry. -/
private lemma rejectImpl_run_inr (enc : SymmEncAlg ProbComp M Ke C) (mac : MacAlg ProbComp C Km T)
    (ke : Ke) (km : Km) (leak : M → Λ) (b : Bool) (ct : C × T) (s : GameState C T) :
    ((rejectImpl enc mac ke km leak b) (Sum.inr ct)).run s =
      pure (none, (s.1, s.2 ++ [(ct, decide (ct ∉ s.1))])) := by
  simp [rejectImpl, rejectDecryptImpl_apply]

/-- A decryption query of the stopped game appends its logged entry. -/
private lemma stopImpl_run_inr (enc : SymmEncAlg ProbComp M Ke C) (mac : MacAlg ProbComp C Km T)
    (ke : Ke) (km : Km) (leak : M → Λ) (b : Bool) (j : ℕ) (ct : C × T) (s : GameState C T) :
    ((stopImpl enc mac ke km leak b j) (Sum.inr ct)).run s =
      pure (none, (s.1, s.2 ++ [(ct, decide (ct ∉ s.1))])) := by
  simp [stopImpl, rejectDecryptImpl_apply]

/-- An ambient query of the stopped game leaves the state unchanged. -/
private lemma stopImpl_run_inl_inl (enc : SymmEncAlg ProbComp M Ke C) (mac : MacAlg ProbComp C Km T)
    (ke : Ke) (km : Km) (leak : M → Λ) (b : Bool) (j : ℕ) (n : ℕ) (s : GameState C T) :
    ((stopImpl enc mac ke km leak b j) (Sum.inl (Sum.inl n))).run s =
      (fun u => (u, s)) <$> (liftM (unifSpec.query n) : ProbComp _) := by
  simp [stopImpl]

/-- A challenge query of the stopped game. -/
private lemma stopImpl_run_inl_inr (enc : SymmEncAlg ProbComp M Ke C) (mac : MacAlg ProbComp C Km T)
    (ke : Ke) (km : Km) (leak : M → Λ) (b : Bool) (j : ℕ) (mm : M × M) (s : GameState C T) :
    ((stopImpl enc mac ke km leak b j) (Sum.inl (Sum.inr mm))).run s =
      if j < s.2.length then pure (none, s) else (challengeImpl enc mac ke km leak b mm).run s := by
  by_cases h : j < s.2.length <;> simp [stopImpl, stopChallengeImpl_apply, h]

/-- The `j`-th logged decryption query has the same distribution in the rejecting game and in
the game stopped at it. -/
theorem prEvent_rejectImpl_freshValidAt_eq (enc : SymmEncAlg ProbComp M Ke C)
    (mac : MacAlg ProbComp C Km T) (vf : C → T → Bool) (ke : Ke) (km : Km) (leak : M → Λ)
    (b : Bool) (j : ℕ) {α : Type} (oa : OracleComp (ccaSpec M C T) α) (s : GameState C T) :
    Pr{let z ← (simulateQ (rejectImpl enc mac ke km leak b) oa).run s}[FreshValidAt vf j z.2] =
      Pr{let z ← (simulateQ (stopImpl enc mac ke km leak b j) oa).run s}[
        FreshValidAt vf j z.2] := by
  have hfrozen : ∀ (s : GameState C T) (ct : C × T), j < s.2.length →
      (s.2 ++ [(ct, decide (ct ∉ s.1))])[j]? = s.2[j]? := fun s ct h =>
    List.getElem?_append_left h
  have h := map_run_simulateQ_evalDistEq_of_eq_until_stopped (rejectImpl enc mac ke km leak b)
    (stopImpl enc mac ke km leak b j) (fun s : GameState C T => j < s.2.length)
    (fun s => s.2[j]?) (fun t s hs => ?_) (fun t s hs z hz => ?_) (fun t s hs z hz => ?_) oa s
  · have e := h.prEvent_eq (fun o => ∃ x, o = some (x, true) ∧ vf x.1 x.2 = true)
    simpa only [prEvent_map, FreshValidAt] using e
  · rcases t with (n | mm) | ct
    · rw [rejectImpl_run_inl_inl, stopImpl_run_inl_inl]
    · rw [stopImpl_run_inl_inr, ite_eq_right hs]
      rfl
    · rw [rejectImpl_run_inr, stopImpl_run_inr]
  · rcases t with (n | mm) | ct
    · rw [rejectImpl_run_inl_inl] at hz
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨_, _, rfl⟩ := hz
      exact ⟨hs, rfl⟩
    · have h2 := snd_of_mem_support_challengeImpl enc mac ke km leak b mm s hz
      exact ⟨h2 ▸ hs, by simp only [h2]⟩
    · rw [rejectImpl_run_inr, mem_support_pure_iff] at hz
      subst hz
      exact ⟨by simp only [List.length_append]; omega, hfrozen s ct hs⟩
  · rcases t with (n | mm) | ct
    · rw [stopImpl_run_inl_inl] at hz
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨_, _, rfl⟩ := hz
      exact ⟨hs, rfl⟩
    · rw [stopImpl_run_inl_inr, ite_eq_left hs, mem_support_pure_iff] at hz
      subst hz
      exact ⟨hs, rfl⟩
    · rw [stopImpl_run_inr, mem_support_pure_iff] at hz
      subst hz
      exact ⟨by simp only [List.length_append]; omega, hfrozen s ct hs⟩

/-- **Guessing the query.** With at most `q` decryption queries, a logged forgery is one of the
first `q` logged decryption queries. -/
theorem exists_freshValidAt_of_forgeryLogged (enc : SymmEncAlg ProbComp M Ke C)
    (mac : MacAlg ProbComp C Km T) (vf : C → T → Bool) (ke : Ke) (km : Km) (leak : M → Λ)
    (b : Bool) {α : Type} (oa : OracleComp (ccaSpec M C T) α)
    {charged : (ccaSpec M C T).Domain → Prop} [DecidablePred charged]
    (hinr : ∀ ct, charged (.inr ct)) {q : ℕ} (hq : oa.IsQueryBoundP charged q)
    (z : α × GameState C T)
    (hz : z ∈ support ((simulateQ (rejectImpl enc mac ke km leak b) oa).run ([], [])))
    (hf : ForgeryLogged vf z.2) : ∃ j ∈ Finset.range q, FreshValidAt vf j z.2 := by
  have hlen := IsQueryBoundP.cost_le_of_mem_support_run_simulateQ (fun s : GameState C T =>
    s.2.length) (fun t _ s w hw => ?_) (fun t ht s w hw => ?_) hq ([], []) z hz
  · obtain ⟨e, he, hfresh, hv⟩ := hf
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
    refine ⟨j, Finset.mem_range.2 (lt_of_lt_of_le hj (by simpa using hlen)), z.2.2[j].1, ?_, hv⟩
    rw [List.getElem?_eq_getElem hj, ← hfresh]
  · rcases t with (n | mm) | ct
    · rw [rejectImpl_run_inl_inl] at hw
      simp only [support_map, Set.mem_image] at hw
      obtain ⟨_, _, rfl⟩ := hw
      exact Nat.le_succ _
    · rw [snd_of_mem_support_challengeImpl enc mac ke km leak b mm s hw]
      exact Nat.le_succ _
    · rw [rejectImpl_run_inr, mem_support_pure_iff] at hw
      subst hw
      simp
  · rcases t with t | ct
    · rcases t with n | mm
      · rw [rejectImpl_run_inl_inl] at hw
        simp only [support_map, Set.mem_image] at hw
        obtain ⟨_, _, rfl⟩ := hw
        exact le_rfl
      · rw [snd_of_mem_support_challengeImpl enc mac ke km leak b mm s hw]
    · exact absurd (hinr ct) ht

/-- The stopped game keeps `StopInv`: before the `j`-th decryption query the entry at `j` is
absent, the entry is logged with its freshness against the current challenge log, and afterwards
the challenge log no longer changes. -/
theorem preservesInv_stopImpl (enc : SymmEncAlg ProbComp M Ke C) (mac : MacAlg ProbComp C Km T)
    (ke : Ke) (km : Km) (leak : M → Λ) (b : Bool) (j : ℕ) :
    QueryImpl.PreservesInv (stopImpl enc mac ke km leak b j) (StopInv j) := by
  intro t s hs z hz
  rcases t with (n | mm) | ct
  · rw [stopImpl_run_inl_inl] at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨_, _, rfl⟩ := hz
    exact hs
  · rw [stopImpl_run_inl_inr] at hz
    by_cases hst : j < s.2.length
    · rw [ite_eq_left hst, mem_support_pure_iff] at hz
      exact hz ▸ hs
    · rw [ite_eq_right hst] at hz
      intro x hx
      rw [snd_of_mem_support_challengeImpl enc mac ke km leak b mm s hz,
        List.getElem?_eq_none (by omega)] at hx
      exact absurd hx (by simp)
  · rw [stopImpl_run_inr, mem_support_pure_iff] at hz
    subst hz
    intro x hx
    rcases lt_trichotomy j s.2.length with hj | hj | hj
    · rw [List.getElem?_append_left hj] at hx
      exact hs x hx
    · subst hj
      simp only [List.getElem?_append_right le_rfl, Nat.sub_self, List.getElem?_cons_zero,
        Option.some.injEq, Prod.mk.injEq, decide_eq_true_eq] at hx
      exact hx.1 ▸ hx.2
    · rw [List.getElem?_eq_none (by simp; omega)] at hx
      exact absurd hx (by simp)

/-! ## The forger -/

/-- The challenge oracle of the forger, stopped at the `j`-th decryption query: encrypt the
selected message under its own key and ask the tagging oracle for the tag. -/
@[expose, simps]
def forgerChallengeImpl (enc : SymmEncAlg ProbComp M Ke C) (ke : Ke) (leak : M → Λ)
    (b : Bool) (j : ℕ) : QueryImpl (LeftOrRight.spec M (C × T))
      (StateT (List (C × T)) (OracleComp (unifSpec + (C →ₒ T)))) where
  toFun mm := do
    let d ← get
    if j < d.length then return none else do
      let c? ← (liftM (LeftOrRight.oracle (enc.encrypt ke) leak b mm : ProbComp (Option C)) :
        OracleComp (unifSpec + (C →ₒ T)) (Option C))
      match c? with
      | some c => do
        let t ← ((unifSpec + (C →ₒ T)).query (Sum.inr c) : OracleComp (unifSpec + (C →ₒ T)) T)
        return some (c, t)
      | none => return none

/-- The decryption oracle of the forger: log the query and answer `none`. -/
@[expose, simps] def forgerDecryptImpl : QueryImpl (C × T →ₒ Option M)
    (StateT (List (C × T)) (OracleComp (unifSpec + (C →ₒ T)))) where
  toFun ct := do
    modify (· ++ [ct])
    return none

/-- The handler of the forger. -/
@[expose] def forgerImpl (enc : SymmEncAlg ProbComp M Ke C) (ke : Ke) (leak : M → Λ) (b : Bool)
    (j : ℕ) : QueryImpl (ccaSpec M C T)
      (StateT (List (C × T)) (OracleComp (unifSpec + (C →ₒ T)))) :=
  unifSpec.passthrough + forgerChallengeImpl (T := T) enc ke leak b j +
    forgerDecryptImpl (M := M) (C := C) (T := T)

/-- **The forger against `mac`** at bit `b` guessing the `j`-th decryption query: sample an
encryption key, run the CCA adversary with challenge queries encrypted at bit `b` and tagged by
the tagging oracle until the `j`-th decryption query, answer every decryption query with `none`,
and output the `j`-th decryption query. -/
@[expose] def forger [Inhabited C] [Inhabited T] (enc : SymmEncAlg ProbComp M Ke C)
    (mac : MacAlg ProbComp C Km T) (leak : M → Λ) (adversary : (scheme enc mac).IND_CCA_Adversary)
    (b : Bool) (j : ℕ) : mac.UnforgeableAdversary where
  main := do
    let ke ← (enc.keygen : ProbComp Ke)
    let z ← (simulateQ (forgerImpl enc ke leak b j) adversary).run []
    return z.2[j]?.getD default

/-- The forger's handler run against the tagging oracle under `km`, on the product of its log and
the tagging log. -/
@[expose] noncomputable def forgerTaggedImpl (enc : SymmEncAlg ProbComp M Ke C)
    (mac : MacAlg ProbComp C Km T) (ke : Ke) (km : Km) (leak : M → Λ) (b : Bool) (j : ℕ) :
    QueryImpl (ccaSpec M C T) (StateT (List (C × T) × QueryLog (C →ₒ T)) ProbComp) :=
  ((unifSpec.passthrough + mac.taggingOracle km).mapStateTBase
    (forgerImpl enc ke leak b j)).flattenStateTWriterT

/-- The state of the stopped game read as the forger's: the logged decryption queries, and the
challenge log in tagging order. -/
@[expose] def forgerView (s : GameState C T) : List (C × T) × QueryLog (C →ₒ T) :=
  (s.2.map Prod.fst, s.1.reverse.map fun x => ⟨x.1, x.2⟩)

/-- The stopped game, read through `forgerView`, is the forger run against the tagging oracle. -/
theorem map_run_simulateQ_stopImpl (enc : SymmEncAlg ProbComp M Ke C)
    (mac : MacAlg ProbComp C Km T) (ke : Ke) (km : Km) (leak : M → Λ) (b : Bool) (j : ℕ)
    {α : Type} (oa : OracleComp (ccaSpec M C T) α) (s : GameState C T) :
    Prod.map id forgerView <$> (simulateQ (stopImpl enc mac ke km leak b j) oa).run s =
      (simulateQ (forgerTaggedImpl enc mac ke km leak b j) oa).run (forgerView s) := by
  refine OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ _ (fun t s => ?_) oa s
  rcases t with (n | mm) | ct
  · rw [stopImpl_run_inl_inl]
    have hq : (liftM (liftM (unifSpec.query n) : OracleComp (unifSpec + (C →ₒ T)) _) :
        StateT (List (C × T)) (OracleComp (unifSpec + (C →ₒ T))) _).run (forgerView s).1 =
          (fun u => (u, (forgerView s).1)) <$>
            (liftM (unifSpec.query n) : OracleComp (unifSpec + (C →ₒ T)) _) := by
      simp [map_eq_bind_pure_comp]
    simp only [forgerTaggedImpl, QueryImpl.flattenStateTWriterT_apply, forgerImpl,
      QueryImpl.mapStateTBase_apply, StateT.run_mk, QueryImpl.passthrough_add,
      QueryImpl.add_apply_inl,
      QueryImpl.liftTarget_apply, QueryImpl.id'_apply]
    erw [hq, simulateQ_map, QueryImpl.simulateQ_add_liftM_query_left]
    simp [Functor.map_map]
  · obtain ⟨m₀, m₁⟩ := mm
    rw [stopImpl_run_inl_inr]
    by_cases hst : j < s.2.length
    · rw [ite_eq_left hst]
      simp [forgerTaggedImpl, QueryImpl.flattenStateTWriterT_apply, forgerImpl,
        forgerChallengeImpl_apply,
        QueryImpl.mapStateTBase_apply, forgerView, hst]
    · rw [ite_eq_right hst]
      by_cases h : leak m₀ = leak m₁
      · simp [challengeImpl_apply, forgerTaggedImpl, QueryImpl.flattenStateTWriterT_apply,
        forgerImpl,
          forgerChallengeImpl_apply, QueryImpl.mapStateTBase_apply, forgerView, hst, h, scheme,
          MacAlg.taggingOracle,
          QueryImpl.simulateQ_add_liftM_left, writerT_run_simulateQ_liftTarget, simulateQ_id']
      · simp [challengeImpl_apply, forgerTaggedImpl, QueryImpl.flattenStateTWriterT_apply,
        forgerImpl,
          forgerChallengeImpl_apply, QueryImpl.mapStateTBase_apply, forgerView, h]
  · rw [stopImpl_run_inr]
    simp [forgerTaggedImpl, QueryImpl.flattenStateTWriterT_apply, forgerImpl,
      forgerDecryptImpl_apply,
      QueryImpl.mapStateTBase_apply, forgerView]

/-- The SUF-CMA experiment of the forger: the forger run against the tagging oracle, with the
`j`-th logged decryption query as the forgery. -/
theorem strongUnforgeableExperiment_forger [Inhabited C] [Inhabited T]
    (enc : SymmEncAlg ProbComp M Ke C) (mac : MacAlg ProbComp C Km T) (vf : Km → C → T → Bool)
    (hvf : ∀ k c t, mac.verify k c t = pure (vf k c t)) (leak : M → Λ)
    (adversary : (scheme enc mac).IND_CCA_Adversary) (b : Bool) (j : ℕ) :
    MacAlg.strongUnforgeableExperiment (forger enc mac leak adversary b j) = (do
      let km ← mac.keygen
      let ke ← enc.keygen
      let z ← (simulateQ (forgerTaggedImpl enc mac ke km leak b j) adversary).run ([], [])
      return (!MacAlg.taggingLogContains z.2.2 (z.2.1[j]?.getD default).1
          (z.2.1[j]?.getD default).2 &&
        vf km (z.2.1[j]?.getD default).1 (z.2.1[j]?.getD default).2)) := by
  simp only [MacAlg.strongUnforgeableExperiment, MacAlg.runWithTaggingOracle_def, forger,
    simulateQ_bind, WriterT.run_bind', hvf]
  refine bind_congr fun km => ?_
  have hkey : (simulateQ (unifSpec.passthrough + mac.taggingOracle km)
      (liftM enc.keygen : OracleComp (unifSpec + (C →ₒ T)) Ke)).run =
        (fun x => (x, [])) <$> enc.keygen := by
    rw [QueryImpl.passthrough_add, QueryImpl.simulateQ_add_liftM_left,
      writerT_run_simulateQ_liftTarget, simulateQ_id']
    rfl
  erw [hkey]
  simp only [QueryImpl.simulateQ_mapStateTBase_run, run_simulateQ_eq_map_flattenStateTWriterT,
    forgerTaggedImpl, simulateQ_pure, WriterT.run_pure', bind_map_left, map_bind, bind_assoc,
    pure_bind, Functor.map_map]
  refine bind_congr fun ke => bind_congr fun z => ?_
  simp [Prod.map]

/-- A forgery at the `j`-th decryption query wins the SUF-CMA experiment of the forger, read
through `forgerView`. -/
private lemma win_forgerView_of_forgeryAt [Inhabited C] [Inhabited T] {vf : C → T → Bool} {j : ℕ}
    {s : GameState C T} (h : ForgeryAt vf j s) :
    (!MacAlg.taggingLogContains (forgerView s).2 ((forgerView s).1[j]?.getD default).1
        ((forgerView s).1[j]?.getD default).2 &&
      vf ((forgerView s).1[j]?.getD default).1 ((forgerView s).1[j]?.getD default).2) = true := by
  obtain ⟨x, hx, hfresh, hv⟩ := h
  have hget : (forgerView s).1[j]?.getD default = x := by simp [forgerView, hx]
  rw [hget]
  simp only [MacAlg.taggingLogContains, forgerView, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true, decide_eq_false_iff_not, List.mem_map, List.mem_reverse, not_exists, not_and]
  refine ⟨fun a ha heq => hfresh ?_, hv⟩
  have h1 : a.1 = x.1 := congrArg Sigma.fst heq
  have h2 : a.2 = x.2 := by
    have := (Sigma.mk.inj_iff.1 heq).2
    exact eq_of_heq this
  exact (Prod.ext h1 h2) ▸ ha

/-- **The forgery bound.** With at most `q` decryption queries, the probability that the rejecting
game at bit `b` logs a forgery is at most the sum over `j < q` of the SUF-CMA advantages of the
forgers guessing the `j`-th decryption query. -/
theorem forgeryExperiment_le_sum [Inhabited C] [Inhabited T] (enc : SymmEncAlg ProbComp M Ke C)
    (mac : MacAlg ProbComp C Km T) (vf : Km → C → T → Bool)
    (hvf : ∀ k c t, mac.verify k c t = pure (vf k c t)) (leak : M → Λ)
    (adversary : (scheme enc mac).IND_CCA_Adversary) (b : Bool) {q : ℕ}
    (hq : adversary.MakesAtMostDecryptionQueries q) :
    𝒟[forgeryExperiment enc mac vf leak adversary b] {true} ≤
      ∑ j ∈ Finset.range q, MacAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp
        (forger enc mac leak adversary b j) := by
  set keys := (scheme enc mac).keygen
  let joint : (Ke × Km → ProbComp (Bool × GameState C T)) →
      ProbComp ((Ke × Km) × (Bool × GameState C T)) := fun r =>
    keys >>= fun k => (fun z => (k, z)) <$> r k
  let run₁ : Ke × Km → ProbComp (Bool × GameState C T) := fun k =>
    (simulateQ (rejectImpl enc mac k.1 k.2 leak b) adversary).run ([], [])
  have h1 : 𝒟[forgeryExperiment enc mac vf leak adversary b] {true} =
      Pr{let w ← joint run₁}[ForgeryLogged (vf w.1.2) w.2.2] := by
    rw [← prEvent_eq_evalDist_singleton]
    simp [forgeryExperiment, joint, run₁, keys]
  have hmem : ∀ (r : Ke × Km → ProbComp (Bool × GameState C T)) w, w ∈ support (joint r) →
      w.2 ∈ support (r w.1) := by
    intro r w hw
    simp only [joint, mem_support_bind_iff, support_map, Set.mem_image] at hw
    obtain ⟨k, _, z, hz, rfl⟩ := hw
    exact hz
  rw [h1]
  have hU : ∀ w ∈ support (joint run₁), ForgeryLogged (vf w.1.2) w.2.2 →
      ∃ j ∈ Finset.range q, FreshValidAt (vf w.1.2) j w.2.2 := by
    intro w hw hf
    refine exists_freshValidAt_of_forgeryLogged enc mac (vf w.1.2) w.1.1 w.1.2 leak b adversary
      ?_ hq w.2 (hmem run₁ w hw) hf
    intro ct
    rfl
  refine (prEvent_mono_of_support _ _ _ hU).trans
    ((prEvent_exists_finset_le _ _ _).trans (Finset.sum_le_sum fun j _ => ?_))
  let run₂ : Ke × Km → ProbComp (Bool × GameState C T) := fun k =>
    (simulateQ (stopImpl enc mac k.1 k.2 leak b j) adversary).run ([], [])
  let run₃ : Ke × Km → ProbComp (Bool × (List (C × T) × QueryLog (C →ₒ T))) := fun k =>
    (simulateQ (forgerTaggedImpl enc mac k.1 k.2 leak b j) adversary).run ([], [])
  let win : (Ke × Km) × (Bool × (List (C × T) × QueryLog (C →ₒ T))) → Bool := fun w =>
    !MacAlg.taggingLogContains w.2.2.2 (w.2.2.1[j]?.getD default).1
        (w.2.2.1[j]?.getD default).2 &&
      vf w.1.2 (w.2.2.1[j]?.getD default).1 (w.2.2.1[j]?.getD default).2
  have h2 : Pr{let w ← joint run₁}[FreshValidAt (vf w.1.2) j w.2.2] =
      Pr{let w ← joint run₂}[FreshValidAt (vf w.1.2) j w.2.2] := by
    refine prEvent_bind_congr _ _ _ _ _ fun k => ?_
    rw [prEvent_map, prEvent_map]
    exact prEvent_rejectImpl_freshValidAt_eq enc mac (vf k.2) k.1 k.2 leak b j adversary _
  have h3 : Pr{let w ← joint run₂}[FreshValidAt (vf w.1.2) j w.2.2] ≤
      Pr{let w ← joint run₂}[win (w.1, (w.2.1, forgerView w.2.2)) = true] := by
    refine prEvent_mono_of_support _ _ _ fun w hw hf => ?_
    have hinv := OracleComp.simulateQ_run_preserves_inv_of_query _ (StopInv j)
      (preservesInv_stopImpl enc mac w.1.1 w.1.2 leak b j) adversary ([], [])
      (fun x hx => by simp at hx) w.2 (hmem run₂ w hw)
    exact win_forgerView_of_forgeryAt (forgeryAt_of_freshValidAt hinv hf)
  have h4 : Pr{let w ← joint run₂}[win (w.1, (w.2.1, forgerView w.2.2)) = true] =
      Pr{let w ← keys >>= fun k => (fun z => (k, z)) <$> run₃ k}[win w = true] := by
    refine prEvent_bind_congr _ _ _ _ _ fun k => ?_
    rw [prEvent_map, prEvent_map]
    have e := map_run_simulateQ_stopImpl enc mac k.1 k.2 leak b j adversary ([], [])
    rw [show forgerView (([] : List (C × T)), ([] : List ((C × T) × Bool))) = ([], []) from rfl]
      at e
    simp only [run₂, run₃]
    rw [← e, prEvent_map]
    rfl
  have h5 : Pr{let w ← keys >>= fun k => (fun z => (k, z)) <$> run₃ k}[win w = true] =
      MacAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp
        (forger enc mac leak adversary b j) := by
    rw [MacAlg.strongUnforgeableAdvantage, ProbCompRuntime.probComp_evalDist,
      strongUnforgeableExperiment_forger enc mac vf hvf, ← prEvent_eq_evalDist_singleton,
      ← prEvent_map _ win (· = true)]
    simp only [keys, scheme, run₃, win, bind_assoc, map_bind, Functor.map_map,
      bind_pure_comp, bind_map_left]
    exact OracleComp.prEvent_bind_bind_swap _ _ _
  exact (h2.le.trans h3).trans (h4.le.trans h5.le)

/-! ## Security -/

/-- **Encrypt-then-MAC is CCA-secure** (Katz–Lindell, §5.3.1). Let `mac` verify deterministically
by `vf`. Against an adversary with at most `q` decryption queries, the CCA advantage against
`scheme enc mac` is at most the CPA advantage of `cpaReduction` against `enc`, plus, for each hidden
bit `b` and each `j < q`, the SUF-CMA advantage of the forger `forger enc mac leak adversary b j`
that guesses that the `j`-th decryption query is a forgery. -/
theorem IND_CCA_Advantage_le [Inhabited C] [Inhabited T] (enc : SymmEncAlg ProbComp M Ke C)
    (mac : MacAlg ProbComp C Km T) (vf : Km → C → T → Bool)
    (hvf : ∀ k c t, mac.verify k c t = pure (vf k c t)) (leak : M → Λ)
    (adversary : (scheme enc mac).IND_CCA_Adversary) {q : ℕ}
    (hq : adversary.MakesAtMostDecryptionQueries q) :
    (scheme enc mac).IND_CCA_Advantage ProbCompRuntime.probComp leak adversary ≤
      enc.IND_CPA_Advantage ProbCompRuntime.probComp leak (cpaReduction enc mac adversary) +
        ∑ j ∈ Finset.range q,
          (MacAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp
              (forger enc mac leak adversary true j) +
            MacAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp
              (forger enc mac leak adversary false j)) := by
  rw [SymmEncAlg.IND_CCA_Advantage_eq_boolDist, SymmEncAlg.IND_CPA_Advantage_eq_boolDist,
    Finset.sum_add_distrib]
  set G := fun b => 𝒟[(scheme enc mac).IND_CCA_Experiment leak adversary b]
  set R := fun b => 𝒟[rejectExperiment enc mac leak adversary b]
  have hR : ∀ b, R b = 𝒟[enc.IND_CPA_Experiment leak (cpaReduction enc mac adversary) b] :=
    fun b => by simp only [R, rejectExperiment_eq_IND_CPA_Experiment]
  have hG : ∀ b, (G b).boolDist (R b) ≤ ∑ j ∈ Finset.range q,
      MacAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp
        (forger enc mac leak adversary b j) := fun b =>
    (boolDist_IND_CCA_Experiment_rejectExperiment_le enc mac vf hvf leak adversary b).trans
      (forgeryExperiment_le_sum enc mac vf hvf leak adversary b hq)
  have h₁ := MeasureTheory.Measure.boolDist_triangle (G true) (R true) (G false)
  have h₂ := MeasureTheory.Measure.boolDist_triangle (R true) (R false) (G false)
  rw [MeasureTheory.Measure.boolDist_comm (R false) (G false)] at h₂
  rw [← hR true, ← hR false]
  calc (G true).boolDist (G false)
      ≤ (G true).boolDist (R true) + ((R true).boolDist (R false) +
          (G false).boolDist (R false)) := h₁.trans (add_le_add le_rfl h₂)
    _ ≤ _ := by
      have := hG true
      have := hG false
      calc _ ≤ (∑ j ∈ Finset.range q, MacAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp
              (forger enc mac leak adversary true j)) + ((R true).boolDist (R false) +
            ∑ j ∈ Finset.range q, MacAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp
              (forger enc mac leak adversary false j)) := by gcongr
        _ = _ := by ring

end EncryptThenMac
