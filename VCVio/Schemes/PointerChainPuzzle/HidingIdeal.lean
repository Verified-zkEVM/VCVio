/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.PointerChainPuzzle.HidingPRF
public import VCVio.OracleComp.QueryTracking.RandomOracle.Commute
public import VCVio.OracleComp.SimSemantics.StateT.Measure

/-!
# Time-lock encryption with the pointer-chain puzzle: the ideal PRF world

This file takes the PRF step of the hiding proof. In the ideal world of the PRF distinguisher
`hidingDistinguisher`, the `2 qEnc` PRF instances are independent random functions; there the
indexed hybrid outputs `true` with the same probability at both hidden bits
(`prfIdealExperiment_indexedRun_true_eq_false`). With the normalization of
`HiddenBit.lean`, the gap between the two hidden bits of the indexed hybrid against independent
PRF keys is then at most twice the PRF advantage of the distinguisher
(`absDiff_indexed_le_prfAdvantage`).

The ideal world is the hybrid `G₃` and the last step of the paper's proof of the hiding theorem
(`app:hiding`): after HMAC under each subkey is replaced by a random function, every ciphertext is
uniform given its length and every tag is uniform, so the view does not depend on the hidden bit.
The paper charges `Adv^prf_{2Q_enc}` once per hidden bit; here the distinguisher draws the bit
itself, and the factor `2` comes from the normalization of `HiddenBit.lean`.

## Independence of the hidden bit

The preprocessing and the generator query only the oracles with subkeys, which the distinguisher
answers with a lazy random oracle. The online phase runs three handlers, the indexed challenger,
the distinguisher's own handler and the random functions of the ideal world; on the joint state
of counter, subkey cache and instance cache they are one stateful handler.

Encryption `j` queries instance `(0, j)` at the block counters `be 8 i`, which are distinct
because a plaintext has fewer than `2 ^ 64` blocks, and instance `(1, j)` once, for the tag. Along
any run no instance of an encryption that has not yet happened has a cached point, so each
envelope is drawn from fresh points: it is distributed as the envelope with uniform keystream
blocks and a uniform tag (`fst_map_run_sealBy_evalDistEq_of_fresh`). Forgetting the instance cache
therefore maps the joint handler onto a fresh game whose encryption samples blocks and tag
directly. In the fresh game the body is the message XOR a uniform keystream, the length field
depends only on the length of the message, unequal-length requests are answered with `none` and
the counter evolves alike at both bits, so every answer has the same distribution at both bits.

The statements carry no query bound: an encryption beyond the `qEnc`-th is the empty byte string
at both bits.

## Main statements

* `PointerChainPuzzle.fst_map_run_sealBy_evalDistEq_of_fresh`: an envelope at a fresh pair of
  instances of the ideal world is the envelope with uniform keystream blocks and a uniform tag.
* `PointerChainPuzzle.prfIdealExperiment_indexedRun_evalDistEq`,
  `PointerChainPuzzle.prfIdealExperiment_indexedRun_true_eq_false`: in the ideal world the indexed
  hybrid does not depend on the hidden bit.
* `PointerChainPuzzle.absDiff_indexed_le_prfAdvantage`: the PRF step.
-/

public section

open OracleSpec OracleComp TimeLockPuzzle PRFScheme
open scoped ENNReal

namespace PointerChainPuzzle

open LeanSeal Envelope

variable {n m : ℕ} {S L Salt Ctx N K : Type}
variable {w : ℕ} (codec : FixedCodec N w) (encodePuzzle : Puzzle n S L Salt → ByteArray)
  (qEnc : ℕ)

variable [DecidableEq S] [DecidableEq L] [DecidableEq Salt] [DecidableEq Ctx] [DecidableEq N]
  [SampleableType S] [SampleableType L] [SampleableType N] [SampleableType K]

/-! ## The ideal world as one stateful handler -/

variable (n S L Salt Ctx N K) in
/-- The handler of `indexedRun`: local coins forwarded, the oracles with subkeys answered by a lazy
random oracle, and instance queries forwarded to the function oracle. -/
private abbrev runImpl : QueryImpl (indexedSpec n S L Salt Ctx N K qEnc)
    (StateT (sealSpec n S L Salt Ctx N K).QueryCache
      (OracleComp (PRFOracleSpec (Fin (2 * qEnc) × ByteArray) (Bytes 32)))) :=
  (QueryImpl.ofLift unifSpec
          (OracleComp (PRFOracleSpec (Fin (2 * qEnc) × ByteArray) (Bytes 32)))).liftTarget
        (StateT (sealSpec n S L Salt Ctx N K).QueryCache
          (OracleComp (PRFOracleSpec (Fin (2 * qEnc) × ByteArray) (Bytes 32)))) +
       ((sealSpec n S L Salt Ctx N K).randomOracle.liftTarget
          (StateT (sealSpec n S L Salt Ctx N K).QueryCache
            (OracleComp (PRFOracleSpec (Fin (2 * qEnc) × ByteArray) (Bytes 32)))) +
        (fun x => liftM (functionQuery (R := Bytes 32) x) : QueryImpl (instanceSpec qEnc)
          (StateT (sealSpec n S L Salt Ctx N K).QueryCache
            (OracleComp (PRFOracleSpec (Fin (2 * qEnc) × ByteArray) (Bytes 32))))))

omit [SampleableType N] in
/-- On a computation of the hiding adversary's own oracles, `runImpl` is the random oracle
of the oracles with subkeys. -/
private theorem run_simulateQ_runImpl_liftComp {α : Type}
    (pre : OracleComp (unifSpec + sealSpec n S L Salt Ctx N K) α)
    (c : (sealSpec n S L Salt Ctx N K).QueryCache) :
    (simulateQ (runImpl n S L Salt Ctx N K qEnc)
        (liftComp pre (indexedSpec n S L Salt Ctx N K qEnc))).run c =
      liftComp ((simulateQ (sealSpec n S L Salt Ctx N K).romImpl pre).run c)
        (PRFOracleSpec (Fin (2 * qEnc) × ByteArray) (Bytes 32)) := by
  induction pre using OracleComp.inductionOn generalizing c with
  | pure x => simp
  | query_bind t k ih =>
    rcases t with u | t
    · simp [ih]
      congr 1
    · rcases t with t | t | t <;>
      · simp only [liftComp_bind, simulateQ_bind, StateT.run_bind, ih, simulateQ_liftM_query]
        simp [OracleSpec.query, simulateQ_liftM_query]
        rfl

variable (n S L Salt Ctx N K) in
/-- The oracles of the online phase: local coins, the left-or-right oracle and the oracles with
subkeys. -/
private abbrev challengeSpec :=
  (unifSpec + LeftOrRight.spec Plaintext ByteArray) + sealSpec n S L Salt Ctx N K

/-- The handler of the indexed challenger in `indexedExperiment`. -/
private abbrev challengerImpl (pz : ByteArray) (b : Bool) :
    QueryImpl (challengeSpec n S L Salt Ctx N K)
      (StateT ℕ (OracleComp (indexedSpec n S L Salt Ctx N K qEnc))) :=
  ((QueryImpl.ofLift unifSpec (OracleComp (indexedSpec n S L Salt Ctx N K qEnc))).liftTarget
        (StateT ℕ (OracleComp (indexedSpec n S L Salt Ctx N K qEnc))) +
      LeftOrRight.oracle (indexedEncrypt (n := n) (S := S) (L := L) (Salt := Salt) (Ctx := Ctx)
        (K := K) codec qEnc pz) plaintextLength b) +
      (fun t => liftM ((indexedSpec n S L Salt Ctx N K qEnc).query (.inr (.inl t))) :
        QueryImpl (sealSpec n S L Salt Ctx N K)
          (StateT ℕ (OracleComp (indexedSpec n S L Salt Ctx N K qEnc))))

/-- The online phase of the ideal world as one stateful handler: the indexed challenger, then
`runImpl`, then the random functions of the ideal world, on the joint state. -/
private abbrev jointImpl (pz : ByteArray) (b : Bool) :
    QueryImpl (challengeSpec n S L Salt Ctx N K)
    (StateT ((ℕ × (sealSpec n S L Salt Ctx N K).QueryCache) × (instanceSpec qEnc).QueryCache)
      ProbComp) :=
  (prfIdealQueryImpl.mapStateTBase
    ((runImpl n S L Salt Ctx N K qEnc).mapStateTBase
      (challengerImpl codec qEnc pz b)).flattenStateT).flattenStateT

/-- The three nested handlers of the online phase are `jointImpl`. -/
private theorem run_challenger_eq_jointImpl (pz : ByteArray) (b : Bool) {α : Type}
    (X : OracleComp (challengeSpec n S L Salt Ctx N K) α)
    (c₁ : (sealSpec n S L Salt Ctx N K).QueryCache) (c₂ : (instanceSpec qEnc).QueryCache) :
    (simulateQ prfIdealQueryImpl ((simulateQ (runImpl n S L Salt Ctx N K qEnc)
        ((simulateQ (challengerImpl codec qEnc pz b) X).run' 0)).run' c₁)).run' c₂ =
      Prod.fst <$> (simulateQ (jointImpl codec qEnc pz b) X).run ((0, c₁), c₂) := by
  simp only [StateT.run'_eq, simulateQ_map, StateT.run_map,
    simulateQ_mapStateTBase_run_eq_map_flattenStateT, Functor.map_map]

/-- `jointImpl` answers the oracles with subkeys from their random oracle. -/
private theorem jointImpl_seal (pz : ByteArray) (b : Bool)
    (t : (sealSpec n S L Salt Ctx N K).Domain) (j : ℕ)
    (c₁ : (sealSpec n S L Salt Ctx N K).QueryCache) (c₂ : (instanceSpec qEnc).QueryCache) :
    (jointImpl codec qEnc pz b (.inr t)).run ((j, c₁), c₂) =
      (fun z => (z.1, ((j, z.2), c₂))) <$>
        ((sealSpec n S L Salt Ctx N K).randomOracle t).run c₁ := by
  simp [jointImpl, challengerImpl, ← liftComp_eq_liftM, simulateQ_prfIdealQueryImpl_liftComp]

/-- `jointImpl` forwards local coins. -/
private theorem jointImpl_unif (pz : ByteArray) (b : Bool) (u : ℕ)
    (s : (ℕ × (sealSpec n S L Salt Ctx N K).QueryCache) × (instanceSpec qEnc).QueryCache) :
    (jointImpl codec qEnc pz b (.inl (.inl u))).run s =
      (fun x => (x, s)) <$> (unifSpec.query u : ProbComp (Fin (u + 1))) := by
  obtain ⟨⟨j, c₁⟩, c₂⟩ := s
  simp [jointImpl, challengerImpl, prfIdealQueryImpl, romImpl_eq_passthrough_add,
    QueryImpl.simulateQ_add_liftM_query_left]

omit [SampleableType N] in
/-- `runImpl` forwards the instance queries of an envelope to the function oracle. -/
private theorem run_simulateQ_runImpl_sealBy (i₀ i₁ : Fin (2 * qEnc)) (pz : ByteArray)
    (nonce : N) (msg : Plaintext) (c₁ : (sealSpec n S L Salt Ctx N K).QueryCache) :
    (simulateQ (runImpl n S L Salt Ctx N K qEnc) (sealBy codec
      (fun x => liftM ((indexedSpec n S L Salt Ctx N K qEnc).query (.inr (.inr (i₀, x)))))
      (fun x => liftM ((indexedSpec n S L Salt Ctx N K qEnc).query (.inr (.inr (i₁, x)))))
      pz nonce msg)).run c₁ =
    (fun r => (r, c₁)) <$> sealBy codec (fun x => functionQuery (R := Bytes 32) (i₀, x))
      (fun x => functionQuery (R := Bytes 32) (i₁, x)) pz nonce msg := by
  have hL : Cslib.IsMonadHom (OracleComp (PRFOracleSpec (Fin (2 * qEnc) × ByteArray) (Bytes 32)))
      (StateT (sealSpec n S L Salt Ctx N K).QueryCache
        (OracleComp (PRFOracleSpec (Fin (2 * qEnc) × ByteArray) (Bytes 32))))
      (fun x => liftM x) :=
    Cslib.IsMonadHom.mk' (fun a => by simp) (fun x y => by simp)
  rw [sealBy_map codec (simulateQ_isMonadHom _)]
  simp only [simulateQ_spec_query, QueryImpl.add_apply_inr]
  rw [← sealBy_map codec hL, StateT.run_liftM, map_eq_bind_pure_comp]
  rfl

omit [DecidableEq N] [SampleableType N] in
/-- In the ideal world the instance queries of an envelope go to the random oracle of the
instances. -/
private theorem simulateQ_prfIdeal_sealBy (i₀ i₁ : Fin (2 * qEnc)) (pz : ByteArray) (nonce : N)
    (msg : Plaintext) :
    simulateQ prfIdealQueryImpl (sealBy codec (fun x => functionQuery (R := Bytes 32) (i₀, x))
      (fun x => functionQuery (R := Bytes 32) (i₁, x)) pz nonce msg) =
    sealBy codec (fun x => (instanceSpec qEnc).randomOracle (i₀, x))
      (fun x => (instanceSpec qEnc).randomOracle (i₁, x)) pz nonce msg := by
  rw [sealBy_map codec (simulateQ_isMonadHom _)]
  simp only [simulateQ_prfIdealQueryImpl_functionQuery]

/-- In the ideal world the nonce of an encryption is a uniform draw that leaves both caches
unchanged. -/
private theorem run_simulateQ_runImpl_nonce (c₁ : (sealSpec n S L Salt Ctx N K).QueryCache)
    (c₂ : (instanceSpec qEnc).QueryCache) :
    (simulateQ prfIdealQueryImpl ((simulateQ (runImpl n S L Salt Ctx N K qEnc)
      (liftM ($ᵗ N : ProbComp N) : OracleComp (indexedSpec n S L Salt Ctx N K qEnc) N)).run
        c₁)).run c₂ = (fun x => ((x, c₁), c₂)) <$> ($ᵗ N : ProbComp N) := by
  simp only [← liftComp_eq_liftM, QueryImpl.simulateQ_add_liftComp_left, simulateQ_liftTarget,
    StateT.run_liftM, simulateQ_bind, simulateQ_pure]
  rw [show simulateQ (QueryImpl.ofLift unifSpec
      (OracleComp (PRFOracleSpec (Fin (2 * qEnc) × ByteArray) (Bytes 32)))) ($ᵗ N : ProbComp N) =
      liftComp ($ᵗ N : ProbComp N) (PRFOracleSpec (Fin (2 * qEnc) × ByteArray) (Bytes 32))
      from rfl]
  rw [simulateQ_prfIdealQueryImpl_liftComp]
  simp [map_eq_bind_pure_comp]

/-- `jointImpl` on a left-or-right query: an unequal-length pair is answered with `none`; an
accepted pair advances the counter and, below the budget, is the envelope of the selected message
with a uniform nonce and the random oracles of instances `(0, j)` and `(1, j)`. -/
private theorem jointImpl_challenge (pz : ByteArray) (b : Bool) (mm : Plaintext × Plaintext)
    (j : ℕ) (c₁ : (sealSpec n S L Salt Ctx N K).QueryCache)
    (c₂ : (instanceSpec qEnc).QueryCache) :
    (jointImpl codec qEnc pz b (.inl (.inr mm))).run ((j, c₁), c₂) =
      if plaintextLength mm.1 = plaintextLength mm.2 then
        if h : j < qEnc then do
          let nonce ← ($ᵗ N : ProbComp N)
          let z ← (sealBy codec
            (fun x => (instanceSpec qEnc).randomOracle (instanceIndex 0 ⟨j, h⟩, x))
            (fun x => (instanceSpec qEnc).randomOracle (instanceIndex 1 ⟨j, h⟩, x))
            pz nonce (if b then mm.2 else mm.1)).run c₂
          pure (some z.1, ((j + 1, c₁), z.2))
        else pure (some ByteArray.empty, ((j + 1, c₁), c₂))
      else pure (none, ((j, c₁), c₂)) := by
  by_cases hl : plaintextLength mm.1 = plaintextLength mm.2
  · by_cases hj : j < qEnc
    · simp [jointImpl, challengerImpl, LeftOrRight.oracle, hl, indexedEncrypt, hj,
        run_simulateQ_runImpl_nonce, run_simulateQ_runImpl_sealBy, simulateQ_prfIdeal_sealBy]
    · simp [jointImpl, challengerImpl, LeftOrRight.oracle, hl, indexedEncrypt, hj]
  · simp [jointImpl, challengerImpl, LeftOrRight.oracle, hl]

omit [SampleableType N] in
/-- A prefix that queries only the hiding adversary's own oracles runs in the ideal world as
its random-oracle simulation. -/
private theorem run_liftComp_bind_eq {α β : Type}
    (pre : OracleComp (unifSpec + sealSpec n S L Salt Ctx N K) α)
    (k : α → OracleComp (indexedSpec n S L Salt Ctx N K qEnc) β)
    (c₁ : (sealSpec n S L Salt Ctx N K).QueryCache) (c₂ : (instanceSpec qEnc).QueryCache) :
    (simulateQ prfIdealQueryImpl ((simulateQ (runImpl n S L Salt Ctx N K qEnc)
        (liftComp pre (indexedSpec n S L Salt Ctx N K qEnc) >>= k)).run' c₁)).run' c₂ =
      (simulateQ (sealSpec n S L Salt Ctx N K).romImpl pre).run c₁ >>= fun z =>
        (simulateQ prfIdealQueryImpl ((simulateQ (runImpl n S L Salt Ctx N K qEnc)
          (k z.1)).run' z.2)).run' c₂ := by
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, run_simulateQ_runImpl_liftComp,
    map_bind, simulateQ_map, simulateQ_prfIdealQueryImpl_liftComp, StateT.run_map,
    StateT.run_liftM, bind_assoc, pure_bind]

/-! ## Fresh instances -/

/-- Distinct kinds or encryptions have distinct instances. -/
theorem instanceIndex_injective {q : ℕ} {i i' : Fin 2} {j j' : Fin q}
    (h : instanceIndex i j = instanceIndex i' j') : i = i' ∧ j = j' :=
  Prod.ext_iff.mp (finProdFinEquiv.injective h)

variable (n S L Salt Ctx N K) in
/-- The state of the fresh game: the counter of accepted requests and the cache of the oracles
with subkeys. -/
private abbrev freshState := ℕ × (sealSpec n S L Salt Ctx N K).QueryCache

/-- The encryption of the fresh game: below the budget, a uniform nonce and the envelope with
uniform keystream blocks and a uniform tag. -/
private def freshEncrypt (pz : ByteArray) (msg : Plaintext) :
    StateT (freshState n S L Salt Ctx N K) ProbComp ByteArray := do
  let s ← get
  set (s.1 + 1, s.2)
  if s.1 < qEnc then
    (liftM (do
      let nonce ← ($ᵗ N : ProbComp N)
      sealBy codec (fun _ => ($ᵗ Bytes 32 : ProbComp (Bytes 32))) (fun _ => $ᵗ Bytes 32) pz
        nonce msg : ProbComp ByteArray) : StateT (freshState n S L Salt Ctx N K) ProbComp ByteArray)
  else return ByteArray.empty

/-- The fresh game: the indexed challenger with every envelope drawn by `freshEncrypt`. -/
private def freshImpl (pz : ByteArray) (b : Bool) :
    QueryImpl (challengeSpec n S L Salt Ctx N K)
      (StateT (freshState n S L Salt Ctx N K) ProbComp) :=
  ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (freshState n S L Salt Ctx N K) ProbComp) +
      LeftOrRight.oracle (freshEncrypt (n := n) (S := S) (L := L) (Salt := Salt) (Ctx := Ctx)
        (K := K) codec qEnc pz) plaintextLength b) +
    (fun t => StateT.mk fun s =>
      (fun z => (z.1, (s.1, z.2))) <$> ((sealSpec n S L Salt Ctx N K).randomOracle t).run s.2 :
      QueryImpl (sealSpec n S L Salt Ctx N K) (StateT (freshState n S L Salt Ctx N K) ProbComp))

omit [DecidableEq N] [SampleableType N] in
/-- **An envelope at a fresh pair of instances is uniform.** If the random oracle of the
instances has cached no point of instances `(0, j)` and `(1, j)`, the envelope it answers is
distributed as the envelope with uniform keystream blocks and a uniform tag. -/
theorem fst_map_run_sealBy_evalDistEq_of_fresh (j : Fin qEnc) (pz : ByteArray) (nonce : N)
    (msg : Plaintext) (c₂ : (instanceSpec qEnc).QueryCache)
    (hfresh : ∀ i x, c₂ (instanceIndex i j, x) = none) :
    Prod.fst <$> (sealBy codec (fun x => (instanceSpec qEnc).randomOracle (instanceIndex 0 j, x))
      (fun x => (instanceSpec qEnc).randomOracle (instanceIndex 1 j, x)) pz nonce msg).run c₂ =ᵈ
      sealBy codec (fun _ => ($ᵗ Bytes 32 : ProbComp (Bytes 32))) (fun _ => $ᵗ Bytes 32)
        pz nonce msg := by
  have h01 : instanceIndex (0 : Fin 2) j ≠ instanceIndex 1 j := fun h =>
    absurd (instanceIndex_injective h).1 (by decide)
  set G : List (Bytes 32) → ProbComp ByteArray := fun bs =>
    ($ᵗ Bytes 32 : ProbComp (Bytes 32)) >>= fun t => pure ((⟨(signedBytes codec pz nonce
      (xorBytes msg.1.data.toList ((bs.flatMap fun x => x.toList).take msg.1.size)) ++
        t.toList).toArray⟩ : ByteArray)) with hG
  simp only [sealBy, StateT.run_bind, map_bind, StateT.run_pure]
  refine (EvalDistEq.bind_congr_of_support (g := fun z => G z.1) _ fun z hz => ?_).trans ?_
  · have hz2 : ∀ y, z.2 (instanceIndex 1 j, y) = c₂ (instanceIndex 1 j, y) := fun y =>
      randomOracle.run_list_mapM_apply_of_forall_ne (fun i => (instanceIndex 0 j, be 8 i)) _
        (t := (instanceIndex 1 j, y)) (fun x _ h => h01 (congrArg Prod.fst h)) c₂ hz
    rw [randomOracle.run_eq, hz2, hfresh]
    simp only [hG, bind_assoc, pure_bind, map_pure]
    exact EvalDistEq.rfl
  · rw [← bind_map_left Prod.fst _ G, randomOracle.fst_map_run_list_mapM_of_fresh
      (fun i => (instanceIndex 0 j, be 8 i))]
    · have := (nodup_map_be_range msg).map (f := Prod.mk (instanceIndex 0 j))
        (fun _ _ h => (Prod.mk.inj h).2)
      rwa [List.map_map] at this
    · exact fun x _ => hfresh 0 _

omit [DecidableEq N] [SampleableType N] in
/-- An envelope at instances `(0, j)` and `(1, j)` leaves the cache of every other instance
unchanged. -/
private theorem run_sealBy_apply_of_ne (j : Fin qEnc) (pz : ByteArray) (nonce : N)
    (msg : Plaintext) (c : (instanceSpec qEnc).QueryCache) {y : Fin (2 * qEnc) × ByteArray}
    (hy : ∀ i, y.1 ≠ instanceIndex i j) {z : ByteArray × (instanceSpec qEnc).QueryCache}
    (hz : z ∈ support ((sealBy codec
      (fun x => (instanceSpec qEnc).randomOracle (instanceIndex 0 j, x))
      (fun x => (instanceSpec qEnc).randomOracle (instanceIndex 1 j, x)) pz nonce msg).run c)) :
    z.2 y = c y := by
  simp only [sealBy, StateT.run_bind, StateT.run_pure, support_bind, support_pure, Set.mem_iUnion,
    Set.mem_singleton_iff, exists_prop] at hz
  obtain ⟨a, ha, b, hb, rfl⟩ := hz
  rw [randomOracle.run_apply_of_ne (fun h => hy 1 (congrArg Prod.fst h).symm) _ hb]
  exact randomOracle.run_list_mapM_apply_of_forall_ne _ _
    (fun x _ h => hy 0 (congrArg Prod.fst h).symm) c ha

variable (n S L Salt Ctx N K) in
/-- The invariant of the joint state: no instance of an encryption that has not yet happened has
a cached point. -/
private def jointInv
    (s : (ℕ × (sealSpec n S L Salt Ctx N K).QueryCache) × (instanceSpec qEnc).QueryCache) :
    Prop :=
  ∀ (i : Fin 2) (j : Fin qEnc), s.1.1 ≤ j → ∀ x, s.2 (instanceIndex i j, x) = none

private theorem jointImpl_preservesInv (pz : ByteArray) (b : Bool) :
    QueryImpl.PreservesInv (jointImpl codec qEnc pz b) (jointInv n S L Salt Ctx N K qEnc) := by
  rintro t ⟨⟨j, c₁⟩, c₂⟩ hs z hz
  rcases t with (u | mm) | t
  · rw [jointImpl_unif] at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨x, -, rfl⟩ := hz
    exact hs
  · rw [jointImpl_challenge] at hz
    generalize (if b then mm.2 else mm.1) = msg at hz
    by_cases hl : plaintextLength mm.1 = plaintextLength mm.2
    · by_cases hj : j < qEnc
      · simp only [hl, hj, ↓reduceIte, ↓reduceDIte] at hz
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          exists_prop] at hz
        obtain ⟨nonce, -, v, hv, rfl⟩ := hz
        intro i j' hj' x
        have hne : ∀ i', (instanceIndex i j', x).1 ≠ instanceIndex i' ⟨j, hj⟩ := by
          intro i' h
          have := congrArg Fin.val (instanceIndex_injective h).2
          simp only at this hj'
          omega
        rw [run_sealBy_apply_of_ne codec qEnc ⟨j, hj⟩ pz nonce _ c₂ hne hv]
        exact hs i j' (by simp only at hj' ⊢; omega) x
      · simp only [hl, hj, ↓reduceIte, ↓reduceDIte] at hz
        rw [support_pure, Set.mem_singleton_iff] at hz
        subst hz
        intro i j' hj' x
        exact hs i j' (by simp only at hj' ⊢; omega) x
    · simp only [hl, ↓reduceIte] at hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hs
  · rw [jointImpl_seal] at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨v, -, rfl⟩ := hz
    exact hs

/-- On the reachable states, one step of `jointImpl` with the instance cache forgotten is a step
of the fresh game. -/
private theorem jointImpl_project (pz : ByteArray) (b : Bool)
    (t : (challengeSpec n S L Salt Ctx N K).Domain)
    (s : (ℕ × (sealSpec n S L Salt Ctx N K).QueryCache) × (instanceSpec qEnc).QueryCache)
    (hs : jointInv n S L Salt Ctx N K qEnc s) :
    Prod.map id Prod.fst <$> (jointImpl codec qEnc pz b t).run s =ᵈ
      (freshImpl codec qEnc pz b t).run s.1 := by
  obtain ⟨⟨j, c₁⟩, c₂⟩ := s
  rcases t with (u | mm) | t
  · rw [jointImpl_unif]
    simp [freshImpl]
  · rw [jointImpl_challenge]
    simp only [freshImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, LeftOrRight.oracle]
    generalize (if b then mm.2 else mm.1) = msg
    by_cases hl : plaintextLength mm.1 = plaintextLength mm.2
    · simp only [hl, ↓reduceIte]
      simp only [StateT.run_map, freshEncrypt, StateT.run_bind, StateT.run_get, StateT.run_set,
        pure_bind]
      by_cases hj : j < qEnc
      · simp only [hj, ↓reduceIte, ↓reduceDIte]
        simp only [StateT.run_liftM, map_bind, bind_assoc, map_pure]
        refine EvalDistEq.bind_right _ fun nonce => ?_
        have := (fst_map_run_sealBy_evalDistEq_of_fresh codec qEnc ⟨j, hj⟩ pz nonce msg c₂
          (fun i x => hs i ⟨j, hj⟩ le_rfl x)).map (fun r => (some r, (j + 1, c₁)))
        convert this using 1
        · simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, Prod.map,
            id]
        · simp only [map_eq_bind_pure_comp, Function.comp_def]
      · simp only [hj, ↓reduceIte, ↓reduceDIte]
        simp
    · simp only [hl, ↓reduceIte]
      simp
  · rw [jointImpl_seal]
    simp [freshImpl, Functor.map_map]

private theorem jointImpl_intertwinesOn (pz : ByteArray) (b : Bool) :
    QueryImpl.IntertwinesOn (jointInv n S L Salt Ctx N K qEnc) (fun s => pure s.1)
      (jointImpl codec qEnc pz b) (freshImpl codec qEnc pz b) := by
  intro t s hs γ _ f
  simp only [pure_bind]
  have h :=
    ((jointImpl_project codec qEnc pz b t s hs).bind_left (fun z => f z.1 z.2)).evalDist_eq
  rw [bind_map_left] at h
  exact h

/-! ## The ideal world does not depend on the hidden bit -/

/-- The online phase of the ideal world is the fresh game. -/
private theorem fst_map_simulateQ_jointImpl_evalDistEq (pz : ByteArray) (b : Bool) {α : Type}
    (X : OracleComp (challengeSpec n S L Salt Ctx N K) α)
    (s : (ℕ × (sealSpec n S L Salt Ctx N K).QueryCache) × (instanceSpec qEnc).QueryCache)
    (hs : jointInv n S L Salt Ctx N K qEnc s) :
    Prod.fst <$> (simulateQ (jointImpl codec qEnc pz b) X).run s =ᵈ
      Prod.fst <$> (simulateQ (freshImpl codec qEnc pz b) X).run s.1 := by
  let : MeasurableSpace α := ⊤
  refine EvalDistEq.of_evalDist_eq ?_
  have h := (jointImpl_intertwinesOn codec qEnc pz b).evalDist_simulateQ_run
    (jointImpl_preservesInv codec qEnc pz b) X s hs (fun a _ => (pure a : ProbComp α))
  simpa only [pure_bind, map_eq_bind_pure_comp, Function.comp_def] using h

private theorem freshImpl_evalDistEq_inl_inl (pz : ByteArray) (u : ℕ)
    (s : freshState n S L Salt Ctx N K) :
    (freshImpl codec qEnc pz true (.inl (.inl u))).run s =ᵈ
      (freshImpl codec qEnc pz false (.inl (.inl u))).run s := by
  exact EvalDistEq.rfl

private theorem freshImpl_evalDistEq_inr (pz : ByteArray) (t : (sealSpec n S L Salt Ctx N K).Domain)
    (s : freshState n S L Salt Ctx N K) :
    (freshImpl codec qEnc pz true (.inr t)).run s =ᵈ
      (freshImpl codec qEnc pz false (.inr t)).run s := by
  exact EvalDistEq.rfl

/-- The fresh game answers a left-or-right query alike at both hidden bits: the envelopes of two
messages of equal length with uniform keystream blocks and tag are equal in distribution. -/
private theorem freshImpl_evalDistEq_lr (pz : ByteArray) (mm : Plaintext × Plaintext)
    (s : freshState n S L Salt Ctx N K) :
    (freshImpl codec qEnc pz true (.inl (.inr mm))).run s =ᵈ
      (freshImpl codec qEnc pz false (.inl (.inr mm))).run s := by
  simp only [freshImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, LeftOrRight.oracle,
    Bool.false_eq_true, ite_true, ite_false]
  split_ifs with hl
  · simp only [StateT.run_map, freshEncrypt, StateT.run_bind, StateT.run_get, StateT.run_set,
      pure_bind]
    split_ifs with hj
    · refine EvalDistEq.map_congr _ ?_
      simp only [StateT.run_liftM]
      refine EvalDistEq.bind_left ?_ _
      exact EvalDistEq.bind_right _ fun nonce => sealBy_uniform_evalDistEq codec pz nonce hl.symm
    · exact EvalDistEq.rfl
  · exact EvalDistEq.rfl

/-- The fresh game answers every query alike at both hidden bits. -/
private theorem freshImpl_evalDistEq (pz : ByteArray)
    (t : (challengeSpec n S L Salt Ctx N K).Domain)
    (s : freshState n S L Salt Ctx N K) :
    (freshImpl codec qEnc pz true t).run s =ᵈ (freshImpl codec qEnc pz false t).run s := by
  rcases t with (u | mm) | t
  · exact freshImpl_evalDistEq_inl_inl codec qEnc pz u s
  · exact freshImpl_evalDistEq_lr codec qEnc pz mm s
  · exact freshImpl_evalDistEq_inr codec qEnc pz t s

variable [NeZero n] [AddCommGroup L] [SampleableType Salt]
  (mkCtx : Salt → Ctx) (initAcc : Ctx → S)
  (adv : HidingAdversary (sealSpec n S L Salt Ctx N K) (Puzzle n S L Salt) Plaintext ByteArray)

/-- The ideal world of the indexed run: the preprocessing and the generator against the random
oracle of the oracles with subkeys, then the online phase under `jointImpl`. -/
private theorem prfIdealExperiment_indexedRun_eq (b : Bool) :
    prfIdealExperiment (indexedRun m codec encodePuzzle qEnc mkCtx initAcc adv b) = (do
      let z ← (simulateQ (sealSpec n S L Salt Ctx N K).romImpl adv.preprocess).run ∅
      let z' ← (simulateQ (sealSpec n S L Salt Ctx N K).romImpl
        (simulateQ (sealSpec n S L Salt Ctx N K).unbatch
          (sealScheme n m mkCtx initAcc N K).gen)).run z.2
      Prod.fst <$> (simulateQ (jointImpl codec qEnc (encodePuzzle z'.1.1) b)
        (simulateQ (sealSpec n S L Salt Ctx N K).unbatch (adv.online z.1 z'.1.1))).run
          ((0, z'.2), ∅)) := by
  unfold prfIdealExperiment
  change (simulateQ prfIdealQueryImpl ((simulateQ (runImpl n S L Salt Ctx N K qEnc)
    (liftComp adv.preprocess (indexedSpec n S L Salt Ctx N K qEnc) >>= fun σ =>
      liftComp (simulateQ (sealSpec n S L Salt Ctx N K).unbatch
        (sealScheme n m mkCtx initAcc N K).gen) (indexedSpec n S L Salt Ctx N K qEnc) >>= fun x =>
      (simulateQ (challengerImpl codec qEnc (encodePuzzle x.1) b)
        (simulateQ (sealSpec n S L Salt Ctx N K).unbatch (adv.online σ x.1))).run' 0)).run'
      ∅)).run' ∅ = _
  simp only [run_liftComp_bind_eq, run_challenger_eq_jointImpl]

/-- **The ideal world does not depend on the hidden bit.** Against independent random functions
as instances, the indexed run has the same output distribution at both hidden bits. -/
theorem prfIdealExperiment_indexedRun_evalDistEq :
    prfIdealExperiment (indexedRun m codec encodePuzzle qEnc mkCtx initAcc adv true) =ᵈ
      prfIdealExperiment (indexedRun m codec encodePuzzle qEnc mkCtx initAcc adv false) := by
  rw [prfIdealExperiment_indexedRun_eq, prfIdealExperiment_indexedRun_eq]
  refine EvalDistEq.bind_right _ fun z => EvalDistEq.bind_right _ fun z' => ?_
  have hs : jointInv n S L Salt Ctx N K qEnc ((0, z'.2), ∅) := fun _ _ _ _ => rfl
  refine (fst_map_simulateQ_jointImpl_evalDistEq codec qEnc _ true _ _ hs).trans
    (EvalDistEq.trans ?_ (fst_map_simulateQ_jointImpl_evalDistEq codec qEnc _ false _ _ hs).symm)
  exact (evalDistEq_simulateQ_run _ _ (freshImpl_evalDistEq codec qEnc _) _ _).map Prod.fst

/-- **`G₃` does not depend on the hidden bit**: with random functions as instances, the indexed
run outputs `true` with the same probability at both hidden bits. -/
theorem prfIdealExperiment_indexedRun_true_eq_false :
    Pr{let g ← (prfIdealExperiment
        (indexedRun m codec encodePuzzle qEnc mkCtx initAcc adv true))}[g = true] =
      Pr{let g ← (prfIdealExperiment
        (indexedRun m codec encodePuzzle qEnc mkCtx initAcc adv false))}[g = true] :=
  (prfIdealExperiment_indexedRun_evalDistEq codec encodePuzzle qEnc mkCtx initAcc
    adv).prEvent_eq _

/-- **The PRF step**: the gap between the two hidden bits of the indexed hybrid against
independent keys of `prf` is at most twice the advantage of the hiding distinguisher. -/
theorem absDiff_indexed_le_prfAdvantage (prf : PRFScheme K ByteArray (Bytes 32)) :
    ENNReal.absDiff
      (Pr{let g ← ((prf.multiKey (Fin (2 * qEnc))).prfRealExperiment
        (indexedRun m codec encodePuzzle qEnc mkCtx initAcc adv true))}[g = true])
      (Pr{let g ← ((prf.multiKey (Fin (2 * qEnc))).prfRealExperiment
        (indexedRun m codec encodePuzzle qEnc mkCtx initAcc adv false))}[g = true]) ≤
      2 * (prf.multiKey (Fin (2 * qEnc))).prfAdvantage
        (hidingDistinguisher m codec encodePuzzle qEnc mkCtx initAcc adv) :=
  (absDiff_prfRealExperiment_eq_two_mul_prfAdvantage _
    (indexedRun m codec encodePuzzle qEnc mkCtx initAcc adv)
    (prfIdealExperiment_indexedRun_true_eq_false codec encodePuzzle qEnc mkCtx initAcc
      adv)).le

end PointerChainPuzzle
