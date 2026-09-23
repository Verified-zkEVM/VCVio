/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.Chain
public import VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.Compatibility
public import VCVio.CryptoFoundations.HardnessAssumptions.HardRelation
public import VCVio.EvalDist.Inequalities

/-!
# Fiat-Shamir reductions for Sigma protocols

This file defines the two reductions behind the EUF-CMA security of the Fiat-Shamir
transform of a Sigma protocol and proves their quantitative bounds.

- `cmaToNmaAdv` turns an EUF-CMA adversary into a managed random-oracle NMA adversary
  (`Stateful.nmaAdvFromCmaWithFinalQuery`), and `cma_to_nma_advantage_bound` bounds the
  CMA advantage by the fork advantage of that adversary plus the simulation loss. The proof
  is discharged by the direct stateful game chain.
- `nmaReduction` turns a managed random-oracle NMA adversary into a witness-finding algorithm
  by replaying the forking lemma and applying special-soundness extraction, and
  `nma_to_hard_relation_bound` bounds its success probability in `hardRelationExperiment`.
- `cmaReduction` is the composite witness-finding algorithm.

Every bound names the reduction it is about. A statement of the form
`∃ reduction, bound ≤ Pr[= true | hardRelationExperiment hr reduction]` would be satisfied by a
reduction that returns a valid witness chosen classically, so it would carry no security
content. -/

@[expose] public section

namespace FiatShamir

open OracleComp OracleSpec
open scoped OracleSpec.PrimitiveQuery

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel) (M : Type)

noncomputable local instance instIsUniformSpecChalSingleton [Fintype Chal] [Inhabited Chal] :
    IsUniformSpec ((Unit →ₒ Chal) : OracleSpec _) :=
  IsUniformSpec.ofFintypeInhabited _

noncomputable local instance instIsUniformSpecChalFn [Fintype Chal] [Inhabited Chal]
    (M Commit : Type) : IsUniformSpec ((M × Commit →ₒ Chal) : OracleSpec _) :=
  IsUniformSpec.ofFintypeInhabited _

/-- CMA-to-NMA reduction for Fiat-Shamir signatures built from a Sigma protocol: run the
EUF-CMA adversary against simulated signing transcripts and a managed random oracle, then issue
one live random-oracle query at the forgery's hash point. -/
abbrev cmaToNmaAdv
    [DecidableEq M] [DecidableEq Commit]
    (simTranscript : Stmt → ProbComp (Commit × Chal × Resp))
    (adv : SignatureAlg.UnforgeableAdversary
      (FiatShamir.inROM σ hr M)) :
    SignatureAlg.ManagedRoNmaAdversary
      (FiatShamir.inROM σ hr M) :=
  Stateful.nmaAdvFromCmaWithFinalQuery σ hr M adv simTranscript

/-- CMA-to-NMA bound for Fiat-Shamir signatures built from a Sigma protocol.

The reduction `cmaToNmaAdv` runs the CMA adversary with simulated signing transcripts and a
managed random oracle, then appends a single explicit live random-oracle query
for the forgery's hash point so that the verification challenge is part of the
forkable transcript. The quantitative
loss is the HVZK simulation cost plus the programming-collision term from
simulator commit predictability; no separate verifier-guessing slack is needed.

The bound is stated against `Fork.advantage σ hr M (cmaToNmaAdv σ hr M simTranscript adv) qH`:
the wrapped
adversary issues `qH + 1` random-oracle queries, and `Fork.forkPoint qH`
indexes `Fin (qH + 1)`, which is exactly the right number of forkable slots
(the framework's structural `+1` in `Fin (qH + 1)` is precisely the wrapper's
verifier slot). The replay-forking denominator is therefore `qH + 1`. -/
theorem cma_to_nma_advantage_bound
    [DecidableEq M] [DecidableEq Commit] [SampleableType Stmt] [SampleableType Wit]
    [Finite Stmt] [Finite Chal] [Inhabited Chal] [SampleableType Chal]
    (simTranscript : Stmt → ProbComp (Commit × Chal × Resp))
    (ζ_zk : ℝ) (hζ_zk : 0 ≤ ζ_zk)
    (hHVZK : σ.HVZK simTranscript ζ_zk)
    (β : ENNReal)
    (hPredSim : σ.simCommitPredictability simTranscript β)
    (adv : SignatureAlg.UnforgeableAdversary
      (FiatShamir.inROM σ hr M))
    (qS qH : ℕ)
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    SignatureAlg.unforgeableAdvantage (runtime M) adv ≤
      Fork.advantage σ hr M (cmaToNmaAdv σ hr M simTranscript adv) qH +
        ENNReal.ofReal ((qS : ℝ) * ζ_zk) + (qS : ENNReal) * (qS + qH) * β :=
  Stateful.cma_advantage_le_fork_bound_of_h1h2 σ hr M
      simTranscript ζ_zk hζ_zk hHVZK β hPredSim adv qS qH hQ
      (le_of_eq <| (Stateful.unforgeableAdvantage_eq_statefulPostKeygenFreshAdvantage
          (σ := σ) (hr := hr) (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) adv).trans
        (Stateful.statefulPostKeygenFreshAdvantage_eq_cmaRealRunProb_signedFreshAdv
          (σ := σ) (hr := hr) (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) adv))

section probabilityPreservation

variable [SampleableType Chal]

/-- Forwarding uniform queries and sampling challenge responses preserves event probabilities. -/
private lemma probEvent_simulateQ_unifChalImpl [Fintype Chal] [Inhabited Chal] {α : Type}
    (oa : OracleComp (unifSpec + (Unit →ₒ Chal)) α) (p : α → Prop) :
    Pr[ p | simulateQ (QueryImpl.ofLift unifSpec ProbComp +
      (uniformSampleImpl (spec := (Unit →ₒ Chal)))) oa] = Pr[ p | oa] := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure x => simp only [simulateQ_pure, probEvent_pure]
  | query_bind t cont ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
        OracleQuery.input_query, probEvent_bind_eq_tsum, ih]
      refine tsum_congr fun u => ?_
      congr 1
      cases t with
      | inl n =>
          simp only [QueryImpl.add_apply_inl, QueryImpl.ofLift_eq_id', QueryImpl.id'_apply,
            probOutput_query, ← Nat.card_eq_fintype_card]
          rfl
      | inr t =>
          simp only [QueryImpl.add_apply_inr, uniformSampleImpl]
          exact probOutput_uniformSample_eq_query (spec := unifSpec + (Unit →ₒ Chal))
            (.inr t) u

end probabilityPreservation

section nmaToExtraction

variable [DecidableEq M] [DecidableEq Commit]

/-- Replay-fork query budget for the NMA reduction: forward the `.inl unifSpec` component
live and rewind only the counted challenge oracle on the `.inr` side. -/
def nmaForkBudget (qH : ℕ) : ℕ ⊕ Unit → ℕ
  | .inl _ => 0
  | .inr () => qH

/-- Per-run invariant for the NMA replay fork. If `Fork.forkPoint qH` selects index `s`,
the cached RO value at `x.target`, the outer log's `s`-th counted-oracle response, and the
challenge under which `x.forgery` verifies all coincide. -/
private def forkSupportInvariant
    (qH : ℕ) (pk : Stmt)
    (x : Fork.Trace Commit Chal Resp M)
    (log : QueryLog (unifSpec + (Unit →ₒ Chal))) : Prop :=
  ∀ s : Fin (qH + 1),
    Fork.forkPoint Commit Chal Resp M qH x =
        some s →
    ∃ ω : Chal,
      QueryLog.getQueryValue? log (Sum.inr ()) (↑s : ℕ) = some ω ∧
      x.roCache x.target = some ω ∧
      σ.verify pk x.target.2 ω x.forgery.2.2 = true

/-- Every `(x, log)` in the support of `replayFirstRun (Fork.runTrace σ hr M nmaAdv pk)`
satisfies the per-run invariant `forkSupportInvariant`. -/
private theorem forkSupportInvariant_of_mem_replayFirstRun [SampleableType Chal]
    (nmaAdv : SignatureAlg.ManagedRoNmaAdversary
      (FiatShamir.inROM σ hr M))
    (qH : ℕ) (pk : Stmt)
    {x : Fork.Trace Commit Chal Resp M}
    {log : QueryLog (unifSpec + (Unit →ₒ Chal))}
    (h : (x, log) ∈ support (replayFirstRun (Fork.runTrace σ hr M nmaAdv pk))) :
    forkSupportInvariant σ M qH pk x log := by
  classical
  intro s hs
  have htarget : x.queryLog[(↑s : ℕ)]? = some x.target :=
    Fork.forkPoint_getElem?_eq_some_target (M := M) (Commit := Commit) (Resp := Resp)
      (Chal := Chal) hs
  have hverified : x.verified = true :=
    Fork.verified_of_forkPoint_eq_some (M := M) (Commit := Commit) (Resp := Resp)
      (Chal := Chal) hs
  obtain ⟨hslt, htgt_eq⟩ := List.getElem?_eq_some_iff.1 htarget
  obtain ⟨ω, hcache_idx, hlog⟩ :=
    Fork.runTrace_cache_outer_lockstep σ hr M nmaAdv pk h (↑s : ℕ) hslt
  rw [htgt_eq] at hcache_idx
  obtain ⟨ω', hcache', hverify⟩ :=
    Fork.exists_cached_verify_of_runTrace_verified σ hr M nmaAdv pk h hverified
  refine ⟨ω, hlog, hcache_idx, ?_⟩
  rwa [Option.some.inj (hcache'.symm.trans hcache_idx)] at hverify

variable [DecidableEq Chal] [SampleableType Wit] [SampleableType Chal]

/-- The branch the NMA extractor takes on a forking-lemma result: from two traces sharing a
commitment whose distinct cached challenges accept, run `σ.extract`; otherwise resample. This is
the post-`contextFork` continuation of `nmaForkExtract`. -/
def nmaForkExtractBranch :
    Option (Fork.Trace Commit Chal Resp M × Fork.Trace Commit Chal Resp M) →
      OracleComp (unifSpec + (Unit →ₒ Chal)) Wit
  | none => liftComp ($ᵗ Wit) (unifSpec + (Unit →ₒ Chal))
  | some (x₁, x₂) =>
    let ⟨m₁, (c₁, s₁)⟩ := x₁.forgery
    let ⟨m₂, (c₂, s₂)⟩ := x₂.forgery
    if _hc : c₁ = c₂ then
      match x₁.roCache (m₁, c₁), x₂.roCache (m₂, c₂) with
      | some ω₁, some ω₂ =>
          if _hω : ω₁ ≠ ω₂ then
            liftComp (σ.extract ω₁ s₁ ω₂ s₂) (unifSpec + (Unit →ₒ Chal))
          else liftComp ($ᵗ Wit) (unifSpec + (Unit →ₒ Chal))
      | _, _ => liftComp ($ᵗ Wit) (unifSpec + (Unit →ₒ Chal))
    else
      liftComp ($ᵗ Wit) (unifSpec + (Unit →ₒ Chal))

/-- Witness-extraction computation used by the NMA reduction: replay the forking lemma, then
take the `nmaForkExtractBranch` continuation on the resulting trace pair. -/
def nmaForkExtract
    (nmaAdv : SignatureAlg.ManagedRoNmaAdversary
      (FiatShamir.inROM σ hr M))
    (qH : ℕ) (pk : Stmt) :
    OracleComp (unifSpec + (Unit →ₒ Chal)) Wit :=
  contextFork (Fork.runTrace σ hr M nmaAdv pk) (nmaForkBudget qH) (Sum.inr ())
    (Fork.forkPoint Commit Chal Resp M qH) >>=
    nmaForkExtractBranch (M := M) (Chal := Chal) σ

/-- NMA-to-witness reduction: run `nmaForkExtract`, answering its unit-indexed challenge oracle
with fresh uniform samples, so that the result is a `ProbComp` witness finder for
`hardRelationExperiment`. -/
def nmaReduction
    (nmaAdv : SignatureAlg.ManagedRoNmaAdversary
      (FiatShamir.inROM σ hr M))
    (qH : ℕ) : Stmt → ProbComp Wit := fun pk =>
  simulateQ (QueryImpl.ofLift unifSpec ProbComp +
    (uniformSampleImpl (spec := (Unit →ₒ Chal)))) (nmaForkExtract σ hr M nmaAdv qH pk)

variable [Fintype Chal] [Inhabited Chal]

/-- Discrete response spaces for the uniform replay experiment. -/
local instance replayResponseMeasurable :
    ∀ t, MeasurableSpace ((Fork.wrappedSpec Chal).Range t) := fun _ => ⊤

local instance replayResponseDiscrete :
    ∀ t, DiscreteMeasurableSpace ((Fork.wrappedSpec Chal).Range t) := fun _ => inferInstance

/-- The replay experiment uses native uniform response measures. -/
noncomputable local instance replayUniformMeasure : IsUniformMeasureSpec (Fork.wrappedSpec Chal) :=
  IsUniformMeasureSpec.ofFiniteNonempty _

/-- At a fixed statement, combine replay forking with the supported special-soundness
extractor. The measure statement uses the native uniform-oracle interpretation; the
existing discrete replay theorem is consumed at this compatibility boundary. -/
private theorem perPk_extraction_bound
    (nmaAdv : SignatureAlg.ManagedRoNmaAdversary
      (FiatShamir.inROM σ hr M))
    (qH : ℕ) (hss : σ.SpeciallySound) (pk : Stmt) :
    let acc := Pr{let t ← Fork.runTrace σ hr M nmaAdv pk}[(Fork.forkPoint _ _ _ M qH t).isSome]
    acc * (acc / (qH + 1 : ENNReal) - challengeSpaceInv Chal) ≤
      Pr{let w ← nmaReduction σ hr M nmaAdv qH pk}[rel pk w = true] := by
  classical
  have hss_nf : ∀ ω₁ p₁ ω₂ p₂, Pr[⊥ | σ.extract ω₁ p₁ ω₂ p₂] = 0 :=
    fun _ _ _ _ => probFailure_eq_zero' inferInstance
  have hExtract :
      Pr[ fun r : Option
          (Fork.Trace Commit Chal Resp M × Fork.Trace Commit Chal Resp M) =>
          ∃ (x₁ x₂ : Fork.Trace Commit Chal Resp M)
            (s : Fin (qH + 1)) (log₁ log₂ : QueryLog (unifSpec + (Unit →ₒ Chal))),
            r = some (x₁, x₂) ∧
            Fork.forkPoint Commit Chal Resp M qH x₁ = some s ∧
            Fork.forkPoint Commit Chal Resp M qH x₂ = some s ∧
            QueryLog.getQueryValue? log₁ (Sum.inr ()) ↑s ≠
              QueryLog.getQueryValue? log₂ (Sum.inr ()) ↑s ∧
            forkSupportInvariant σ M qH pk x₁ log₁ ∧
            forkSupportInvariant σ M qH pk x₂ log₂
          | contextFork (Fork.runTrace σ hr M nmaAdv pk) (nmaForkBudget qH) (Sum.inr ())
            (Fork.forkPoint Commit Chal Resp M qH)] ≤
        Pr[ fun w : Wit => rel pk w = true | nmaReduction σ hr M nmaAdv qH pk] := by
    classical
    let chalSpec : OracleSpec Unit := Unit →ₒ Chal
    let wrappedMain := Fork.runTrace σ hr M nmaAdv pk
    let cf := Fork.forkPoint Commit Chal Resp M qH
    let qb : ℕ ⊕ Unit → ℕ := nmaForkBudget qH
    rw [show Pr[fun w : Wit => rel pk w = true | nmaReduction σ hr M nmaAdv qH pk] =
          Pr[fun w : Wit => rel pk w = true | nmaForkExtract σ hr M nmaAdv qH pk] by
        unfold nmaReduction
        exact probEvent_simulateQ_unifChalImpl _ _]
    set branchFn := nmaForkExtractBranch (M := M) (Chal := Chal) σ with hbranchFn_def
    have hforkExtract_eq : nmaForkExtract σ hr M nmaAdv qH pk =
        contextFork wrappedMain qb (Sum.inr ()) cf >>= branchFn := rfl
    rw [hforkExtract_eq, probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
    refine ENNReal.tsum_le_tsum fun r => ?_
    by_cases hE :
        ∃ (x₁ x₂ : Fork.Trace Commit Chal Resp M)
          (s : Fin (qH + 1)) (log₁ log₂ : QueryLog (unifSpec + (Unit →ₒ Chal))),
          r = some (x₁, x₂) ∧
          cf x₁ = some s ∧
          cf x₂ = some s ∧
          QueryLog.getQueryValue? log₁ (Sum.inr ()) ↑s ≠
            QueryLog.getQueryValue? log₂ (Sum.inr ()) ↑s ∧
          forkSupportInvariant σ M qH pk x₁ log₁ ∧
          forkSupportInvariant σ M qH pk x₂ log₂
    swap
    · rw [ite_eq_right hE]
      exact zero_le
    rw [ite_eq_left hE]
    by_cases hsupp : r ∈ support (contextFork wrappedMain qb (Sum.inr ()) cf)
    swap
    · rw [probOutput_eq_zero_of_not_mem_support hsupp, zero_mul]
    obtain ⟨x₁, x₂, s, log₁, log₂, hreq, hcf₁, hcf₂, hneq, hP₁, hP₂⟩ := hE
    obtain ⟨ω₁, hlog₁, hcache₁, hverify₁⟩ := hP₁ s hcf₁
    obtain ⟨ω₂, hlog₂, hcache₂, hverify₂⟩ := hP₂ s hcf₂
    simp only [Fork.Trace.target] at hcache₁ hcache₂ hverify₁ hverify₂
    have hω_ne : ω₁ ≠ ω₂ := fun heq => hneq (by rw [hlog₁, hlog₂, heq])
    -- The two forgeries share a target hash point, so they share a commitment.
    have hc_eq : x₁.forgery.2.1 = x₂.forgery.2.1 :=
      congrArg Prod.snd <| Fork.runTrace_target_eq_of_mem_contextFork σ hr M nmaAdv qH pk
        x₁ x₂ s (hreq ▸ hsupp) hcf₁ hcf₂
    -- On the live fork event, `branchFn` reduces to the witness extractor `σ.extract`.
    have hbranch : branchFn r = liftComp (σ.extract ω₁ x₁.forgery.2.2 ω₂ x₂.forgery.2.2)
        (unifSpec + chalSpec) := by
      rw [hbranchFn_def, hreq]
      simp only [chalSpec, nmaForkExtractBranch, hcache₁, hcache₂,
        dite_eq_left hc_eq, dite_eq_left hω_ne]
    rw [hbranch, probEvent_liftComp]
    -- The extractor returns a valid witness with probability one (special soundness).
    rw [show Pr[fun w : Wit => rel pk w = true |
          σ.extract ω₁ x₁.forgery.2.2 ω₂ x₂.forgery.2.2] = 1 from
      probEvent_eq_one_iff.2 ⟨hss_nf _ _ _ _, fun w hw =>
        SigmaProtocol.extract_sound_of_speciallySoundAt σ (hss pk) hω_ne hverify₁
          (hc_eq.symm ▸ hverify₂) hw⟩, mul_one]
  have hFork := (Fork.replayForkingBound (σ := σ) (hr := hr) (M := M) nmaAdv qH pk
    (P_out := forkSupportInvariant σ M qH pk)
    (hP := fun h => forkSupportInvariant_of_mem_replayFirstRun σ hr M nmaAdv qH pk h)
    (hreach := Fork.runTrace_forkPoint_CfReachable
      (σ := σ) (hr := hr) (M := M) nmaAdv qH pk)).trans hExtract
  dsimp only
  simpa only [evalDist_apply_singleton, probOutput_bind_eq_tsum, probOutput_pure,
    probEvent_eq_tsum_ite, Bool.coe_iff_coe, eq_iff_iff, true_iff,
      mul_ite, mul_one, mul_zero] using hFork

/-- The named replay extractor's valid-witness probability at a fixed statement.
`acc` is forkable acceptance, whose identification with actual verification requires a
final verifier query and a query bound on the wrapped prover. Failed forks use the
reduction's explicit uniform-witness fallback. -/
theorem pointwise_extraction_bound
    (nmaAdv : SignatureAlg.ManagedRoNmaAdversary
      (FiatShamir.inROM σ hr M))
    (qH : ℕ) (hss : σ.SpeciallySound) (pk : Stmt) :
    let acc := Pr{let t ← Fork.runTrace σ hr M nmaAdv pk}[(Fork.forkPoint _ _ _ M qH t).isSome]
    acc * (acc / (qH + 1 : ENNReal) - challengeSpaceInv Chal) ≤
      Pr{let w ← nmaReduction σ hr M nmaAdv qH pk}[rel pk w = true] :=
  perPk_extraction_bound σ hr M nmaAdv qH hss pk

end nmaToExtraction

/-- The challenge-space reciprocal `(Fintype.card Chal)⁻¹` is finite. -/
@[aesop (rule_sets := [finiteness]) safe apply]
lemma challengeSpaceInv_ne_top [Fintype Chal] [Nonempty Chal] : challengeSpaceInv Chal ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top <|
    ENNReal.inv_le_one.2 (by exact_mod_cast Fintype.card_pos)

/-- NMA-to-extraction via the forking lemma and special soundness: the witness-finding
algorithm `nmaReduction σ hr M nmaAdv qH` succeeds in `hardRelationExperiment` with probability at
least `acc · (acc / (qH + 1) - 1/|Chal|)`, where `acc` is the fork advantage of `nmaAdv`.

The parameter `qH` is the *fork slot parameter* passed to `Fork.forkPoint qH`,
i.e., the number of `Fin (qH + 1)` candidate target positions over which the
replay-forking lemma sums. It is *not* required to be a valid query bound on
the adversary: callers may supply a wrapped adversary with up to `qH + 1`
queries (the framework's structural `+1` in `Fin (qH + 1)` accommodates the
extra slot). -/
theorem nma_to_hard_relation_bound
    [DecidableEq M] [DecidableEq Commit] [DecidableEq Chal]
    [SampleableType Wit] [SampleableType Chal]
    (hss : σ.SpeciallySound)
    (hss_nf : ∀ ω₁ p₁ ω₂ p₂, Pr[⊥ | σ.extract ω₁ p₁ ω₂ p₂] = 0)
    [Fintype Chal] [Inhabited Chal]
    (nmaAdv : SignatureAlg.ManagedRoNmaAdversary
      (FiatShamir.inROM σ hr M))
    (qH : ℕ) :
    Fork.advantage σ hr M nmaAdv qH *
        (Fork.advantage σ hr M nmaAdv qH / (qH + 1 : ENNReal) - challengeSpaceInv Chal) ≤
      Pr[= true | hardRelationExperiment hr (nmaReduction σ hr M nmaAdv qH)] := by
  classical
  -- Retain the public losslessness premise for callers of the compatibility theorem.
  have _ := hss_nf
  set acc : Stmt → ENNReal := fun pk =>
    Pr[ fun x => (Fork.forkPoint Commit Chal Resp M qH x).isSome |
      Fork.runTrace σ hr M nmaAdv pk] with hacc_def
  have hAdv_eq_tsum :
      Fork.advantage σ hr M nmaAdv qH =
        ∑' pkw : Stmt × Wit, Pr[= pkw | hr.gen] * acc pkw.1 := by
    simp only [Fork.advantage, Fork.exp, ← probEvent_eq_eq_probOutput,
      probEvent_simulateQ_unifChalImpl, probEvent_bind_eq_tsum, bind_pure_comp,
      probEvent_map, Function.comp_def, probEvent_liftComp, acc]
  have hRHS_eq_tsum :
      Pr[= true | hardRelationExperiment hr (nmaReduction σ hr M nmaAdv qH)] =
        ∑' pkw : Stmt × Wit, Pr[= pkw | hr.gen] *
          Pr[ fun w : Wit => rel pkw.1 w = true |
            nmaReduction σ hr M nmaAdv qH pkw.1] := by
    simp only [hardRelationExperiment, ← probEvent_eq_eq_probOutput, bind_pure_comp,
      probEvent_bind_eq_tsum, probEvent_map, Function.comp_def]
  -- The replay-forking bound feeds the per-`pk` witness-extraction bound.
  have hPerPkFinal : ∀ pk : Stmt,
      acc pk * (acc pk / (qH + 1 : ENNReal) - challengeSpaceInv Chal) ≤
        Pr[ fun w : Wit => rel pk w = true |
          nmaReduction σ hr M nmaAdv qH pk] := by
    intro pk
    simpa only [acc, evalDist_apply_singleton, probOutput_bind_eq_tsum, probOutput_pure,
      probEvent_eq_tsum_ite, Bool.coe_iff_coe, eq_iff_iff, true_iff,
      mul_ite, mul_one, mul_zero] using
      pointwise_extraction_bound σ hr M nmaAdv qH hss pk

  rw [hAdv_eq_tsum, hRHS_eq_tsum]
  simpa only [DiscreteEvalDistCompatible.lintegral_evalDist _ (g := fun a ↦ a) measurable_id,
    ← OracleComp.EvalDist.expectedValue_def, OracleComp.EvalDist.expectedValue_map] using
    OracleComp.EvalDist.marginalized_jensen_forking_bound_map (mx := hr.gen)
    (acc := fun pkw => acc pkw.1)
    (B := fun pkw => Pr[ fun w : Wit => rel pkw.1 w = true |
      nmaReduction σ hr M nmaAdv qH pkw.1])
    (q := (qH : ENNReal) + 1) (hinv := challengeSpaceInv Chal)
    (fun _ => probEvent_le_one) (fun pkw => hPerPkFinal pkw.1)

/-- CMA-to-witness reduction for Fiat-Shamir signatures built from a Sigma protocol: the
NMA-to-witness reduction `nmaReduction` applied to the CMA-to-NMA adversary `cmaToNmaAdv`,
with fork slot parameter `qH`. -/
abbrev cmaReduction
    [DecidableEq M] [DecidableEq Commit] [DecidableEq Chal]
    [SampleableType Wit] [SampleableType Chal]
    (simTranscript : Stmt → ProbComp (Commit × Chal × Resp))
    (adv : SignatureAlg.UnforgeableAdversary
      (FiatShamir.inROM σ hr M))
    (qH : ℕ) : Stmt → ProbComp Wit :=
  nmaReduction σ hr M (cmaToNmaAdv σ hr M simTranscript adv) qH

end FiatShamir
