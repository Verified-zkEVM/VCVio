/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import ToMathlib.Probability.UniformOn
public import VCVio.CryptoFoundations.CoordinateFork.SpecialSoundness

/-!
# A fixed-statement extraction bound for coordinate-wise special soundness

This module proves the fixed-statement, table-model extraction-success inequality underlying the
`μ = 1` case of Lemma 2.31 of Fenzi–Moghaddas–Nguyen. Composing the coordinate-wise table fork with
an extensional `ℓ`-coordinate-wise `k`-special sound extractor yields a valid witness with
probability at least `ε - ℓ(k-1)/|S|`, where `ε` is the prover's accepting probability.

`coordExtract` is the composite: fork on the prover's response table to obtain `ℓ(k-1)+1` accepting
transcripts whose challenges are `SS(S, ℓ, k)`, then hand them to `ext`. Its success event is
`∃ w, r = some w ∧ rel x w`, which no aborting run satisfies — so the bound is a statement about
witnesses produced, not merely about the extractor terminating.

The input `P : ProbComp ((ι → S) → Resp)` is a distribution of complete response tables after the
commitment `pc`. This can encode a responder whose coins are fixed before answering challenges,
but no theorem here derives such a table distribution, or its cross-rewind coupling, from an
interactive malicious prover. Query count is also absent; see `CoordinateFork.lean` and
`docs/agents/forking.md`.

This is not the paper's full knowledge-soundness theorem: it has no security-parameter
quantification, joint bad-event experiment, oracle-query semantics, or expected-polynomial-time
claim. Only `μ = 1` is represented.
-/

public section

open Finset CoordinateWise OracleComp MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace SigmaProtocol

variable {Stmt Wit Commit PrvState Resp : Type} {rel : Stmt → Wit → Bool}
variable {ι S : Type} [DecidableEq ι] [Fintype ι] [DecidableEq S] [Fintype S]
variable [SampleableType (ι → S)] [DecidableEq Resp]
variable {k : ℕ} {x : Stmt}

/-- The composite extractor: run the coordinate-wise fork against the prover's response table, then
apply the `k`-ary extractor to the accepting transcripts it returns. Aborts exactly when the fork
does. -/
@[expose] noncomputable def coordExtract
    (σ : SigmaProtocol Stmt Wit Commit PrvState (ι → S) Resp rel)
    (k : ℕ) (ext : Stmt → Commit → Finset ((ι → S) × Resp) → ProbComp Wit) (x : Stmt)
    (pc : Commit)
    (P : ProbComp ((ι → S) → Resp)) : ProbComp (Option Wit) :=
  coordForkT (σ.verify x pc) k P >>= fun r =>
    match r with
    | none => pure none
    | some (τ, X) => some <$> ext x pc (transcripts τ X)

/-- The event that the composite extractor produced a valid witness. Aborting runs fail it, so a
bound on this event is not a bound on termination. -/
@[expose] def Extracted (rel : Stmt → Wit → Bool) (x : Stmt) (r : Option Wit) : Prop :=
  ∃ w, r = some w ∧ rel x w = true

@[simp] theorem not_extracted_none : ¬ Extracted rel x none := by
  simp [Extracted]

omit [DecidableEq ι] [Fintype S] [SampleableType (ι → S)] in
/-- A good fork is exactly a coordinate-wise special sound set of accepting transcripts.

Naming this makes the fork's output usable without the extractor: it is the hypothesis of
`CoordSpeciallySoundAt`, and `CoordinateWise.IsCoordSpecialSoundTranscripts.exists_pair` reads a
verified pair off it in any prescribed coordinate. -/
theorem isCoordSpecialSoundTranscripts_of_goodTranscripts
    {σ : SigmaProtocol Stmt Wit Commit PrvState (ι → S) Resp rel} {pc : Commit}
    {τ : (ι → S) → Resp} {X : Finset (ι → S)}
    (hgood : GoodTranscripts (σ.verify x pc) k (some (τ, X))) :
    IsCoordSpecialSoundTranscripts (σ.verify x pc) k (transcripts τ X) := by
  rw [goodTranscripts_some_iff] at hgood
  obtain ⟨hsound, hacc⟩ := hgood
  refine ⟨fun p hp => ?_, ?_⟩
  · obtain ⟨c, y⟩ := p
    obtain ⟨h1, rfl⟩ := mem_transcripts.mp hp
    exact hacc c h1
  · rwa [image_fst_transcripts]

omit [DecidableEq ι] [Fintype S] [SampleableType (ι → S)] in
/-- On a good fork the composite extractor certainly produces a valid witness. -/
theorem prEvent_extracted_eq_one_of_goodTranscripts
    {σ : SigmaProtocol Stmt Wit Commit PrvState (ι → S) Resp rel}
    {ext : Stmt → Commit → Finset ((ι → S) × Resp) → ProbComp Wit} {pc : Commit}
    (hss : σ.CoordSpeciallySoundAt k ext x) {τ : (ι → S) → Resp} {X : Finset (ι → S)}
    (hgood : GoodTranscripts (σ.verify x pc) k (some (τ, X))) :
    Pr{let r ← (some <$> ext x pc (transcripts τ X) : ProbComp (Option Wit))}[Extracted rel x r]
      = 1 := by
  rw [prEvent_map]
  refine prEvent_eq_one_of_forall_mem_support _ _ fun w hw => ⟨w, rfl, ?_⟩
  exact hss pc (transcripts τ X) (isCoordSpecialSoundTranscripts_of_goodTranscripts hgood) w hw

/-- The fixed-statement, table-model extraction-success inequality underlying the `μ = 1`
Σ-protocol case of **Lemma 2.31**. Against an extensional `ℓ`-coordinate-wise `k`-special sound
extractor, the composite returns a valid witness with probability at least `ε - ℓ(k-1)/|S|`,
where `ε` is the probability that the prover's response is accepted on a uniform challenge.

This theorem alone is not a knowledge-soundness definition or an efficiency theorem. -/
theorem sub_div_le_prEvent_extracted_coordExtract [Nonempty S]
    (σ : SigmaProtocol Stmt Wit Commit PrvState (ι → S) Resp rel) (k : ℕ)
    (ext : Stmt → Commit → Finset ((ι → S) × Resp) → ProbComp Wit) (x : Stmt)
    (hss : σ.CoordSpeciallySoundAt k ext x) (pc : Commit)
    (P : ProbComp ((ι → S) → Resp)) :
    acceptRatio (acceptTable (σ.verify x pc) P)
        - (Fintype.card ι : ℝ≥0∞) * (k - 1 : ℕ) / Fintype.card S
      ≤ Pr{let r ← σ.coordExtract k ext x pc P}[Extracted rel x r] := by
  refine (sub_div_le_prEvent_goodTranscripts_coordForkT (σ.verify x pc) k P).trans ?_
  rw [coordExtract]
  refine le_of_eq_of_le (mul_one _).symm
    (mul_le_prEvent_bind_of_forall _ _ _ _ le_rfl fun r hgood => ?_)
  obtain ⟨τ, X, rfl, hpay⟩ := hgood
  exact le_of_eq (prEvent_extracted_eq_one_of_goodTranscripts hss ⟨τ, X, rfl, hpay⟩).symm

/-! ## Sampling the first message

The bound above fixes the prover's first message. Averaging it over a distribution of
`(pc, τ)` pairs covers commitment generation as well: the prover picks a first message and, with
its coins then fixed, the table of responses it will give. Only the first message is added; the
challenge is still uniform and the response table is still pre-sampled. -/

section Commit

/-- The composite extractor when the prover chooses its first message too. -/
@[expose] noncomputable def coordExtractCommit
    (σ : SigmaProtocol Stmt Wit Commit PrvState (ι → S) Resp rel)
    (k : ℕ) (ext : Stmt → Commit → Finset ((ι → S) × Resp) → ProbComp Wit) (x : Stmt)
    (P : ProbComp (Commit × ((ι → S) → Resp))) : ProbComp (Option Wit) :=
  P >>= fun p => σ.coordExtract k ext x p.1 (pure p.2)

/-- The `ε` of the bound below: the probability that the prover's transcript verifies, over its own
first message and response table and a uniform challenge. -/
@[expose] noncomputable def verifyProb
    (σ : SigmaProtocol Stmt Wit Commit PrvState (ι → S) Resp rel)
    (x : Stmt) (P : ProbComp (Commit × ((ι → S) → Resp))) : ℝ≥0∞ :=
  Pr{let p ← P; let c ← $ᵗ (ι → S)}[σ.verify x p.1 c (p.2 c)]

omit [DecidableEq S] [DecidableEq Resp] in
/-- For an already-fixed response table the accepting ratio is the verification probability on a
uniform challenge. -/
theorem acceptRatio_acceptTable_pure (V : (ι → S) → Resp → Bool) (τ : (ι → S) → Resp) :
    acceptRatio (acceptTable V (pure τ) : ProbComp ((ι → S) → Bool))
      = Pr{let c ← $ᵗ (ι → S)}[V c (τ c)] := by
  classical
  rw [acceptTable, map_pure, acceptRatio, SampleableType.prEvent_uniformSample]
  refine congrArg (· / _) ?_
  rw [Finset.natCast_card_filter]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [prEvent_eq_evalDist_map]
  by_cases h : V c (τ c) <;> simp [h]

omit [DecidableEq S] [DecidableEq Resp] in
/-- Averaging the fixed-first-message accepting ratio over the prover's choice. -/
theorem verifyProb_eq_lintegral (σ : SigmaProtocol Stmt Wit Commit PrvState (ι → S) Resp rel)
    (x : Stmt) (P : ProbComp (Commit × ((ι → S) → Resp)))
    [MeasurableSpace (Commit × ((ι → S) → Resp))]
    [DiscreteMeasurableSpace (Commit × ((ι → S) → Resp))] :
    verifyProb σ x P
      = ∫⁻ p, acceptRatio (acceptTable (σ.verify x p.1) (pure p.2)) ∂𝒟[P] := by
  have key := prEvent_bind_eq_lintegral_of_discrete P
    (fun p : Commit × ((ι → S) → Resp) =>
      (($ᵗ (ι → S)) >>= fun c => pure (σ.verify x p.1 c (p.2 c) = true))) id
  simp only [id_eq, bind_pure] at key
  rw [verifyProb, key]
  exact lintegral_congr fun p => (acceptRatio_acceptTable_pure (σ.verify x p.1) p.2).symm

/-- The `μ = 1` extraction bound with the prover's first message sampled rather than fixed. The
loss is unchanged: averaging a pointwise bound over the first message costs nothing. -/
theorem sub_div_le_prEvent_extracted_coordExtractCommit [Nonempty S]
    (σ : SigmaProtocol Stmt Wit Commit PrvState (ι → S) Resp rel) (k : ℕ)
    (ext : Stmt → Commit → Finset ((ι → S) × Resp) → ProbComp Wit) (x : Stmt)
    (hss : σ.CoordSpeciallySoundAt k ext x) (P : ProbComp (Commit × ((ι → S) → Resp))) :
    verifyProb σ x P - (Fintype.card ι : ℝ≥0∞) * (k - 1 : ℕ) / Fintype.card S
      ≤ Pr{let r ← σ.coordExtractCommit k ext x P}[Extracted rel x r] := by
  classical
  -- The statement mentions no measure on the prover's own output, so the discrete structure the
  -- averaging step needs is introduced here rather than carried as a hypothesis.
  let _ : MeasurableSpace (Commit × ((ι → S) → Resp)) := ⊤
  let _ : MeasurableSingletonClass (Commit × ((ι → S) → Resp)) := ⟨fun _ => trivial⟩
  set L : ℝ≥0∞ := (Fintype.card ι : ℝ≥0∞) * (k - 1 : ℕ) / Fintype.card S with hL
  have key := prEvent_bind_eq_lintegral_of_discrete P
    (fun p : Commit × ((ι → S) → Resp) => σ.coordExtract k ext x p.1 (pure p.2))
    (Extracted rel x)
  rw [tsub_le_iff_right, verifyProb_eq_lintegral, coordExtractCommit, key]
  calc ∫⁻ p, acceptRatio (acceptTable (σ.verify x p.1) (pure p.2)) ∂𝒟[P]
      ≤ ∫⁻ p, (Pr{let r ← σ.coordExtract k ext x p.1 (pure p.2)}[Extracted rel x r] + L) ∂𝒟[P] :=
        lintegral_mono fun p => tsub_le_iff_right.mp
          (sub_div_le_prEvent_extracted_coordExtract σ k ext x hss p.1 (pure p.2))
    _ = (∫⁻ p, Pr{let r ← σ.coordExtract k ext x p.1 (pure p.2)}[Extracted rel x r] ∂𝒟[P])
          + L := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ _ := by rfl

end Commit

end SigmaProtocol
