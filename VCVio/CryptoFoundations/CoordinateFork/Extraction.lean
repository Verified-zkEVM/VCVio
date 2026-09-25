/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import ToMathlib.Probability.UniformOn
public import VCVio.CryptoFoundations.CoordinateFork.Operational
public import VCVio.CryptoFoundations.CoordinateFork.SpecialSoundness

/-!
# Extracting a witness from a coordinate-wise fork

`coordExtractOp` is the `μ = 1` Σ-protocol case of Lemma 2.31 of Fenzi–Moghaddas–Nguyen, over the
paper's own algorithm: run Figure 11's resampling loop (`OracleComp.coordForkOpT`) against the
prover's response table, then hand the accepting transcripts it returns to an extensional
`ℓ`-coordinate-wise `k`-special sound extractor. All three clauses of Lemma 7.1 hold of that one
computation:

* **output** — `OracleComp.coordForkOpT_success`: a successful run's fork produced `ℓ(k-1)+1`
  transcripts the verifier accepts, whose challenges form an `SS(S, ℓ, k)` set;
* **success** — `sub_div_le_prEvent_extracted_coordExtractOp`: a valid witness comes back with
  probability at least `ε - ℓ(k-1)/|S|`, where `ε` is the prover's accepting probability;
* **cost** — `lintegral_cost_coordExtractOp_le`: at most `1 + ℓ(k-1)` table lookups in
  expectation.

The success event is `∃ w, r = some w ∧ rel x w`, which no aborting run satisfies, so the middle
clause is about witnesses produced rather than about the extractor terminating.

`coordExtract` is the same composite over the total-lookup table core `coordForkT`. It reads the
whole response table at once, so it has no query count; it is kept because the averaging over the
prover's first message below is stated through it, and because the table core is what the counting
argument is proved about.

What this is not. The input `P : ProbComp ((ι → S) → Resp)` is a distribution of complete response
tables after the commitment `pc`; no theorem here derives such a distribution, or its cross-rewind
coupling, from an interactive malicious prover — see `CoordinateFork/Realizability.lean`, which
also says why the independent construction there is *not* a rewound prover. The count is of table
lookups, returned as data by the loop, not oracle queries measured by the cost model in
`docs/agents/query-tracking.md`. And there is no security-parameter quantification, joint bad-event
experiment, or expected-polynomial-time claim, so this is not Definition 2.28. Only `μ = 1` is
represented.
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


/-! ## Extracting through Figure 11

`coordExtract` runs the total-lookup table core: it reads the whole response table, so it has no
query count to report. `coordExtractOp` runs the paper's algorithm instead — `coordForkOpT`, the
resampling loop of Figure 11 carrying the prover's responses — and the three clauses of Lemma 7.1
then hold of *one* named computation: it returns a valid witness with probability at least
`ε - ℓ(k-1)/|S|` (`sub_div_le_prEvent_extracted_coordExtractOp`) after at most `1 + ℓ(k-1)` table
lookups in expectation (`lintegral_cost_coordExtractOp_le`), and what the fork handed the
extractor was `ℓ(k-1)+1` accepting transcripts whose challenges are `SS(S, ℓ, k)`
(`OracleComp.coordForkOpT_success`).

The count is of *table lookups*, returned as data by the loop; it is not an oracle-query count
measured by `VCVio/OracleComp/QueryTracking/`. Bridging the two is future work. -/

section Operational

/-- The composite extractor over the paper's algorithm: run Figure 11 against the prover's
response table, then hand the accepting transcripts it returns to the `k`-ary extractor. The
lookup count the loop reports is carried through unchanged. -/
@[expose] noncomputable def coordExtractOp
    (σ : SigmaProtocol Stmt Wit Commit PrvState (ι → S) Resp rel)
    (k : ℕ) (ext : Stmt → Commit → Finset ((ι → S) × Resp) → ProbComp Wit) (x : Stmt)
    (pc : Commit) (P : ProbComp ((ι → S) → Resp)) : ProbComp (Option Wit × ℕ) :=
  coordForkOpT (σ.verify x pc) k P >>= fun r =>
    match r.1 with
    | none => pure (none, r.2)
    | some (τ, X) => (fun w => (some w, r.2)) <$> ext x pc (transcripts τ X)

/-- **The success clause, for the paper's algorithm.** -/
theorem sub_div_le_prEvent_extracted_coordExtractOp [Nonempty S]
    (σ : SigmaProtocol Stmt Wit Commit PrvState (ι → S) Resp rel) (k : ℕ)
    (ext : Stmt → Commit → Finset ((ι → S) × Resp) → ProbComp Wit) (x : Stmt)
    (hss : σ.CoordSpeciallySoundAt k ext x) (pc : Commit)
    (P : ProbComp ((ι → S) → Resp)) :
    acceptRatio (acceptTable (σ.verify x pc) P)
        - (Fintype.card ι : ℝ≥0∞) * (k - 1 : ℕ) / Fintype.card S
      ≤ Pr{let r ← σ.coordExtractOp k ext x pc P}[Extracted rel x r.1] := by
  refine (sub_div_le_prEvent_goodTranscripts_coordForkOpT (σ.verify x pc) k P).trans ?_
  rw [coordExtractOp]
  refine le_of_eq_of_le (mul_one _).symm
    (mul_le_prEvent_bind_of_forall _ _ _ _ le_rfl fun r hgood => ?_)
  obtain ⟨τ, X, hEq, hss', hpay⟩ := hgood
  rw [hEq]
  refine le_of_eq ?_
  rw [prEvent_map]
  refine (prEvent_eq_one_of_forall_mem_support _ _ fun w hw => ⟨w, rfl, ?_⟩).symm
  exact hss pc (transcripts τ X)
    (isCoordSpecialSoundTranscripts_of_goodTranscripts ⟨τ, X, hEq ▸ rfl, hss', hpay⟩) w hw

/-- **The expected-lookup clause, for the paper's algorithm.** The composite reports exactly the
lookups its fork made, so the bound is the fork's. -/
theorem lintegral_cost_coordExtractOp_le [Nonempty S]
    (σ : SigmaProtocol Stmt Wit Commit PrvState (ι → S) Resp rel) (k : ℕ)
    (ext : Stmt → Commit → Finset ((ι → S) × Resp) → ProbComp Wit) (x : Stmt)
    (pc : Commit) (P : ProbComp ((ι → S) → Resp)) :
    ∫⁻ n, (n : ℝ≥0∞) ∂𝒟[Prod.snd <$> σ.coordExtractOp k ext x pc P]
      ≤ 1 + Fintype.card ι * (k - 1 : ℕ) := by
  -- The composite returns the fork's tally verbatim, so the two agree in law even though the
  -- extractor's own run sits between them.
  classical
  let _ : MeasurableSpace (Option (((ι → S) → Resp) × Finset (ι → S)) × ℕ) := ⊤
  let _ : DiscreteMeasurableSpace (Option (((ι → S) → Resp) × Finset (ι → S)) × ℕ) :=
    ⟨fun _ => trivial⟩
  let _ : MeasurableSpace Wit := ⊤
  let _ : MeasurableSpace (Option Wit × ℕ) := ⊤
  have hbranch : ∀ r : Option (((ι → S) → Resp) × Finset (ι → S)) × ℕ,
      𝒟[Prod.snd <$> (match r.1 with
          | none => (pure (none, r.2) : ProbComp (Option Wit × ℕ))
          | some (τ, X) => (fun w => (some w, r.2)) <$> ext x pc (transcripts τ X))]
        = 𝒟[(pure r.2 : ProbComp ℕ)] := by
    intro r
    match hr : r.1 with
    | none => simp
    | some p =>
        rw [show (Prod.snd <$> ((fun w => (some w, r.2)) <$> ext x pc (transcripts p.1 p.2)))
            = ((fun _ => r.2) <$> ext x pc (transcripts p.1 p.2) : ProbComp ℕ) from
              Functor.map_map .. ,
          _root_.evalDist_map_const, evalDist_apply_univ_eq_one, one_smul, evalDist_pure]
  have hlaw : 𝒟[Prod.snd <$> σ.coordExtractOp k ext x pc P]
      = 𝒟[Prod.snd <$> coordForkOpT (σ.verify x pc) k P] := by
    rw [coordExtractOp, map_bind, map_eq_bind_pure_comp (f := Prod.snd)
        (x := coordForkOpT (σ.verify x pc) k P),
      evalDist_bind_of_discrete, evalDist_bind_of_discrete]
    exact congrArg (Measure.bind _) (funext fun r => (hbranch r).trans rfl)
  rw [hlaw]
  exact lintegral_cost_coordForkOpT_le (σ.verify x pc) k P

end Operational

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
