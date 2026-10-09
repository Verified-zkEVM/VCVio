/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.CoverageRun
public import HashSig.SLHDSA.Security.JointBound
import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
# The coverage bound and the security target of SLH-DSA

For SLH-DSA in the three-oracle random-oracle model (`romScheme`) at a fixed public seed, this
module bounds the probability of interleaved-target coverage in the ideal hidden-seed game, and
with the joint bound of `HashSig.SLHDSA.Security.JointBound` proves the security target
`SecurityTarget core e optRand 2 1`.

## The coverage bound

`prEvent_idealDraw_runItsrCovered_le`: in `idealDraw`, a forger with hash budget `qh` and signing
budget `qs` makes the forged message fresh and every FORS digit of its digest covered by the digest
of a logged signature (`RunItsrCovered`) with probability at most
`(qh + 1) · weightedTargetCoverBound h a k qs qh (qs / |Y|)`. The chain is:

* *Untagging.* The secret-free experiment in the ideal game is the role-tagged experiment
  `roleExperiment` under the collapse handler (`simulateQ_collapseFwd_roleExperiment`), and the
  ideal game on that is the duplicated random oracle on the joint interface
  (`SecretEncoding.map_run_simulateQ_idealImpl_collapseFwd`). Coverage reads only `H_msg`
  answers, so it is an event of that run whatever the drawn seeds.
* *Transport to tapes.* The duplicated random oracle is the class-indexed tape oracle over a tape
  family drawn at the lengths `tapeLength qh qs`, and an event of the run that yields a witness
  `w` with a tape event `M w` and a run event `H w` is bounded by
  `∑ w, Pr[M w] · β w` when `β w` bounds `H w` on every family
  (`AnswerTape.prEvent_run_dupRandomOracleFwd_le_sum`).
* *Witnesses.* A witness is the forger-tape position `n` of the target and a coverer slot for each
  FORS tree, on the signer tape or at another forger-tape position
  (`exists_witness_of_runItsrCovered`). Its tape event `TapeMatch` has mass at most
  `(2 ^ h)⁻¹ ^ r · ((2 ^ a)⁻¹) ^ k` for `r` distinct coverer slots (`prEvent_tapeMatch_le`), and
  its run event, every designated forger-tape position hit by a fresh randomizer draw, has
  probability at most `(qs / |Y|) ^ r₁` for `r₁` distinct forger-tape slots
  (`prEvent_roleRun_hitAll_le`).
* *The count.* Summed over the coverer assignments, these products are
  `weightedTargetCoverBound h a k qs qh (qs / |Y|)`
  (`KeyedHash.Covering.sum_pow_card_image_eq_weightedTargetCoverBound`), and the target position
  contributes the factor `qh + 1`.

## The security target

`unforgeableAdvantage_romScheme_pure_le_securityBound` adds the coverage bound to the joint bound
`2 (qh + V) / |Y|` of `unforgeableAdvantage_romScheme_pure_le_add_idealDraw`, which is
`securityBound` at `c = 2` and `r = 1`. `securityTarget_two_one` restates it as
`SecurityTarget core e optRand 2 1`, and `unforgeableAdvantage_romScheme_le_securityBound` averages
it over any distribution of the public seed, the uniform one of FIPS 205 included.

## Scope

* The model is the classical random-oracle model with three oracles: the tweakable hash, `H_msg`
  and `PRF_msg`. Nothing here is quantum.
* `optRand` is arbitrary, so the statements cover hedged and deterministic signing.
* The `H_msg` answers of the model are drawn by any uniform sampler of `Bytes m`, the one
  `SecurityTarget` binds. The answer tapes of the proof draw from the global sampler; the tape
  identification `AnswerTape.evalDist_run_dupRandomOracleFwd_eq_tapeFamily` relates the two,
  since only the uniform law of either enters.
* The faithfulness step relating the three-oracle model to the byte-level scheme over a single
  SHAKE256 is not included: neither its losses nor, for deterministic signing, its term
  `qs / 2 ^ (8 n)`.
-/

public section

open OracleComp OracleSpec SignatureAlg MeasureTheory
open scoped ENNReal

namespace SLHDSA.Security

open Coverage SLHDSA.DigestTransport KeyedHash.Covering

variable {vp : ValidatedParams} {core : CorePrimitives vp.params}

/-! ## The tape event of a witness -/

section TapeMatch

/-- The index of a coverer slot on the concatenation of the forger tape, of length `qh + 1`, and
the signer tape, of length `qs`, for the target at forger-tape position `n`: a signer slot `inl s`
is at `qh + 1 + s`, and a forger slot `inr p` at the `p`-th forger-tape position other than `n`. -/
def coverIdx {qh qs : ℕ} (n : Fin (qh + 1)) : Fin qs ⊕ Fin qh → Fin ((qh + 1) + qs)
  | .inl s => Fin.natAdd (qh + 1) s
  | .inr p => Fin.castAdd qs (n.succAbove p)

/-- Distinct coverer slots have distinct indices. -/
theorem coverIdx_injective {qh qs : ℕ} (n : Fin (qh + 1)) :
    Function.Injective (coverIdx (qs := qs) n) := by
  rintro (s | p) (s' | p') h <;>
    simp only [coverIdx, Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd] at h
  · exact congrArg Sum.inl (Fin.ext (by omega))
  · have := (n.succAbove p').isLt; omega
  · have := (n.succAbove p).isLt; omega
  · exact congrArg Sum.inr (Fin.succAbove_right_injective (Fin.ext h))

/-- No coverer slot sits at the target position. -/
theorem coverIdx_ne_castAdd {qh qs : ℕ} (n : Fin (qh + 1)) (c : Fin qs ⊕ Fin qh) :
    coverIdx n c ≠ Fin.castAdd qs n := by
  rcases c with s | p <;>
    simp only [coverIdx, ne_eq, Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd]
  · have := n.isLt; omega
  · exact fun h => Fin.succAbove_ne n p (Fin.ext h)

variable [SampleableType core.Y]

/-- **The tape mass of a witness.** Over a tape family drawn at the lengths `tapeLength qh qs`,
the tape event of the witness `w` has probability at most `(2 ^ h)⁻¹ ^ r · ((2 ^ a)⁻¹) ^ k`, with
`r` the number of distinct coverer slots of `w`. -/
theorem prEvent_tapeMatch_le {qh qs : ℕ}
    (w : Fin (qh + 1) × (Fin vp.params.k → Fin qs ⊕ Fin qh)) :
    Pr{let L ← AnswerTape.tapeFamily (tapeClassRange core) (tapeLength qh qs)}[
        TapeMatch core w L] ≤
      (((2 : ℝ≥0∞) ^ vp.params.h)⁻¹) ^ (Finset.univ.image w.2).card *
        (((2 : ℝ≥0∞) ^ vp.params.a)⁻¹) ^ vp.params.k := by
  classical
  let _ : ∀ j, MeasurableSpace (tapeClassRange core j) := fun _ => ⊤
  have _ : ∀ j, DiscreteMeasurableSpace (tapeClassRange core j) := fun _ => ⟨fun _ => trivial⟩
  let _ : MeasurableSpace (Bytes vp.params.m) := ⊤
  have _ : DiscreteMeasurableSpace (Bytes vp.params.m) := ⟨fun _ => trivial⟩
  let _ : MeasurableSpace ((k : TapeClass) → List (tapeClassRange core k)) := ⊤
  have _ : DiscreteMeasurableSpace ((k : TapeClass) → List (tapeClassRange core k)) :=
    ⟨fun _ => trivial⟩
  obtain ⟨n, f⟩ := w
  set j₀ : Fin ((qh + 1) + qs) := Fin.castAdd qs n
  set g : Fin vp.params.k → Fin ((qh + 1) + qs) := fun i => coverIdx n (f i)
  rw [prEvent_eq_evalDist_of_discrete]
  have h2 := AnswerTape.evalDist_tapeFamily_setOf_eq₂ (R := tapeClassRange core)
    (j := TapeClass.forger) (j' := TapeClass.signer) (by decide) rfl (tapeLength qh qs)
    (fun lF lS => TapeMatchOn (n, f) lF lS)
  simp only [cast_eq] at h2
  refine (le_of_eq h2).trans ?_
  change 𝒟[AnswerTape.answerTape (Bytes vp.params.m) ((qh + 1) + qs)]
      {v | TapeMatchOn (n, f) (List.ofFn fun i => v (Fin.castAdd qs i))
        (List.ofFn fun i => v (Fin.natAdd (qh + 1) i))} ≤ _
  have hsub : {v : Fin ((qh + 1) + qs) → Bytes vp.params.m |
        TapeMatchOn (n, f) (List.ofFn fun i => v (Fin.castAdd qs i))
          (List.ofFn fun i => v (Fin.natAdd (qh + 1) i))} ⊆
      (fun (v : Fin ((qh + 1) + qs) → Bytes vp.params.m) i => coveringDigest vp (v i)) ⁻¹'
        {u | ∀ i, (u (g i)).1 = (u j₀).1 ∧ (u (g i)).2 i = (u j₀).2 i} := by
    intro v hv i
    obtain ⟨dn, dc, hn, hc, h1, h2⟩ := hv i
    have hdn : dn = v j₀ := by
      simp only [List.getElem?_ofFn, Fin.is_lt, ↓reduceDIte, Option.some.injEq] at hn
      exact hn.symm
    have hdc : dc = v (g i) := by
      simp only [g]
      dsimp only at hc
      rcases hfi : f i with s | p <;>
        simp only [hfi, coverValue, List.getElem?_ofFn, Fin.is_lt, ↓reduceDIte,
          Option.some.injEq] at hc <;>
        exact hc.symm
    subst hdn hdc
    exact ⟨h1, h2⟩
  refine (measure_mono hsub).trans ?_
  rw [evalDist_answerTape_preimage_coveringDigest vp ((qh + 1) + qs)]
  refine (evalDist_answerTape_coverWitness_le _ _ _ j₀ g fun i => coverIdx_ne_castAdd n (f i)).trans
    (le_of_eq ?_)
  have hg : Finset.univ.image g = (Finset.univ.image f).image (coverIdx n) := by
    rw [Finset.image_image]
    rfl
  rw [hg, Finset.card_image_of_injective _ (coverIdx_injective n)]

end TapeMatch

/-! ## The run event of a witness -/

section HitAll

/-- The designated positions of a witness are as many as its distinct forger-tape coverer
slots. -/
theorem card_desigPos {qh qs : ℕ} (w : Fin (qh + 1) × (Fin vp.params.k → Fin qs ⊕ Fin qh)) :
    (desigPos w).card = (Finset.univ.filter fun p : Fin qh => ∃ i, w.2 i = .inr p).card :=
  Finset.card_image_of_injective _ (Fin.val_injective.comp Fin.succAbove_right_injective)

variable [SampleableType core.Y] [SampleableType (Bytes vp.params.m)] [DecidableEq core.Y]
  [SampleableType core.SkSeed] [SampleableType core.SkPrf] [DecidableEq core.PkSeed]
  [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf]

/-- **The hit probability of a witness.** On the instrumented role run of a forger with signing
budget `qs`, over a tape family whose tape of class `other` is empty, every designated position of
the witness `w` is hit by a fresh randomizer draw, with no draw hitting two of them, with
probability at most `(qs / |Y|) ^ r₁`, with `r₁` the number of distinct forger-tape coverer slots
of `w`. -/
theorem prEvent_roleRun_hitAll_le {e : core.SkSeed ≃ core.Y}
    {optRand : PublicKeyCore core → ProbComp core.Y} {pkSeedDist : ProbComp core.PkSeed}
    {adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist)} {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) (pkSeed : core.PkSeed)
    (L : (j : TapeClass) → List (tapeClassRange core j)) (hL : L .other = [])
    (w : Fin (qh + 1) × (Fin vp.params.k → Fin qs ⊕ Fin qh)) :
    Pr{let z ← roleRun core adv pkSeed L}[
        AnswerTape.HitAll (randRel core) TapeClass.forger (desigPos w) z.2] ≤
      ((qs : ℝ≥0∞) / Nat.card core.Y) ^
        (Finset.univ.filter fun p : Fin qh => ∃ i, w.2 i = .inr p).card :=
  (prEvent_roleExperiment_hitAll_le core hadv pkSeed L hL (desigPos w)).trans_eq
    (by rw [card_desigPos])

end HitAll

/-! ## The coverage bound -/

variable [SampleableType core.Y] [SampleableType (Bytes vp.params.m)] [DecidableEq core.Y]
  [SampleableType core.SkSeed] [SampleableType core.SkPrf] [DecidableEq core.PkSeed]
  [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf]

/-- **The coverage bound in the ideal hidden-seed game, per public seed.** For a forger with hash
budget `qh` and signing budget `qs`, `idealDraw` at public seed `pkSeed` fires interleaved-target
coverage with a fresh forged message (`RunItsrCovered`), on the transcript rebuilt with the drawn
seeds and the cache merged under them, with probability at most
`(qh + 1) · weightedTargetCoverBound h a k qs qh (qs / |Y|)`. -/
theorem prEvent_idealDraw_runItsrCovered_le (e : core.SkSeed ≃ core.Y)
    (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeed : core.PkSeed)
    {adv : UnforgeableAdversary (romScheme core e optRand (pure pkSeed))} {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    Pr{let w ← idealDraw e optRand pkSeed adv}[
        RunItsrCovered core (DeriveOutcome.fill core w.1 w.2.1,
          (secretEncoding core e pkSeed).merge w.1 w.2.2)] ≤
      ((qh : ℝ≥0∞) + 1) * weightedTargetCoverBound vp.params.h vp.params.a vp.params.k qs qh
        ((qs : ℝ≥0∞) / Nat.card core.Y) := by
  classical
  have hm : ∀ (s : core.SkSeed × core.SkPrf)
      (C : SecretEncoding.SplitCache (hashSpec core) (DeriveQuery core) core.Y)
      (r : core.Y) (ps : core.PkSeed) (pr : core.Y) (m : List Byte),
      ((secretEncoding core e pkSeed).merge s C).fst (.hmsg r ps pr m) =
        C.1.fst (.hmsg r ps pr m) := fun s C _ _ _ _ => by
    simp only [QueryCache.fst_apply]
    refine (secretEncoding core e pkSeed).merge_apply_of_not_exists s C ?_
    rintro ⟨x | ⟨o, msg⟩, hx⟩ <;> cases hx
  simp only [idealDraw]
  refine prEvent_bind_le_of_forall_le _ _ _ fun s => ?_
  rw [show ((simulateQ (SecretEncoding.idealImpl (hashSpec core) (DeriveQuery core) core.Y)
      (unforgeableTranscriptExperiment (deriveAdversary core adv pkSeed))).run (∅, ∅) >>=
        fun z => (pure (s, z) : ProbComp _)) =
      Prod.mk s <$> (simulateQ (SecretEncoding.idealImpl (hashSpec core) (DeriveQuery core)
        core.Y) (unforgeableTranscriptExperiment (deriveAdversary core adv pkSeed))).run (∅, ∅)
    from bind_pure_comp _ _, prEvent_map]
  have hev : ∀ z : DeriveOutcome core ×
      SecretEncoding.SplitCache (hashSpec core) (DeriveQuery core) core.Y,
      RunItsrCovered core (DeriveOutcome.fill core (s, z).1 (s, z).2.1,
          (secretEncoding core e pkSeed).merge (s, z).1 (s, z).2.2) ↔
        RunItsrCovered core (DeriveOutcome.fill core s z.1, z.2.1) := fun z => by
    simp only [RunItsrCovered, ItsrCovered, ForgerDigest, LoggedDigest, RunFresh, hm]
  rw [prEvent_congr _ _ _ hev, ← simulateQ_collapseFwd_roleExperiment core adv pkSeed]
  have hbr := SecretEncoding.map_run_simulateQ_idealImpl_collapseFwd
    (roleExperiment core adv pkSeed)
    ((∅, ∅) : SecretEncoding.SplitCache (hashSpec core) (DeriveQuery core) core.Y)
  rw [QueryCache.addEquiv_empty] at hbr
  have hpr : Pr{let z ← (simulateQ (SecretEncoding.idealImpl (hashSpec core) (DeriveQuery core)
        core.Y) (simulateQ (SecretEncoding.collapseFwd (hashSpec core) (DeriveQuery core) core.Y)
          (roleExperiment core adv pkSeed))).run (∅, ∅)}[
        RunItsrCovered core (DeriveOutcome.fill core s z.1, z.2.1)] =
      Pr{let z ← (simulateQ (AnswerTape.dupRandomOracleFwd (jointSpec core))
          (roleExperiment core adv pkSeed)).run ∅}[
        RunItsrCovered core (DeriveOutcome.fill core s z.1, z.2.fst)] := by
    rw [← hbr, prEvent_map]
    rfl
  rw [hpr]
  refine (AnswerTape.prEvent_run_dupRandomOracleFwd_le_sum (tapeClass core)
    (range_eq_tapeClassRange core)
    (AnswerTape.freshHitAux (IsRandPoint core) (randRel core)) ∅
    (roleExperiment core adv pkSeed)
    (tapeLength qh qs) (fun z => RunItsrCovered core (DeriveOutcome.fill core s z.1, z.2.fst))
    Finset.univ (TapeMatch core)
    (fun w z => AnswerTape.HitAll (randRel core) TapeClass.forger (desigPos w) z.2)
    (fun w => ((qs : ℝ≥0∞) / Nat.card core.Y) ^
      (Finset.univ.filter fun p : Fin qh => ∃ i, w.2 i = .inr p).card)
    (fun L hL z hz hcov => by
      obtain ⟨w, hw⟩ := exists_witness_of_runItsrCovered core hadv pkSeed s L hL z hz hcov
      exact ⟨w, Finset.mem_univ w, hw⟩)
    (fun L hL w _ => prEvent_roleRun_hitAll_le hadv pkSeed L
      (List.eq_nil_of_length_eq_zero
        (AnswerTape.length_of_mem_support_tapeFamily (tapeLength qh qs) hL .other)) w)).trans ?_
  refine (Finset.sum_le_sum fun w _ => mul_le_mul_left (prEvent_tapeMatch_le w) _).trans
    (le_of_eq ?_)
  rw [Fintype.sum_prod_type]
  simp only [sum_pow_card_image_eq_weightedTargetCoverBound, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-! ## The security target -/

/-- **SLH-DSA meets the security target at `c = 2` and `r = 1`, per public seed.** In the
classical random-oracle model with three oracles (the tweakable hash, `H_msg` and `PRF_msg`),
under the byte laws, the key discipline and `|Y| ≤ |SK.prf|`, the forging advantage against
`romScheme` at public seed `pkSeed` of a forger making at most `qh` hash queries and `qs` signing
queries is at most `securityBound vp.params |Y| 2 1 qh qs`:
`(qh + 1) · weightedTargetCoverBound h a k qs qh (qs / |Y|) + 2 (qh + V) / |Y|`, with `V` the
verifier's query bound. `optRand` is arbitrary, so this holds for hedged and deterministic
signing, and the `H_msg` answers may be drawn by any uniform sampler of `Bytes m`. -/
theorem unforgeableAdvantage_romScheme_pure_le_securityBound (laws : core.ByteLaws)
    (hd : core.KeyDiscipline vp) (hcard : Nat.card core.Y ≤ Nat.card core.SkPrf)
    (e : core.SkSeed ≃ core.Y) (optRand : PublicKeyCore core → ProbComp core.Y)
    (pkSeed : core.PkSeed) {adv : UnforgeableAdversary (romScheme core e optRand (pure pkSeed))}
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    unforgeableAdvantage (ProbCompRuntime.rom (hashSpec core)) adv ≤
      securityBound vp.params (Nat.card core.Y) 2 1 qh qs := by
  refine (unforgeableAdvantage_romScheme_pure_le_add_idealDraw laws hd hcard e optRand pkSeed
    hadv).trans ?_
  rw [securityBound, add_comm]
  gcongr
  · exact prEvent_idealDraw_runItsrCovered_le e optRand pkSeed hadv
  · rw [ENNReal.div_eq_inv_mul, mul_comm]
    push_cast
    rw [mul_add]

/-- **The security target of SLH-DSA at `c = 2` and `r = 1`.** In the classical random-oracle
model with three oracles (the tweakable hash, `H_msg` and `PRF_msg`), under the byte laws, the key
discipline and `|Y| ≤ |SK.prf|`, for every public seed, every forger against `romScheme` at that
seed making at most `qh` hash queries and `qs` signing queries has forging advantage at most
`securityBound vp.params |Y| 2 1 qh qs`, in both signing modes and at every uniform sampler of
`Bytes m`. -/
theorem securityTarget_two_one (laws : core.ByteLaws) (hd : core.KeyDiscipline vp)
    (hcard : Nat.card core.Y ≤ Nat.card core.SkPrf) (e : core.SkSeed ≃ core.Y)
    (optRand : PublicKeyCore core → ProbComp core.Y) :
    SecurityTarget core e optRand 2 1 := fun pkSeed _ _ _ hadv =>
  unforgeableAdvantage_romScheme_pure_le_securityBound laws hd hcard e optRand pkSeed hadv

/-- **The security bound for every distribution of the public seed.** In the classical
random-oracle model with three oracles, under the byte laws, the key discipline and
`|Y| ≤ |SK.prf|`, every forger against `romScheme` with the public seed drawn from `pkSeedDist`,
the uniform draw of FIPS 205 included, making at most `qh` hash queries and `qs` signing queries
has forging advantage at most `securityBound vp.params |Y| 2 1 qh qs`, in both signing modes. -/
theorem unforgeableAdvantage_romScheme_le_securityBound (laws : core.ByteLaws)
    (hd : core.KeyDiscipline vp) (hcard : Nat.card core.Y ≤ Nat.card core.SkPrf)
    (e : core.SkSeed ≃ core.Y) (optRand : PublicKeyCore core → ProbComp core.Y)
    (pkSeedDist : ProbComp core.PkSeed)
    (adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist)) {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    unforgeableAdvantage (ProbCompRuntime.rom (hashSpec core)) adv ≤
      securityBound vp.params (Nat.card core.Y) 2 1 qh qs :=
  unforgeableAdvantage_romScheme_le core (securityTarget_two_one laws hd hcard e optRand)
    pkSeedDist adv hadv

end SLHDSA.Security
