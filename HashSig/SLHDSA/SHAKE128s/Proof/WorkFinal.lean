/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ShareJointShared
public import HashSig.SLHDSA.SHAKE128s.Proof.ShareFiled
public import HashSig.SLHDSA.SHAKE128s.Proof.WorkTarget

/-!
# `127` bits on the adversary's own work

Counting mode `Security.adversaryWork`: the adversary's signing requests, its own hash calls and
the verification of its forgery. Key generation's and the signer's hash calls are free.

* **The per-setup link** (`setupBound`): the jointly capped real game, coupled with the jointly
  capped lenient game (`ShareJointCouple.couple_whole`), raises the lenient flag whenever its
  real event comes with an accepted forgery — at the claims, which an accepted forgery's game
  always takes — and the lenient flag has the blind flag's law (`ShareUntilBad`).
* **The shared half** (`hsharedFused`): `ShareJointShared.hshared` at the refined paired run,
  `(q - 8) / 2 ^ 128` on accepted forgeries.
* **The target** (`hasSecurityBits_work`): `WorkTarget.warmed_bound` for
  `569 ≤ q`; below that nothing wins, since an accepted forgery's verification alone costs `569`
  counted calls.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational

namespace SlhDsaSecurity.WorkFinal

open Security CanonicalGraph ShareGame ShareInv ShareWhole ShareEvent WarmedGame Target
  RoutedSplit BySourceBridge

/-! ## The per-setup link -/

/-- **At a good setup, the jointly capped real event with an accepted forgery is at most the
blind flag.** -/
theorem setupBound (adversary : Adversary) (limit : Nat) :
    ShareJointShared.SetupBound adversary limit := by
  intro setup hgood
  refine le_trans (prEvent_le_of_relTriple (q := fun lenient => lenient.2.2 = true)
    (relTriple_support_left (ShareJointCouple.couple_whole setup hgood adversary limit)) ?_) ?_
  · rintro real lenient ⟨hfinal, -⟩ ⟨hevent, hverified⟩
    obtain ⟨hforgery, -, stateV, hinv, hcache, hlog, hadv, hver, hacc⟩ := hfinal
    obtain ⟨hclaims, zs, w, hw, hreal⟩ := hacc hverified
    rw [hclaims, hforgery]
    cases hflag : stateV.2 with
    | true => simp [claimsStep, hflag]
    | false =>
      rcases hevent with hbad | hlate | hlate
      · exact flag_of_inputBad setup real zs w hw hreal stateV hinv hflag hcache hlog hver hbad
      · have := flag_of_prfHit setup real stateV hinv hadv hver hlate
        rw [hflag] at this
        cases this
      · have := flag_of_signerHit setup hgood real stateV hinv hcache hlog hlate
        rw [hflag] at this
        cases this
  · exact le_of_eq (ShareUntilBad.probEvent_bad_eq setup _ St.start)

/-- **The blind verifier files what it consults**, at every setup. -/
theorem verifierFiles (setup : Setup) : ShareJointBound.VerifierFiles setup :=
  fun request wire p w hw => ShareFiled.verify_probes_filed_any setup setup.pk request wire p w hw

/-! ## The shared half, at the refined paired run -/

/-- The shared half on accepted forgeries, at the refined paired run. -/
theorem hsharedFused (q : Nat) (adversary : Adversary) (hbudget : TailBudgetW adversary q)
    (hq : 569 ≤ q) :
    Pr{let pair ← pairedFused (CarrierTail.carrierTail CarrierThin.keep127 adversary)}[
        GoodWalk pair.1 ∧
        (InputBad ((pair.1.1, (FinalAssembly.forgetFused pair.2).1),
          (FinalAssembly.forgetFused pair.2).2) ∨ Target127.late pair) ∧
        (FinalAssembly.forgetFused pair.2).1.1.verified = true] ≤
      ((q - 8 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  have hpaired : pairedFused (CarrierTail.carrierTail CarrierThin.keep127 adversary) =
      LateProbes.pairedOf (CarrierTail.carrierTail CarrierThin.keep127) adversary := rfl
  rw [hpaired]
  refine le_trans (le_of_eq ?_) (ShareJointShared.hshared q adversary hbudget hq
    (setupBound adversary (q - 569)) verifierFiles)
  exact LateProbes.probEvent_forget (CarrierTail.forgetsTo CarrierThin.keep127 adversary)
    (fun pair : SharedJoin.RecordedPair => GoodWalk pair.1 ∧
      (InputBad (SharedJoin.recordedTraceOf pair) ∨ Target127.Late pair) ∧
      pair.2.1.1.1.verified = true)

/-! ## Nothing wins below `569` -/

attribute [local irreducible] Scheme.keygenInternal Scheme.keygen Scheme.verify Scheme.sign
  afterKeygen Security.countQueries WarmedGame.afterSeeds

/-- Forgetting the hash counts of `runAll` gives `run`. -/
theorem map_fst_runAll (adversary : Adversary) :
    Prod.fst <$> runAll adversary = run adversary := by
  rw [runAll, run, ← BySourceBridge.run_map, RecordedBudget.map_countAllHashes]

/-- **Below `569` counted calls, nothing wins**: an accepted forgery's verification alone
costs that many. -/
theorem advantage_eq_zero (adversary : Adversary) (q : Nat) (hq : q < 569)
    (hbound : securityGame.HasQueryBound () adversaryWork adversary q) :
    securityGame.advantage () adversary = 0 := by
  unfold Xmss.SecurityGame.advantage
  refine prEvent_eq_zero_of_forall_mem_support _ _ fun result hresult hwin => ?_
  change result ∈ support ((fun result => (decide (Wins result.1), result.2)) <$>
    runBySource adversary) at hresult
  rw [support_map] at hresult
  obtain ⟨bySource, hbySource, rfl⟩ := hresult
  have hwins : Wins bySource.1 := by simpa using hwin
  have hsum := (OracleComp.prEvent_eq_one_iff _ _).mp hbound _ (by
    change _ ∈ support ((fun result => (decide (Wins result.1), result.2)) <$>
      runBySource adversary)
    rw [support_map]
    exact ⟨bySource, hbySource, rfl⟩)
  obtain ⟨keygenHashes, laterHashes, hcounts, -⟩ :=
    exists_sourceCounts adversary bySource hbySource
  simp only at hsum
  rw [sum_adversaryWork, hcounts] at hsum
  simp only [sourceCounts] at hsum
  have hrun : bySource.1 ∈ support (run adversary) := by
    rw [← map_fst_runAll, ← map_fst_runBySource, support_map]
    exact ⟨bySource, hbySource, rfl⟩
  have hwork := VerificationBudget.accepted_outcome_work adversary bySource.1 hrun hwins.1
  unfold Counts.work at hwork
  omega

/-! ## The target -/

/-- **`SLH-DSA-SHAKE-128s` has `127` bits of strong security on the adversary's own work**:
signing requests, its own hash calls and the verification of its forgery are counted; key
generation's and the signer's hash calls are free. -/
theorem hasSecurityBits_work : HasSecurityBits adversaryWork 127 := by
  intro q _ adversary hlimit hbound
  by_cases hq : 569 ≤ q
  · have hbudget := tailBudgetW_of hlimit hbound
    rw [advantage_securityGame, totalAdvantage,
      MainTheorem.probEvent_runAll adversary (fun result => Wins result.1),
      WarmedGame.probEvent_warmed adversary (fun outcome => Wins outcome.1)]
    exact WorkTarget.warmed_bound q adversary hbudget (by omega)
      (hsharedFused q adversary hbudget hq)
  · rw [advantage_eq_zero adversary q (by omega) hbound]
    exact zero_le

end SlhDsaSecurity.WorkFinal
