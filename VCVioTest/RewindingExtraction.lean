/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.CryptoFoundations.Rewinding.Extraction
public import VCVio.CryptoFoundations.Rewinding.ThresholdFinder
public import VCVio.CryptoFoundations.Rewinding.FixedTape
public import VCVio.CryptoFoundations.SigmaProtocol

/-!
# Extracting a witness from a frozen Σ-protocol prover

A malicious prover for a specially sound Σ-protocol commits, then responds to one challenge. Run
against frozen reruns of this prover (`Rewinding.fixedTape`), the threshold finder with two branches
looks for two distinct accepting challenges. The transcripts of those two runs share the commitment
(`Rewinding.ResetPolicy.eagerTable_fst_eq`), and the protocol's extractor turns them into a witness.
A valid witness comes back with probability at least the prover's acceptance probability minus the
threshold error. Recovery (`Rewinding.recover`) finds both transcripts in a cache of the finder's
runs, since the finder queried both, so it costs at most two complete runs in expectation: the
finder's own.
-/

public section

open OracleComp OracleSpec Rewinding
open scoped ENNReal

namespace VCVioTest.RewindingExtraction

variable {Stmt Wit Commit St Chal Resp : Type} {rel : Stmt → Wit → Bool}

/-- The single round of challenges. -/
abbrev chals (Chal : Type) (_ : Fin 1) : Type := Chal

/-- Two branches: two distinct accepting challenges. -/
abbrev two (_ : Fin 1) : ℕ := 2

/-- A malicious prover's complete run on a challenge vector: its commitment phase, then its
response to the challenge. -/
@[expose] def proverRun (commit : ProbComp (Commit × St)) (respond : St → Chal → ProbComp Resp)
    (c : (i : Fin 1) → chals Chal i) : ProbComp (Commit × Resp) :=
  commit >>= fun s => (s.1, ·) <$> respond s.2 (c 0)

/-- The two leaves of a one-round tree with two branches. -/
@[expose] def leafPoints (t : VecTree (chals Chal) two) : Fin 2 → (i : Fin 1) → chals Chal i :=
  fun j => t.leaf fun _ => j

/-- The Σ-protocol's extractor on the transcripts at the two leaves. -/
@[expose] def sigmaExt (σ : SigmaProtocol ProbComp Stmt Wit Commit St Chal Resp rel)
    (t : VecTree (chals Chal) two) (ts : ((i : Fin 1) → Fin (two i)) → Commit × Resp) :
    ProbComp Wit :=
  σ.extract (leafPoints t 0 0) (ts fun _ => (0 : Fin 2)).2 (leafPoints t 1 0)
    (ts fun _ => (1 : Fin 2)).2

/-- A computation answered by fresh coins, with no ambient state, is itself. -/
theorem run'_simulateQ_coins {α : Type} (oa : ProbComp α) :
    (simulateQ (coins (S := Unit)) oa).run' () = oa := by
  simp [coins]

/-- The leaves of a one-round tree with two branches are the siblings at the root. -/
theorem leafPoints_eq_siblings (t : VecTree (chals Chal) two) (j : Fin 2) :
    leafPoints t j 0 = t.siblings (fun _ => 0) 0 j := by
  have hupd : Function.update (fun _ : Fin 1 => (0 : Fin 2)) 0 j = fun _ => j :=
    funext fun i => by fin_cases i; simp
  simp only [leafPoints, VecTree.siblings, hupd]

/-- The two transcripts at the leaves of a good tree share the commitment and accept at distinct
challenges, so the Σ-protocol's extractor returns a valid witness. -/
theorem sigmaExt_valid [Finite Chal]
    (σ : SigmaProtocol ProbComp Stmt Wit Commit St Chal Resp rel) (x : Stmt)
    (hss : σ.SpeciallySoundAt x)
    (commit : ProbComp (Commit × St)) (respond : St → Chal → ProbComp Resp)
    (F : ((i : Fin 1) → chals Chal i) → Commit × Resp)
    (hF : F ∈ support (fixedTape.eagerTable (proverRun commit respond)))
    (t : VecTree (chals Chal) two) (hstruct : t.IsStructured fun _ ch => Function.Injective ch)
    (hacc : ∀ p, σ.verify x (F (t.leaf p)).1 (t.leaf p 0) (F (t.leaf p)).2 = true)
    (w : Wit) (hw : w ∈ support (sigmaExt σ t fun p => F (t.leaf p))) : rel x w = true := by
  have hcommit : (F (leafPoints t 0)).1 = (F (leafPoints t 1)).1 :=
    fixedTape.eagerTable_fst_eq (Q := (i : Fin 1) → chals Chal i) (S := Commit × St)
      (A := Commit) (B := Resp) commit Prod.fst (fun s c => respond s.2 (c 0)) hF _ _
  have hne : leafPoints t 0 0 ≠ leafPoints t 1 0 := by
    rw [leafPoints_eq_siblings, leafPoints_eq_siblings]
    exact fun h => absurd (hstruct (fun _ => 0) 0 h) (by decide)
  have h0 : σ.verify x (F (leafPoints t 0)).1 (leafPoints t 0 0) (F (leafPoints t 0)).2 = true :=
    hacc fun _ => 0
  have h1 :
      σ.verify x (F (leafPoints t 0)).1 (leafPoints t 1 0) (F (leafPoints t 1)).2 = true := by
    rw [hcommit]
    exact hacc fun _ => 1
  exact hss (F (leafPoints t 0)).1 (leafPoints t 0 0) (leafPoints t 1 0) (F (leafPoints t 0)).2
    (F (leafPoints t 1)).2 hne h0 h1 w hw

/-- The extractor: the threshold finder with two branches against verdicts of complete reruns,
then recovery of the two transcripts from a cache of those runs, and the Σ-protocol's extractor. -/
@[expose] def sigmaRecover [SampleableType Chal] [DecidableEq Chal]
    (σ : SigmaProtocol ProbComp Stmt Wit Commit St Chal Resp rel) (x : Stmt) :
    OracleComp (unifSpec + rerunSpec ((i : Fin 1) → chals Chal i) (Commit × Resp)) (Option Wit) :=
  recover (fun c t => σ.verify x t.1 (c 0) t.2) (thresholdFinder (chals Chal) two) VecTree.leaf
    (sigmaExt σ)

/-- Against frozen reruns of a malicious prover, recovery gives a valid witness with probability at
least the prover's acceptance probability, averaged over challenges, minus the threshold error,
after at most two complete runs in expectation: the finder's own. -/
theorem sigma_recover [Fintype Chal] [SampleableType Chal] [DecidableEq Chal]
    (σ : SigmaProtocol ProbComp Stmt Wit Commit St Chal Resp rel) (x : Stmt)
    (hss : σ.SpeciallySoundAt x) (hc : 2 ≤ Fintype.card Chal)
    (commit : ProbComp (Commit × St)) (respond : St → Chal → ProbComp Resp) :
    (∑ c, Pr{let t ← proverRun commit respond c}[σ.verify x t.1 (c 0) t.2 = true]) /
          Fintype.card ((i : Fin 1) → chals Chal i) - thresholdError (chals Chal) two ≤
        Pr{let z ← fixedTape.attempt (proverRun commit respond) (sigmaRecover σ x)}[
          ∃ w, z.1 = some w ∧ rel x w = true] ∧
      expectedCalls (fixedTape.attempt (proverRun commit respond) (sigmaRecover σ x)) ≤
        2 := by
  have hk : ∀ i, 1 ≤ two i ∧ two i ≤ Fintype.card (chals Chal i) :=
    fun _ => ⟨(by norm_num : (1 : ℕ) ≤ 2), hc⟩
  have hb := fixedTape.recover_tree_bounds (proverRun commit respond)
    (fun c t => σ.verify x t.1 (c 0) t.2) (isTreeFinder_thresholdFinder (chals Chal) two hk)
    (sigmaExt σ) (fun w => rel x w = true) (sigmaExt_valid σ x hss commit respond)
  simp only [pure_bind, run'_simulateQ_coins] at hb
  refine ⟨tsub_le_iff_left.mpr (hb.1.trans
    (add_le_add le_rfl (mul_le_of_le_one_left zero_le tsub_le_self))), hb.2.trans ?_⟩
  norm_num

end VCVioTest.RewindingExtraction
