/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coverage.ExpectedCredit
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coverage.ExpectedCredit
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Settlement.Coverage
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Work.TapeLengths
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Price.Average
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Settlement.Coverage
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coupling.Tapes
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coupling.Guarded
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Price.Graph

/-! # Bounding residual winning probability by actual FORS coverage -/

public section

open OracleComp OracleSpec SignatureAlg MeasureTheory
open scoped ENNReal
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded
open scoped SLHDSA.SHAKE128s.Bridge.SharedExperiment.SampleSpaces
namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.GuardedFill

private theorem prEvent_extend_pair_le {α β γ : Type} (source : ProbComp α)
    (fill : α → ProbComp β) (secret : ProbComp γ)
    (hit : α × β × γ → Prop) (paid : α → Prop)
    (covers : ∀ b ∈ support source, ∀ st ∈ support (fill b), ∀ sk ∈ support secret,
      hit (b, st, sk) → paid b) :
    let run : ProbComp (α × β × γ) := do
      let b ← source
      let st ← fill b
      let sk ← secret
      pure (b, st, sk)
    Pr{let r ← run}[hit r] ≤ Pr{let b ← source}[paid b] := by
  intro run
  apply (prEvent_mono_of_support run hit (fun r => paid r.1) ?_).trans_eq
  · have projected : Prod.fst <$> run =ᵈ source := by
      simp only [run, map_bind, map_pure]
      conv_rhs => rw [← id_map source, map_eq_bind_pure_comp]
      apply EvalDistEq.bind_right
      intro b
      exact (OracleComp.EvalDistEq.bind_const _ _).trans (OracleComp.EvalDistEq.bind_const _ _)
    simpa only [prEvent_map] using projected.prEvent_eq paid
  · intro r mem
    simp only [run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at mem
    obtain ⟨b, hb, st, hst, sk, hs, rfl⟩ := mem
    exact covers b hb st hst sk hs

private theorem residual_le_of_block {s : FIPS205.core.PkSeed}
    {adv : Game.Adversary FIPS205.Answer PK} {caps : Nat × Nat}
    {fallback : (input : LabCommon.Domain) → LabCommon.Range input} {L R : Nat}
    (event : Filled → Prop) (paid : Block → Prop)
    (covers : ∀ (b : Block), b ∈ support (NoticingTape.blockRunOf
      (Native.nativeRun s adv true caps fallback) L R) →
      ∀ (st : LabState FIPS205.core), st ∈ support (RelabelState.endFill b.2.2.1.1.2.1) →
      ∀ secret : Secret,
        event (eraseTapes (b, st, secret)) → paid b) :
    Pr{let r ← ((slhGraph FIPS205.core s).deferredFillDraw ($ᵗ Secret)
      (labProgram s adv true true caps fallback))}[event r] ≤
      Pr{let b ← (NoticingTape.blockRunOf (Native.nativeRun s adv true caps fallback) L R)}[
        paid b] := by
  have marg := (eraseTapes_tapedFill s adv true caps fallback L R).prEvent_eq event
  rw [prEvent_map] at marg
  rw [← marg]
  apply prEvent_extend_pair_le _ (fun b : Block => RelabelState.endFill b.2.2.1.1.2.1)
    ($ᵗ Secret) (fun r => event (eraseTapes r)) paid
  intro b hb st hs secret _
  exact covers b hb st hs secret

private theorem block_covers_unpaid (q : Nat) (hq : 2 * q < 2 ^ 128)
    (s : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (b : Block) (hb : b ∈ support (NoticingTape.blockRunOf
      (Native.nativeRun s adv true (32 * q - 1, 2 ^ 64) fallback) (2 ^ 64 + 1) (16 * 2 ^ 128)))
    (st : LabState FIPS205.core) (hst : st ∈ support (RelabelState.endFill b.2.2.1.1.2.1))
    (secret : Secret) :
    Physical.residual s (eraseTapes (b, st, secret)) → actualCoverage b := by
  intro hit
  obtain ⟨⟨out, observed, won⟩, _, unpaid⟩ := hit
  have cb := Native.native_counts_le_tape_lengths q hq s adv fallback b.1.1 b.1.2 b.2
    (NoticingTape.mem_support_blockRunOf _ _ _ b hb).2.2
  change (if b.2.2.2.2 then none else some b.2.1.2) = some out at observed
  have nb : b.2.2.2.2 = false := by
    cases flag : b.2.2.2.2 with
    | false => rfl
    | true => simp [flag] at observed
  rw [nb] at observed
  have same : b.2.1.2 = out := Option.some.inj observed
  apply Native.fired_of_uncharged_winner q s adv fallback b hb cb.1 cb.2 st secret hst
    nb ((congrArg (SigningView.Wins id) same).mpr won)
  · exact fun conflict => unpaid (Or.inl (Or.inl conflict))
  · exact fun collision => unpaid (Or.inl (Or.inr collision))
  · exact fun hidden => unpaid (Or.inr (Or.inl hidden))

/-- The residual success event after the graph and key hazards were paid is a subevent of
the native used-prefix FORS coverage event, without an additional byte or key error. -/
theorem uncharged_probability_le_actualCoverage (q : Nat) (hq : 2 * q < 2 ^ 128)
    (s : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input) :
    Pr{let r ← ((slhGraph FIPS205.core s).deferredFillDraw ($ᵗ Secret)
      (labProgram s adv true true (32 * q - 1, 2 ^ 64) fallback))}[Physical.residual s r] ≤
      Pr{let b ← (NoticingTape.blockRunOf
        (Native.nativeRun s adv true (32 * q - 1, 2 ^ 64) fallback)
        (2 ^ 64 + 1) (16 * 2 ^ 128))}[actualCoverage b] :=
  residual_le_of_block (Physical.residual s) actualCoverage
    (block_covers_unpaid q hq s adv fallback)

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.GuardedFill
