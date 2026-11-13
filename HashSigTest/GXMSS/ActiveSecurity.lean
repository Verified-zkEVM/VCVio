/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Interval.Reductions.ActiveSecurity
import all HashSig.GXMSS.Security.Interval.Reductions.SplicedView
import all HashSig.GXMSS.Chain
import all HashSig.GXMSS.Scheme
import all HashSig.GXMSS.Merkle
import HashSig.GXMSS.Interval.Merkle.Basic

/-!
# Singleton nonmaximum code and strong freshness controls

A one-coordinate singleton code satisfies the core nonmaximum premise and cannot have two
codewords. A constant hash admits two different valid signatures at the same message/randomizer
pair. The actual first signing record therefore permits a fresh strong forgery by flipping its OTS.
Implementation imports expose signature equality and chain/tree computations for kernel controls.
-/

public section
namespace GXMSS.ActiveSecurityProbe
open ENNReal GXMSS.Reductions GXMSS.Interval.Reductions GXMSS.Interval.Reductions.Chain
open GXMSS.Interval.Unforgeability GXMSS.IntervalMerkle IncomparableEncoding
open OracleComp OracleSpec TweakableHash SyncSignatureUnforgeability

/-- A one-step, one-chain hash instance with a constant output. -/
@[expose] def hash : HashInstance Unit ((Fin 1 × Fin 1 × Fin 1) ⊕ (Fin 1 × Fin 1))
    (Bool ⊕ ((Bool × Bool) ⊕ (Fin 1 → Bool))) Bool 0 1 1 where
  thf := ⟨pure (), fun _ _ _ => false⟩
  digestInput := ⟨Sum.inl, Sum.inl_injective⟩
  pairInput := ⟨fun pair => Sum.inr (Sum.inl pair),
    Function.Injective.comp Sum.inr_injective Sum.inl_injective⟩
  vectorInput := ⟨fun vector => Sum.inr (Sum.inr vector),
    Function.Injective.comp Sum.inr_injective Sum.inr_injective⟩
  chainTweak := ⟨Sum.inl, Sum.inl_injective⟩
  treeTweak := ⟨Sum.inr, Sum.inr_injective⟩
  chain_ne_tree := fun c t => Sum.inl_ne_inr (a := c) (b := t)

/-- The only emitted word is zero, which is below the maximum digit one. -/
@[expose] def encoding : IncomparableEncoding Unit Unit Unit (Epoch 0) 1 2 where
  code := {fun _ => 0}
  incomparable := by
    intro x hx y hy hne
    exact (hne ((Set.mem_singleton_iff.mp hx).trans
      (Set.mem_singleton_iff.mp hy).symm)).elim
  encode := fun _ _ _ _ => some ⟨fun _ => 0, Set.mem_singleton _⟩

/-- The singleton global code satisfies the pointwise core premise. -/
theorem singleton_nonmaximum : encoding.NoMaximumOutput := by
  intro pp msg r ep word hword
  have hmem := encoding.mem_code_of_value_eq_some pp msg r ep hword
  have heq : word = (fun _ => 0) := by simpa [encoding] using hmem
  subst word
  exact ⟨0, by decide⟩

/-- The former two-codeword premise is impossible for this admitted encoding. -/
theorem singleton_not_two :
    ¬ ∃ x y : Codeword 1 2, x ∈ encoding.code ∧ y ∈ encoding.code ∧ x ≠ y := by
  rintro ⟨x, y, hx, hy, hne⟩
  have hx' : x = (fun _ => 0) := by simpa [encoding] using hx
  have hy' : y = (fun _ => 0) := by simpa [encoding] using hy
  exact hne (hx'.trans hy'.symm)

/-- The single available epoch is active. -/
@[expose] def whole : Interval 0 := ⟨0, 0, by decide⟩

private def starts (b : Bool) (_ : Epoch 0) (_ : Fin 1) := b

private def fillers : Fillers whole Bool := fun _ => false

private def honest (b : Bool) : GXMSS.Signature Unit Bool 0 1 :=
  GXMSS.Interval.signatureOfWord hash whole
    (GXMSS.Interval.keys hash whole () (starts b) fillers).2 0 ((fun _ => 0), ())

private def flip (sig : GXMSS.Signature Unit Bool 0 1) : GXMSS.Signature Unit Bool 0 1 :=
  { sig with ots := fun i => !sig.ots i }

private def source (b : Bool) : Result Unit Bool Unit Unit 0 1 :=
  let (pk, sk) := GXMSS.Interval.keys hash whole () (starts b) fillers
  ⟨pk, sk.complete, (0, (), flip (honest b)),
    Function.update emptyHistory 0 (some ((), some (honest b)))⟩

/-- Both the honest and altered signatures verify at the same message/randomizer pair. -/
private theorem two_valid_signatures (b : Bool) :
    GXMSS.Interval.verify hash encoding (source b).pk 0 () (honest b) = true ∧
      GXMSS.Interval.verify hash encoding (source b).pk 0 () (flip (honest b)) = true ∧
      honest b ≠ flip (honest b) := by
  cases b <;> decide

/-- Exact signature-pair freshness accepts the alternate OTS at the already consumed epoch. -/
private theorem active_strong_forgery (b : Bool) :
    activeMatchingEvent hash encoding 1 whole
      (GXMSS.Interval.keys hash whole () (starts b) fillers).2
      ((source b).pk, (source b).forgery, (source b).history) = true := by
  cases b <;> decide

/-- One actual signing request is followed by an altered signature at the same pair. -/
def adversary : SchemeAdversary Unit Bool Unit Unit 0 1 where
  forge _ := do
    let sig ← (unifSpec + signingSpec (Epoch 0) Unit (GXMSS.Signature Unit Bool 0 1)).query
      (.inr (0, ()))
    pure (0, (), flip (sig.getD ⟨(), fun _ => false, fun _ => false⟩))

/-- All requests are counted; this concrete program makes exactly one. -/
theorem one_request : SigningQueryBound 1 adversary := by
  intro pk
  suffices ∀ sig : Option (GXMSS.Signature Unit Bool 0 1),
      IsQueryBoundP (pure (0, (), flip (sig.getD ⟨(), fun _ => false, fun _ => false⟩)) :
        OracleComp (unifSpec + signingSpec (Epoch 0) Unit (GXMSS.Signature Unit Bool 0 1))
          (Forgery (Epoch 0) Unit (GXMSS.Signature Unit Bool 0 1)))
        (fun q => q.isRight = true) 0 by
    simpa [adversary] using this
  intro sig
  trivial

/-- The strong-forgery witness is returned by the actual shared signing runner. -/
private theorem actual_source (b : Bool) :
    GXMSS.Interval.viewFromKeys hash encoding 1 whole adversary () (starts b) fillers =
      (do
        let _ ← ($ᵗ Unit : ProbComp Unit)
        let out := source b
        pure (out.pk, out.forgery, out.history)) := by
  cases b <;>
    dsimp only [GXMSS.Interval.viewFromKeys, GXMSS.Interval.viewWithKeys, adversary,
      Forgery, ExperimentResult] <;>
    simp only [runWithSigningOracle, runWithSigningKernel, oraclesWithSigningKernel,
      run_simulateQ_query_bind, simulateQ_pure, StateT.run_pure, QueryImpl.add_apply_inr] <;>
    dsimp only [StateT.run, StateT.bind, StateT.pure, signingKernelOracle] <;>
    simp [GXMSS.Interval.scheme, GXMSS.Interval.sign, IncomparableEncoding.retry_one,
      IncomparableEncoding.attempt, encoding, IncomparableEncoding.value, emptyHistory,
      record, Epoch.IsActive, whole, source, honest, flip, GXMSS.Interval.keys, GXMSS.keys,
      map_eq_bind_pure_comp, bind_assoc]

/-- The public core applies to this singleton code without a two-codeword witness. -/
theorem singleton_core_bound :
    𝒟[activeMatchingExperiment hash encoding 1 whole adversary] {true} ≤
      TargetCollisionResistance.advantage
        (encodingTargetCollisionReduction hash encoding 1 1 whole adversary) +
      SM_DT_TCR_Advantage
        (sameMessageRandomizerChainTargetCollisionReduction hash encoding 1 whole adversary) +
      SM_DT_TCR_Advantage (chainCutTargetCollisionReduction hash encoding 1 whole adversary) +
      SM_DT_PRE_Advantage
        (selectedChainPreimageReduction hash encoding 1 whole (by decide) (by decide) adversary) +
      SM_DT_UD_Advantage
        (chainUndetectabilityReduction hash encoding 1 whole
          (by decide) (by decide) adversary) := by
  have h := activeMatchingMass_le_advantages hash encoding 1 1 whole
    (by decide) (by decide) singleton_nonmaximum adversary one_request
  simpa [whole] using h

end GXMSS.ActiveSecurityProbe
