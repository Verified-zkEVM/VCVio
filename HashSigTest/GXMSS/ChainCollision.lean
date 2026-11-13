/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Interval.Reductions.ChainCollision
import all HashSig.GXMSS.Security.Interval.Reductions.ChainCollision
import HashSig.GXMSS.Security.Interval.Reductions.SplicedView
import HashSig.GXMSS.Security.Interval.Reductions.ChainPrograms
import HashSig.GXMSS.Security.Auxiliary.ChainWitnesses
import HashSig.GXMSS.Security.Reductions.TargetRegistration.Chains
import all HashSig.GXMSS.Chain
import HashSig.GXMSS.Merkle
import HashSig.GXMSS.Interval.Merkle.Basic
import VCVio.CryptoFoundations.SyncSignatureAlg.Unforgeability
import HashSig.GXMSS.Security.Interval.Auxiliary.Interaction

/-!
# Registered chain collision orientation controls

The first chain step is the identity and later steps return false. Honest and forged paths can
therefore differ at the designated cut and merge at the next registered target. The tests retain
the actual encoding, complete signature history and honest-first native target orientation.
-/

public section
namespace GXMSS.ChainCollisionProbe
open GXMSS.Reductions GXMSS.Interval.Reductions.Chain GXMSS.IntervalMerkle
open IncomparableEncoding OracleComp OracleSpec SyncSignatureUnforgeability

/-- Identity at the first chain step and a constant hash at every later step. -/
@[expose] def hash : HashInstance Unit ((Fin 1 × Fin 2 × Fin 3) ⊕ (Fin 1 × Fin 1))
    (Bool ⊕ ((Bool × Bool) ⊕ (Fin 2 → Bool))) Bool 0 2 2 where
  thf := ⟨pure (), fun _ tweak input => match tweak, input with
    | .inl (_, _, position), .inl x => if position.val = 0 then x else false
    | _, _ => false⟩
  digestInput := ⟨Sum.inl, Sum.inl_injective⟩
  pairInput := ⟨fun pair => Sum.inr (Sum.inl pair),
    Function.Injective.comp Sum.inr_injective Sum.inl_injective⟩
  vectorInput := ⟨fun vector => Sum.inr (Sum.inr vector),
    Function.Injective.comp Sum.inr_injective Sum.inr_injective⟩
  chainTweak := ⟨Sum.inl, Sum.inl_injective⟩
  treeTweak := ⟨Sum.inr, Sum.inr_injective⟩
  chain_ne_tree := fun c t => Sum.inl_ne_inr (a := c) (b := t)

private def honestWord : Codeword 2 4 := fun i => if i = 0 then 1 else 0

private def forgedWord : Codeword 2 4 := fun i => if i = 0 then 0 else 1

private def encoding : IncomparableEncoding Unit Bool Unit (Epoch 0) 2 4 where
  code := {honestWord, forgedWord}
  incomparable := by
    intro x hx y hy hne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl
    · rcases hy with rfl | rfl
      · exact (hne rfl).elim
      · exact ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩
    · rcases hy with rfl | rfl
      · exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩
      · exact (hne rfl).elim
  encode := fun _ msg _ _ => if msg then some ⟨honestWord, by simp⟩
    else some ⟨forgedWord, by simp⟩

private def whole : Interval 0 := ⟨0, 0, by decide⟩

/-- Two independently chosen start cells for the single epoch. -/
@[expose] def starts (a b : Bool) (_ : Epoch 0) (i : Fin 2) : Bool :=
  if i = 0 then a else b

private def fillers : Fillers whole Bool := fun _ => false

private def honest (a b : Bool) : GXMSS.Signature Unit Bool 0 2 :=
  GXMSS.Interval.signatureOfWord hash whole
    (GXMSS.Interval.keys hash whole () (starts a b) fillers).2 0 (honestWord, ())

private def flip (sig : GXMSS.Signature Unit Bool 0 2) : GXMSS.Signature Unit Bool 0 2 :=
  { sig with ots := fun i => if i = 0 then !sig.ots 0 else sig.ots 1 }

private def forged (a b : Bool) : GXMSS.Signature Unit Bool 0 2 := flip (honest a b)

private def source (a b : Bool) : Result Unit Bool Bool Unit 0 2 :=
  let (pk, sk) := GXMSS.Interval.keys hash whole () (starts a b) fillers
  ⟨pk, sk.complete, (0, false, forged a b),
    Function.update emptyHistory 0 (some (true, some (honest a b)))⟩

private def state (a b : Bool) : TCRKeyState Unit
    ((Fin 1 × Fin 2 × Fin 3) ⊕ (Fin 1 × Fin 1))
    (Bool ⊕ ((Bool × Bool) ⊕ (Fin 2 → Bool))) Bool 0 2 :=
  ⟨starts a b, GXMSS.endpoints hash () (starts a b), false,
    endpointTargets hash () (starts a b), false⟩

/-- All six positive targets fit within the original eight-target chain capacity. -/
theorem registered_capacity :
    (endpointTargets hash () (starts false false)).length = 6 ∧
      (chainTCRProblem hash).numTargets = 8 := by
  rw [endpointTargets_length]
  exact ⟨rfl, rfl⟩

private def sameSource (a b : Bool) : Result Unit Bool Bool Unit 0 2 :=
  { source a b with forgery := (0, true, forged a b) }

/-- Equal message and randomizer retain the unequal OTS collision at target one. -/
private theorem same_message_candidate (a b : Bool) :
    firstChainCandidate hash encoding (state a b) () (sameSource a b) =
      (1, Sum.inl (!a)) := by
  cases a <;> cases b <;> decide

/-- The same-message witness also wins with its honest input registered first. -/
private theorem same_message_wins (a b : Bool) :
    firstChainCandidateWins hash () (endpointTargets hash () (starts a b))
      (firstChainCandidate hash encoding (state a b) () (sameSource a b)) = true := by
  cases a <;> cases b <;> decide

/-- The designated cut is non-aligned, and the merge is at registered target one. -/
private theorem cut_candidate (a b : Bool) :
    secondChainCandidate hash encoding (state a b) () (source a b) =
      (1, Sum.inl (!a)) := by
  cases a <;> cases b <;> decide

/-- The exact registered honest-first target accepts the different forged input. -/
private theorem cut_wins (a b : Bool) :
    firstChainCandidateWins hash () (endpointTargets hash () (starts a b))
      (secondChainCandidate hash encoding (state a b) () (source a b)) = true := by
  cases a <;> cases b <;> decide

/-- The first target's input is the honest value, rather than the extracted forged value. -/
private theorem target_orientation (a b : Bool) :
    (endpointTargets hash () (starts a b))[1]? =
      some (hash.chainTweak (0, 0, ⟨1, by decide⟩), hash.digestInput a) := by
  cases a <;> cases b <;> decide

private def adversary : SchemeAdversary Unit Bool Bool Unit 0 2 where
  forge _ := do
    let sig ← (unifSpec + signingSpec (Epoch 0) Bool (GXMSS.Signature Unit Bool 0 2)).query
      (.inr (0, true))
    pure (0, false, flip (sig.getD ⟨(), fun _ => false, fun _ => false⟩))

/-- The constructed full collision witness is the actual one-request signing view. -/
private theorem actual_source (a b : Bool) :
    GXMSS.Interval.viewFromKeys hash encoding 1 whole adversary () (starts a b) fillers =
      (do
        let _ ← ($ᵗ Unit : ProbComp Unit)
        let out := source a b
        pure (out.pk, out.forgery, out.history)) := by
  cases a <;> cases b <;>
    dsimp only [GXMSS.Interval.viewFromKeys, GXMSS.Interval.viewWithKeys, adversary,
      Forgery, ExperimentResult] <;>
    simp only [runWithSigningOracle, runWithSigningKernel, oraclesWithSigningKernel,
      run_simulateQ_query_bind, simulateQ_pure, StateT.run_pure, QueryImpl.add_apply_inr] <;>
    dsimp only [StateT.run, StateT.bind, StateT.pure, signingKernelOracle] <;>
    simp [GXMSS.Interval.scheme, GXMSS.Interval.sign, IncomparableEncoding.retry_one,
      IncomparableEncoding.attempt, encoding, IncomparableEncoding.value, emptyHistory,
      record, Epoch.IsActive, whole, source, forged, honest, flip,
      GXMSS.Interval.keys, GXMSS.keys, map_eq_bind_pure_comp, bind_assoc]

end GXMSS.ChainCollisionProbe
