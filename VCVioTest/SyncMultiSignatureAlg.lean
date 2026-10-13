/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module

public import VCVio.CryptoFoundations.SyncMultiSignatureAlg
public import VCVioTest.SyncSignatureAlg

/-!
# Independent Definition 9 probes

The honest count-sensitive scheme accepts every finite participant count. Explicit failure and
missing mass both reject at one participant. A fair-key scheme accepts only true public keys:
its singleton key average is one half, but its false key violates the same per-tuple bound.
The configured order-sensitive scheme encodes the aligned pairs as its aggregate, so swapping
signatures alone is detectably different. Repeated keys and the empty tuple remain valid inputs.
These examples establish correctness observations, not Definition 10 security or compression.
-/

public section

namespace SyncMultiSignatureProbe

open ENNReal OracleComp SyncMultiSignatureAlg

/-- Independently sequencing pure computations preserves every coordinate. -/
theorem sequence_pure {m : Type → Type} [Monad m] [LawfulMonad m]
    {α : Type} (k : ℕ) (f : Fin k → α) :
    Fin.mOfFn k (fun i => (pure (f i) : m α)) = pure f := by
  induction k with
  | zero =>
    have hf : f = Fin.elim0 := funext fun i => i.elim0
    simp [Fin.mOfFn, hf]
  | succ k ih =>
    simp only [Fin.mOfFn, ih, pure_bind]
    congr 1
    exact Fin.cons_self_tail f

/-- Successful coordinate outputs are aligned with exactly their original public keys. -/
theorem accepts_all_some {m : Type → Type} [Monad m] {M PK SK S A E : Type}
    (alg : SyncMultiSignatureAlg m M PK SK S A E) {k : ℕ}
    (pks : Fin k → PK) (ep : E) (msg : M) (sigs : Fin k → S) :
    alg.accepts pks ep msg (fun i => some (sigs i)) =
      alg.verify pks ep msg (alg.aggregate ep msg fun i => (pks i, sigs i)) := by
  unfold accepts
  rw [show (fun i => some (sigs i)) = (fun i => (pure (sigs i) : Option S)) from rfl]
  rw [sequence_pure]
  rfl

/-- A count-sensitive honest scheme at arbitrary epochs. -/
@[expose] def honest (E : Type) :
    SyncMultiSignatureAlg ProbComp Unit Unit Unit Unit ℕ E where
  keygen := pure ((), ())
  sign _ _ _ := pure (some ())
  aggregate {k} _ _ _ := k
  verify {k} _ _ _ agg := agg == k

/-- Every fixed tuple succeeds for the honest scheme, including zero and repeated participants. -/
theorem honest_success (E : Type) (k : ℕ) (keys : Fin k → Unit × Unit)
    (ep : E) (msg : Unit) :
    (honest E).successMass ProbCompRuntime.probComp keys ep msg = 1 := by
  simp [successMass, honest,
    sequence_pure, accepts_all_some]

/-- The native independent-signing theorem includes the empty ordered tuple. -/
theorem honest_independent_signing_empty (E : Type) (ep : E) :
    let keys : Fin 0 → Unit × Unit := fun i => i.elim0
    let outs : Fin 0 → Option Unit := fun i => i.elim0
    Pr{let sampled ← Fin.mOfFn 0 (fun i => (honest E).sign (keys i).2 ep ())}[
      sampled = outs] =
      ∏ i, Pr{let out ← (honest E).sign (keys i).2 ep ()}[out = outs i] := by
  dsimp
  exact (honest E).independent_signing_probability (fun i => i.elim0) ep ()
    (fun i => i.elim0)

/-- Honest correctness holds at every participant count and every epoch type. -/
theorem honest_complete_zero (E : Type) :
    (honest E).Complete ProbCompRuntime.probComp (fun _ => 0) := by
  intro k keys hkeys ep msg
  simp [honest_success]

/-- Singleton signing returns failure despite an always-accepting aggregate verifier. -/
@[expose] def alwaysFails : SyncMultiSignatureAlg ProbComp Unit Unit Unit Unit Unit Unit where
  keygen := pure ((), ())
  sign _ _ _ := pure none
  aggregate _ _ _ := ()
  verify _ _ _ _ := true

/-- Returned signing failure has no singleton aggregate success mass. -/
theorem returned_failure :
    alwaysFails.successMass ProbCompRuntime.probComp (fun _ : Fin 1 => ((), ())) () () = 0 := by
  simp [successMass, alwaysFails,
    Fin.mOfFn, accepts]

/-- Completely missing runtime output mass is not normalized into successful signatures. -/
theorem missing_mass {m : Type → Type} [Monad m] {M PK SK S A E : Type}
    (alg : SyncMultiSignatureAlg m M PK SK S A E) (runtime : ProbCompRuntime m)
    (ks : PK × SK) (ep : E) (msg : M)
    (h : runtime.evalDist (alg.accepts (fun _ : Fin 1 => ks.1) ep msg <$>
      Fin.mOfFn 1 (fun _ => alg.sign ks.2 ep msg)) = 0) :
    alg.successMass runtime (fun _ : Fin 1 => ks) ep msg = 0 := by
  simp [successMass, h]

/-- With no participants the failing signer is never invoked; the empty aggregate is accepted. -/
theorem empty_failure_signer :
    alwaysFails.successMass ProbCompRuntime.probComp (fun i : Fin 0 => i.elim0) () () = 1 := by
  simp [successMass, alwaysFails, Fin.mOfFn, accepts]

/-- A fair public key determines whether singleton aggregate verification accepts. -/
@[expose] def mixed : SyncMultiSignatureAlg ProbComp Unit Bool Unit Unit Unit Unit where
  keygen := (fun b => (b, ())) <$> ($ᵗ Bool)
  sign _ _ _ := pure (some ())
  aggregate _ _ _ := ()
  verify pks _ _ _ := (List.ofFn pks).all id

/-- Both fair public keys, including false, are producible. -/
theorem mixed_generated (b : Bool) : mixed.Generated ProbCompRuntime.probComp (b, ()) := by
  simp [Generated, mixed]

/-- The singleton good key has full successful aggregate mass. -/
theorem mixed_good :
    mixed.successMass ProbCompRuntime.probComp (fun _ : Fin 1 => (true, ())) () () = 1 := by
  simp [successMass, mixed, Fin.mOfFn, accepts,
    List.ofFn_succ]

/-- The singleton bad key has zero successful aggregate mass. -/
theorem mixed_bad :
    mixed.successMass ProbCompRuntime.probComp (fun _ : Fin 1 => (false, ())) () () = 0 := by
  simp [successMass, mixed, Fin.mOfFn, accepts,
    List.ofFn_succ]

/-- Key-averaged singleton acceptance, observing both runtime steps explicitly. -/
@[expose] noncomputable def mixedAverage : ℝ≥0∞ :=
  ProbCompRuntime.probComp.evalDist (do
    let ks ← mixed.keygen
    let outs ← Fin.mOfFn 1 (fun _ => mixed.sign ks.2 () ())
    return mixed.accepts (fun _ => ks.1) () () outs) {true}

/-- Averaging over the key generator hides half of the bad-key behavior. -/
theorem mixed_average : mixedAverage = 2⁻¹ := by
  simp [mixedAverage, mixed, Fin.mOfFn, accepts, List.ofFn_succ]

/-- An error allowance of one half at every count fails on the producible bad singleton. -/
theorem not_mixed_complete_half :
    ¬ mixed.Complete ProbCompRuntime.probComp (fun _ => 2⁻¹) := by
  intro h
  have hbad := h 1 (fun _ => (false, ())) (fun _ => mixed_generated false) () ()
  rw [mixed_bad] at hbad
  norm_num at hbad

/-- The singleton averaged bound holds while Definition 9's per-tuple bound fails. -/
theorem mixed_separates : (1 - (2⁻¹ : ℝ≥0∞) ≤ mixedAverage) ∧
    ¬ mixed.Complete ProbCompRuntime.probComp (fun _ => 2⁻¹) := by
  refine ⟨?_, not_mixed_complete_half⟩
  rw [mixed_average]
  norm_num

/-- Configuration is captured by signing and verification; aggregation preserves pair order. -/
@[expose] def ordered (E : Type) (cfg : Bool) :
    SyncMultiSignatureAlg ProbComp Unit Bool Bool Bool (List (Bool × Bool)) E where
  keygen := (fun b => (b, b)) <$> ($ᵗ Bool)
  sign sk _ _ := pure (some (cfg != sk))
  aggregate _ _ pairs := List.ofFn pairs
  verify pks _ _ agg := agg == List.ofFn (fun i => (pks i, cfg != pks i))

/-- Repeating a key preserves both coordinate positions in the native product theorem. -/
theorem ordered_independent_signing_repeated (cfg : Bool) :
    let keys : Fin 2 → Bool × Bool := ![(true, true), (true, true)]
    let outs : Fin 2 → Option Bool := ![some (cfg != true), some (cfg != true)]
    Pr{let sampled ← Fin.mOfFn 2 (fun i => (ordered Unit cfg).sign (keys i).2 () ())}[
      sampled = outs] =
      ∏ i, Pr{let out ← (ordered Unit cfg).sign (keys i).2 () ()}[out = outs i] := by
  dsimp
  exact (ordered Unit cfg).independent_signing_probability
    ![(true, true), (true, true)] () () ![some (cfg != true), some (cfg != true)]

/-- Correctly aligned distinct keys verify for either constructor configuration. -/
theorem aligned_order (cfg : Bool) :
    (ordered Unit cfg).accepts ![false, true] () () ![some (cfg != false), some (cfg != true)] =
      true := by
  cases cfg <;> decide

/-- Swapping signatures while fixing the key order rejects. -/
theorem swapped_signatures (cfg : Bool) :
    (ordered Unit cfg).accepts ![false, true] () () ![some (cfg != true), some (cfg != false)] =
      false := by
  cases cfg <;> decide

/-- Repeated public keys are accepted when their signatures occupy the matching positions. -/
theorem repeated_keys (cfg : Bool) :
    (ordered Unit cfg).accepts ![true, true] () () ![some (cfg != true), some (cfg != true)] =
      true := by
  cases cfg <;> decide

/-- Empty aggregation is observed by the verifier at the same arbitrary epoch. -/
theorem ordered_empty (E : Type) (cfg : Bool) (ep : E) :
    (ordered E cfg).accepts (fun i : Fin 0 => i.elim0) ep ()
      (fun i : Fin 0 => i.elim0) = true := by
  simp [accepts, Fin.mOfFn, ordered, List.ofFn_zero]

/-- Returned-failure signing violates zero-error correctness at a producible singleton. -/
theorem not_alwaysFails_complete_zero :
    ¬ alwaysFails.Complete ProbCompRuntime.probComp (fun _ => 0) := by
  intro h
  have hkeys : alwaysFails.GeneratedTuple ProbCompRuntime.probComp
      (fun _ : Fin 1 => ((), ())) := by
    intro i
    simp [Generated, alwaysFails]
  have hbad := h 1 _ hkeys () ()
  simp [returned_failure] at hbad

/-- An empty tuple does not bypass an aggregate verifier that rejects it. -/
@[expose] def rejectsEmpty : SyncMultiSignatureAlg ProbComp Unit Unit Unit Unit ℕ Unit :=
  { honest Unit with verify := fun {k} _ _ _ _ => decide (0 < k) }

/-- Empty verification rejection has zero success mass despite making no signing calls. -/
theorem empty_rejection :
    rejectsEmpty.successMass ProbCompRuntime.probComp (fun i : Fin 0 => i.elim0) () () = 0 := by
  simp [successMass, rejectsEmpty, Fin.mOfFn, accepts]

/-- Producibility for the order-sensitive family requires matching public and secret bits. -/
theorem ordered_generated_iff (E : Type) (cfg : Bool) (ks : Bool × Bool) :
    (ordered E cfg).Generated ProbCompRuntime.probComp ks ↔ ks.1 = ks.2 := by
  rcases ks with ⟨pk, sk⟩
  cases pk <;> cases sk <;>
    simp [Generated, ordered]

/-- Correctly generated tuples have full success mass for either fixed configuration. -/
theorem ordered_success (E : Type) (cfg : Bool) (k : ℕ) (keys : Fin k → Bool × Bool)
    (hkeys : ∀ i, (keys i).1 = (keys i).2) (ep : E) (msg : Unit) :
    (ordered E cfg).successMass ProbCompRuntime.probComp keys ep msg = 1 := by
  simp [successMass, ordered,
    sequence_pure, accepts_all_some, hkeys]

/-- Every configuration has zero error for every producible tuple and arbitrary epoch type. -/
theorem ordered_complete_zero (E : Type) :
    ∀ cfg, (ordered E cfg).Complete ProbCompRuntime.probComp (fun _ => 0) := by
  intro cfg k keys hkeys ep msg
  have heq : ∀ i, (keys i).1 = (keys i).2 :=
    fun i => (ordered_generated_iff E cfg (keys i)).mp (hkeys i)
  simp [ordered_success E cfg k keys heq]

/-- Repeated keys are a producible two-participant tuple. -/
theorem repeated_generated (cfg : Bool) :
    (ordered Unit cfg).GeneratedTuple ProbCompRuntime.probComp ![(true, true), (true, true)] := by
  intro i
  rw [ordered_generated_iff]
  fin_cases i <;> rfl

end SyncMultiSignatureProbe
