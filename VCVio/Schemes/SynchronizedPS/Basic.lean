/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.CryptoFoundations.AggregateSignatureAlg.Synchronized
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import Mathlib.LinearAlgebra.BilinearMap

/-! # Synchronized Pointcheval–Sanders aggregate signatures

Keys are `(x • g₂, y • g₂)`, a share on `(t, m)` is `(x + y*m) • H(t)`, and
aggregation adds shares. Verification requires a common period and checks the pairing against
the sum of the message-weighted public keys. This ports `Signatures/SynchronizedPS/Game.lean`
in Gurkan's signature-security-lean at revision 3eaa8c4.
-/

public section

open OracleComp OracleSpec

namespace SynchronizedPS

/-- Derive both public-key components from the certified scalar pair. -/
@[expose] def publicKeyOf {F G₂ : Type} [SMul F G₂] (g₂ : G₂) (sk : F × F) : G₂ × G₂ :=
  (sk.1 • g₂, sk.2 • g₂)

/-- The certified co-signers' scalar contribution at their declared messages. -/
@[expose] def offset {F : Type} [Field F] (others : List ((F × F) × F)) : F :=
  (others.map fun p => p.1.1 + p.1.2 * p.2).sum

/-- Synchronized PS with one period hash oracle and an independent uniform-sampling interface.
Empty aggregates verify exactly when their pairing is zero; nonempty aggregates must have one
common period. Certified-key experiments always verify a nonempty list. -/
@[expose] def scheme {F Period G₁ G₂ Gₜ : Type} [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ] [DecidableEq Period]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₂ : G₂) :
    AggregateSignatureAlg (OracleComp (unifSpec + (Period →ₒ G₁)))
      (Period × F) (G₂ × G₂) (F × F) G₁ where
  keygen := do
    let x ← ($ᵗ F : ProbComp F)
    let y ← ($ᵗ F : ProbComp F)
    return (publicKeyOf g₂ (x, y), (x, y))
  sign _ sk tm := do
    let h ← (Period →ₒ G₁).query tm.1
    return (sk.1 + sk.2 * tm.2) • h
  verify pk tm σ := do
    let h ← (Period →ₒ G₁).query tm.1
    return decide (e h (pk.1 + tm.2 • pk.2) = e σ g₂)
  aggregate sigs := pure sigs.sum
  aggregateVerify pairs σ := do
    match pairs with
    | [] => return decide (0 = e σ g₂)
    | (_, tm) :: _ =>
      if ¬pairs.all (fun p => decide (p.2.1 = tm.1)) then return false
      let h ← (Period →ₒ G₁).query tm.1
      return decide (e h (pairs.map (fun p => p.1.1 + p.2.2 • p.1.2)).sum = e σ g₂)

/-- Bilinearity verifies an honest aggregate with a common hash, including the empty sum. -/
theorem pairing_sum_signatures {F G₁ G₂ Gₜ : Type} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₂ : G₂) (h : G₁)
    (signers : List ((F × F) × F)) :
    e h (signers.map (fun p => (publicKeyOf g₂ p.1).1 +
        p.2 • (publicKeyOf g₂ p.1).2)).sum =
      e (signers.map (fun p => (p.1.1 + p.1.2 * p.2) • h)).sum g₂ := by
  induction signers with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons, map_add, LinearMap.add_apply, ih]
    congr 1
    simp [publicKeyOf, add_smul, mul_smul, mul_comm]

/-- With a consistently interpreted period hash, every honest aggregate verifies. -/
theorem aggregateVerify_honest {F Period G₁ G₂ Gₜ : Type} [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ] [DecidableEq Period]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₂ : G₂) (H : Period → G₁) (t : Period)
    (signers : List ((F × F) × F)) :
    simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn H))
      ((scheme e g₂).aggregateVerify
        (signers.map (fun p => (publicKeyOf g₂ p.1, (t, p.2))))
        (signers.map (fun p => (p.1.1 + p.1.2 * p.2) • H t)).sum) =
      (pure true : ProbComp Bool) := by
  have hp := pairing_sum_signatures e g₂ (H t) signers
  cases signers with
  | nil => simp [scheme]
  | cons p ps =>
    have hId (a : G₁) : (liftM (m := Id) (a : Id G₁) : ProbComp G₁) = pure a := rfl
    simpa [scheme, List.map_map, Function.comp_def, unifFwdAnswerImpl,
      QueryImpl.simulateQ_add_liftM_query_right, hId, add_assoc, add_left_comm, add_comm] using
      congrArg (pure : Bool → ProbComp Bool) (decide_eq_true hp)

/-- Certified co-signers contribute their known scalar offset to the honest pairing equation. -/
theorem aggregateVerify_certified {F Period G₁ G₂ Gₜ : Type} [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ] [DecidableEq Period]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₂ : G₂) (x y : F) (tm : Period × F)
    (others : List ((F × F) × F)) (σ : G₁) :
    (scheme e g₂).aggregateVerify
      ((publicKeyOf g₂ (x, y), tm) ::
        others.map (fun p => (publicKeyOf g₂ p.1, (tm.1, p.2)))) σ = (do
          let h ← (Period →ₒ G₁).query tm.1
          return decide (e h ((x + y * tm.2 + offset others) • g₂) = e σ g₂)) := by
  simp only [scheme, publicKeyOf, bind_pure_comp, add_smul, mul_smul, map_add, map_smul,
    List.all_eq_true, decide_eq_true_eq, Prod.forall, not_forall,
    List.sum_map_add, ite_not, List.all_cons, decide_true, List.all_map, Function.comp_def,
    Bool.true_and, implies_true, ↓reduceIte, List.map_cons, List.map_map, List.sum_cons,
    add_left_comm, add_assoc, offset, mul_comm, List.sum_smul]
  congr 1
  funext h
  rw [smul_comm y tm.2 (e h g₂)]

/-- Honest signing, aggregation and verification succeed with probability one under the
shared random-oracle runtime, for any period and any list of certified keys and messages. -/
theorem aggregate_correctness {F Period G₁ G₂ Gₜ : Type} [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    [DecidableEq Gₜ] [DecidableEq Period]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₂ : G₂) (t : Period)
    (signers : List ((F × F) × F)) :
    (ProbCompRuntime.rom (Period →ₒ G₁)).evalDist (do
      let sigs ← signers.mapM fun p => (scheme e g₂).sign (publicKeyOf g₂ p.1) p.1 (t, p.2)
      let σ ← (scheme (Period := Period) e g₂).aggregate sigs
      (scheme e g₂).aggregateVerify
        (signers.map (fun p => (publicKeyOf g₂ p.1, (t, p.2)))) σ) {true} = 1 := by
  rw [ProbCompRuntime.rom_evalDist]
  change 𝒟[(simulateQ (Period →ₒ G₁).romImpl _).run' ∅] {b | b = true} = 1
  rw [evalDist_apply_setOf_simulateQ_romImpl_run'_eq_one_iff]
  intro f _
  have hId (a : G₁) : (liftM (m := Id) (a : Id G₁) : ProbComp G₁) = pure a := rfl
  have hs (ps : List ((F × F) × F)) :
      simulateQ (unifFwdAnswerImpl f)
        (ps.mapM fun p => (scheme e g₂).sign (publicKeyOf g₂ p.1) p.1 (t, p.2)) =
      (pure (ps.map fun p => (p.1.1 + p.1.2 * p.2) • (f t).run) : ProbComp (List G₁)) := by
    induction ps with
    | nil => simp
    | cons p ps ih =>
      simp only [List.mapM_cons, simulateQ_bind, simulateQ_pure, ih]
      simp [scheme, unifFwdAnswerImpl, QueryImpl.simulateQ_add_liftM_query_right, hId, Id.run]
  simp only [simulateQ_bind, hs, pure_bind]
  change 𝒟[simulateQ (unifFwdAnswerImpl f)
    (pure (signers.map (fun p => (p.1.1 + p.1.2 * p.2) • (f t).run)).sum >>= fun σ =>
      (scheme e g₂).aggregateVerify
        (signers.map (fun p => (publicKeyOf g₂ p.1, (t, p.2)))) σ)] {b | b = true} = 1
  simp only [pure_bind]
  have hv : simulateQ (unifFwdAnswerImpl f)
      ((scheme e g₂).aggregateVerify
        (signers.map (fun p => (publicKeyOf g₂ p.1, (t, p.2))))
        (signers.map (fun p => (p.1.1 + p.1.2 * p.2) • (f t).run)).sum) =
      (pure true : ProbComp Bool) :=
    aggregateVerify_honest e g₂ (fun t => (f t).run) t signers
  rw [hv]
  simp

end SynchronizedPS
