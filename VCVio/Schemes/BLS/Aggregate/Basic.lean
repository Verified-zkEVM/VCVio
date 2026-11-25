/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.AggregateSignatureAlg
public import VCVio.Schemes.BLS.Basic

/-! # BGLS aggregate signatures

The aggregate BLS scheme of Boneh, Gentry, Lynn and Shacham (EUROCRYPT 2003), in additive
notation. Keys lie in the second source and hashes and signatures in the first source.
The distinct-message check is part of BGLS's scheme and prevents the repeated-message
rogue-key attack. The public Type 2 source map is needed by extraction, not by the algorithms.
-/

public section

open OracleComp OracleSpec

namespace BLS.Aggregate

variable {F G₁ G₂ Gₜ M : Type}

/-- Sum the pairing contributions, querying the hash oracle once for each listed message. -/
@[expose] def pairingSum [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) : List (G₂ × M) → OracleComp (M →ₒ G₁) Gₜ
  | [] => pure 0
  | (pk, msg) :: pairs => do
    let h ← (M →ₒ G₁).query msg
    let rest ← pairingSum e pairs
    return e h pk + rest

/-- BGLS aggregate BLS with second-source public keys. Aggregation adds signatures.
Aggregate verification first rejects repeated messages, as required by BGLS, and then
checks the sum of pairings. Randomness and message hashes occupy separate oracle summands. -/
@[expose] def scheme [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ] [DecidableEq M]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₂ : G₂) :
    AggregateSignatureAlg (OracleComp (unifSpec + (M →ₒ G₁))) M G₂ F G₁ where
  keygen := do
    let x ← ($ᵗ F : ProbComp F)
    return (x • g₂, x)
  sign _ x msg := do
    let h ← (M →ₒ G₁).query msg
    return x • h
  verify pk msg σ := do
    let h ← (M →ₒ G₁).query msg
    return decide (e σ g₂ = e h pk)
  aggregate sigs := pure sigs.sum
  aggregateVerify pairs σ := do
    if ¬(pairs.map Prod.snd).Nodup then return false
    let rhs ← pairingSum e pairs
    return decide (e σ g₂ = rhs)

/-- Evaluating the verification hashes against a fixed function gives the corresponding
sum of pairings. A random oracle uses one such function consistently across all calls. -/
theorem simulateQ_pairingSum [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (H : M → G₁) (pairs : List (G₂ × M)) :
    simulateQ (r := Id) (fun msg => H msg : QueryImpl (M →ₒ G₁) Id)
        (pairingSum e pairs) = (pairs.map (fun p => e (H p.2) p.1)).sum := by
  induction pairs with
  | nil => rfl
  | cons p pairs ih =>
    rcases p with ⟨pk, msg⟩
    simp [pairingSum, ih]
    rfl

/-- Bilinearity makes the sum of honest signatures satisfy the aggregate pairing equation,
for arbitrary secret keys, messages, and a consistently interpreted hash function. -/
theorem pairing_sum_signatures [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₂ : G₂) (H : M → G₁)
    (signers : List (F × M)) :
    e (signers.map (fun p => p.1 • H p.2)).sum g₂ =
      (signers.map (fun p => e (H p.2) (p.1 • g₂))).sum := by
  induction signers with
  | nil => simp
  | cons p signers ih => simp [ih]

/-- Under any fixed hash function, an aggregate of honest signatures on distinct messages
is accepted. Secret keys may repeat and no nondegeneracy assumption is needed. -/
theorem aggregateVerify_honest [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ] [DecidableEq M]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₂ : G₂) (H : M → G₁)
    (signers : List (F × M)) (hd : (signers.map Prod.snd).Nodup) :
    simulateQ (unifFwdAnswerImpl (fun msg => H msg : QueryImpl (M →ₒ G₁) Id))
      ((scheme e g₂).aggregateVerify (signers.map (fun p => (p.1 • g₂, p.2)))
        (signers.map (fun p => p.1 • H p.2)).sum) = (pure true : ProbComp Bool) := by
  have hId (a : Gₜ) : (liftM (m := Id) (a : Id Gₜ) : ProbComp Gₜ) = pure a := rfl
  simp [scheme, List.map_map, Function.comp_def, hd, unifFwdAnswerImpl,
    QueryImpl.simulateQ_add_liftM_right, simulateQ_pairingSum, pairing_sum_signatures, hId]

/-- Honest signing, aggregation, and verification accept with probability one under the
shared lazy random oracle, for any fixed list of secret keys and distinct messages. -/
theorem aggregate_correctness [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ] [DecidableEq M]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₂ : G₂)
    (signers : List (F × M)) (hd : (signers.map Prod.snd).Nodup) :
    (ProbCompRuntime.rom (M →ₒ G₁)).evalDist (do
      let sigs ← signers.mapM fun p => (scheme e g₂).sign (p.1 • g₂) p.1 p.2
      let σ ← (scheme (M := M) e g₂).aggregate sigs
      (scheme e g₂).aggregateVerify (signers.map (fun p => (p.1 • g₂, p.2))) σ) {true} = 1 := by
  rw [ProbCompRuntime.rom_evalDist]
  change 𝒟[(simulateQ (M →ₒ G₁).romImpl _).run' ∅] {b | b = true} = 1
  rw [evalDist_apply_setOf_simulateQ_romImpl_run'_eq_one_iff]
  intro f _
  have hId (a : G₁) : (liftM (m := Id) (a : Id G₁) : ProbComp G₁) = pure a := rfl
  have hs (ps : List (F × M)) :
      simulateQ (unifFwdAnswerImpl f)
        (ps.mapM fun p => (scheme e g₂).sign (p.1 • g₂) p.1 p.2) =
      (pure (ps.map fun p => p.1 • (f p.2).run) : ProbComp (List G₁)) := by
    induction ps with
    | nil => simp
    | cons p ps ih =>
      simp only [List.mapM_cons, simulateQ_bind, simulateQ_pure, ih]
      simp [scheme, unifFwdAnswerImpl, QueryImpl.simulateQ_add_liftM_query_right, hId, Id.run]
  simp only [simulateQ_bind, hs, pure_bind]
  change 𝒟[simulateQ (unifFwdAnswerImpl f)
    (pure (signers.map (fun p => p.1 • (f p.2).run)).sum >>= fun σ =>
      (scheme e g₂).aggregateVerify (signers.map (fun p => (p.1 • g₂, p.2))) σ)]
      {b | b = true} = 1
  simp only [pure_bind]
  have hv : simulateQ (unifFwdAnswerImpl f)
      ((scheme e g₂).aggregateVerify (signers.map (fun p => (p.1 • g₂, p.2)))
        (signers.map (fun p => p.1 • (f p.2).run)).sum) = (pure true : ProbComp Bool) :=
    aggregateVerify_honest e g₂ (fun m => (f m).run) signers hd
  rw [hv]
  simp

/-- Repeated messages are rejected before any verification hash query. -/
theorem aggregateVerify_eq_false_of_not_nodup [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ] [DecidableEq M]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₂ : G₂) (pairs : List (G₂ × M)) (σ : G₁)
    (hd : ¬(pairs.map Prod.snd).Nodup) :
    (scheme e g₂).aggregateVerify pairs σ = pure false := by
  simp [scheme, hd]

end BLS.Aggregate
