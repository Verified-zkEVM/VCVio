/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.CryptoFoundations.SignatureAlg.Routed

/-!
# Routed adversaries on a toy encoding

One typed family `ℕ →ₒ Bool` is encoded into one random oracle `ℕ →ₒ Bool` at a shift read off
the public key: under the public key `n`, the typed point `t` is the raw input `t + n`, and raw
inputs below `n` are no typed point. A toy scheme signs a message by its typed hash, and a forger
over the single oracle reads the raw input encoding the typed point `5` under its public key.

* The routed forger keeps the forger's budget of one hash query and no signing query.
* Under the public key `3`, the raw input `8` is the typed point `5`, and the router answers the
  raw input `1` from its table alone, without a typed query.
* In the typed world, the experiment against the forger is the experiment against the forger
  holding the router, in the random oracle model of the typed family.
* The encoding is injective, so no clash occurs, and the forger's success in the random oracle
  model of the single oracle is at most the routed forger's success in the random oracle model
  of the typed family.
* When the public key pairs the shift with a uniform bit, key generation has two possible public
  keys; the encoding read off the shift is the same at both, and the same bound holds with the
  router read off the public key.
-/

public section

open OracleComp OracleSpec SignatureAlg

namespace VCVioTest.SignatureAlgRouted

/-- One typed family with one-bit answers. -/
abbrev spec : OracleSpec ℕ := ℕ →ₒ Bool

/-- The typed point `t` encoded as the raw input `t + n`; a raw input below `n` is no typed
point. -/
noncomputable def shifted (n : ℕ) : RandomOracleEncoding spec ℕ Bool :=
  .ofSplit (Tail := fun _ => Unit) (· + n) (fun x => if n ≤ x then some (x - n) else none)
    (by
      intro x t h
      split_ifs at h with hx
      cases h
      omega)
    (fun t => by simp)
    (fun _ => (Equiv.prodPUnit Bool).symm)

/-- The toy scheme: the public key is `3`, a signature is the typed hash of the message, and
verification compares it with the typed hash. -/
noncomputable def hashSigAlg : SignatureAlg (OracleComp (unifSpec + spec)) ℕ ℕ Unit Bool where
  keygen := pure (3, ())
  sign _ _ m := (unifSpec + spec).query (.inr m)
  verify _ m σ := (fun b => b == σ) <$> (unifSpec + spec).query (.inr m)

/-- The toy scheme over the single oracle, with typed hashes encoded under the public key `3`. -/
noncomputable abbrev byteSigAlg :=
  hashSigAlg.map (simulateQ' ((shifted 3).encodeImpl ∘ₛ liftTypedImpl))

/-- The forger reads the raw input encoding the typed point `5` under its public key and outputs
the answer as a signature of `5`. -/
noncomputable def rawAdv : UnforgeableAdversary byteSigAlg where
  main pk := do
    let b ← ((unifSpec + (ℕ →ₒ Bool)) + (ℕ →ₒ Bool)).query (.inl (.inr (pk + 5)))
    return (5, b)

/-- The forger read on the common interface. -/
noncomputable abbrev commonAdv :
    UnforgeableAdversary (hashSigAlg.map (simulateQ' (liftTypedImpl (ext := ℕ →ₒ Bool)))) :=
  rawAdv.mapOracles liftRawImpl

/-- The routed forger: the forger on the common interface, with its raw queries routed by the
encoding at its public key. -/
noncomputable abbrev routedAdv : UnforgeableAdversary hashSigAlg :=
  commonAdv.route (fun pk => (shifted pk).tableRouter) ∅

theorem rawAdv_romQueryBound : rawAdv.RomQueryBound 1 0 := fun pk => by
  constructor <;> simp [rawAdv, IsHashQuery, IsSignQuery]

/-- The routed forger keeps the forger's budget. -/
example : routedAdv.RomQueryBound 1 0 :=
  RandomOracleEncoding.romQueryBound_route_tableRouter rawAdv_romQueryBound ∅

/-- Under the public key `3`, the raw input `8` is the typed point `5`. -/
example : (shifted 3).route 8 = some 5 := rfl

/-- Under the public key `3`, the raw input `1` is answered from the router's table alone. -/
example : IsQueryBoundP (((shifted 3).tableRouter 1).run ∅) (fun t => t.isRight) 0 :=
  RandomOracleEncoding.isQueryBoundP_run_tableRouter_of_route_eq_none rfl ∅

/-- In the typed world of the encoding under the public key `3`, the experiment against the forger
read on the common interface is the experiment against the forger holding the router under `3`
in the random oracle model of the typed family. -/
example (c : spec.QueryCache) :
    Prod.map id Prod.fst <$>
        (simulateQ (shifted 3).typedImpl (unforgeableTranscriptExperiment commonAdv)).run (c, ∅) =
      (simulateQ spec.romImpl (unforgeableTranscriptExperiment (commonAdv.route
        (sigAlg := hashSigAlg) (fun _ => (shifted 3).tableRouter) ∅))).run c :=
  RandomOracleEncoding.map_run_simulateQ_typedImpl_unforgeableTranscriptExperiment _ _ c ∅

/-- The shifted encoding is injective, so no typed cache has a clash. -/
theorem not_clash (n : ℕ) (c : spec.QueryCache) : ¬(shifted n).Clash c := by
  rintro ⟨q, q', hne, -, -, he⟩
  exact hne (by simpa [shifted, RandomOracleEncoding.ofSplit] using he)

/-- The forger's success over the single oracle is at most the routed forger's success over the
typed family. -/
example : Pr{let z ← (simulateQ (ℕ →ₒ Bool).romImpl
      (unforgeableTranscriptExperiment rawAdv)).run ∅}[z.1.wins = true] ≤
    Pr{let z ← (simulateQ spec.romImpl
      (unforgeableTranscriptExperiment routedAdv)).run ∅}[z.1.wins = true] := by
  refine ((shifted 3).prEvent_simulateQ_romImpl_run_unforgeableTranscriptExperiment_le
    rawAdv (Ek := shifted) (fun z hz => ?_) (fun z => z.wins = true)).trans (le_of_eq ?_)
  · simp only [hashSigAlg, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
  · exact prEvent_congr _ _ _ fun z => or_iff_left (not_clash 3 z.2)

/-! ## A public key with a random part -/

/-- A scheme whose public key pairs the shift `3` with a uniform bit, so that key generation has
two possible public keys. -/
noncomputable def twoKeySigAlg :
    SignatureAlg (OracleComp (unifSpec + spec)) ℕ (ℕ × Bool) Unit Bool where
  keygen := do
    let b ← (liftM ($ᵗ Bool : ProbComp Bool) : OracleComp (unifSpec + spec) Bool)
    return ((3, b), ())
  sign _ _ m := (unifSpec + spec).query (.inr m)
  verify _ m σ := (fun b => b == σ) <$> (unifSpec + spec).query (.inr m)

/-- The forger over the single oracle reads the raw input encoding the typed point `5` under the
shift of its public key. -/
noncomputable def twoKeyRawAdv :
    UnforgeableAdversary (twoKeySigAlg.map (simulateQ' ((shifted 3).encodeImpl ∘ₛ liftTypedImpl)))
    where
  main pk := do
    let b ← ((unifSpec + (ℕ →ₒ Bool)) + (ℕ →ₒ Bool)).query (.inl (.inr (pk.1 + 5)))
    return (5, b)

/-- Every public key the key generation can output has shift `3`, whichever bit it draws, so the
encoding read off the public key is the encoding at `3`. -/
theorem shifted_fst_of_mem_support_keygen :
    ∀ z ∈ support twoKeySigAlg.keygen, shifted z.1.1 = shifted 3 := by
  intro z hz
  simp only [twoKeySigAlg, support_bind, support_pure, Set.mem_iUnion,
    Set.mem_singleton_iff] at hz
  obtain ⟨b, -, rfl⟩ := hz
  rfl

/-- With two possible public keys, the forger's success over the single oracle is at most the
success of the forger holding the router read off the shift of its public key. -/
example : Pr{let z ← (simulateQ (ℕ →ₒ Bool).romImpl
      (unforgeableTranscriptExperiment twoKeyRawAdv)).run ∅}[z.1.wins = true] ≤
    Pr{let z ← (simulateQ spec.romImpl (unforgeableTranscriptExperiment
      ((twoKeyRawAdv.mapOracles liftRawImpl
        (sigAlg' := twoKeySigAlg.map (simulateQ' liftTypedImpl))).route
        (sigAlg := twoKeySigAlg) (fun pk => (shifted pk.1).tableRouter) ∅))).run ∅}[
        z.1.wins = true] := by
  refine ((shifted 3).prEvent_simulateQ_romImpl_run_unforgeableTranscriptExperiment_le
    twoKeyRawAdv (Ek := fun pk => shifted pk.1) shifted_fst_of_mem_support_keygen
    (fun z => z.wins = true)).trans (le_of_eq ?_)
  exact prEvent_congr _ _ _ fun z => or_iff_left (not_clash 3 z.2)

end VCVioTest.SignatureAlgRouted
