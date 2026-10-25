/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.CryptoFoundations.SignatureAlg.RomQueryCount
import VCVio.OracleComp.QueryTracking.QueryBound.Simulation
import VCVio.EvalDist.ProbabilityBounds

/-!
# Canonical wire interfaces for signatures

Canonical decoding preserves exact returned-pair freshness. The adversary transformation
forwards ambient queries and translates each signing query once. Message encoding is fixed
by the interface; transporting security requires its injectivity.
-/

public section

open OracleSpec OracleComp

namespace SignatureAlg

/-- An exact parser for canonical encodings, with a value for unsuccessful reduction outputs.
The fallback is never used to accept a wire signature. -/
structure CanonicalEncoding (α β : Type) where
  /-- The canonical wire representation of a semantic value. -/
  encode : α → β
  /-- Parse the whole wire value, rejecting malformed or noncanonical input. -/
  decode : β → Option α
  /-- Parsing succeeds exactly on the canonical representation of its result. -/
  decode_eq_some_iff : ∀ b a, decode b = some a ↔ b = encode a
  /-- Candidate used by the reduction after a failed parse; it never bypasses wire rejection. -/
  fallback : α

namespace CanonicalEncoding

variable {α β : Type} (c : CanonicalEncoding α β)

@[simp] theorem decode_encode (a : α) : c.decode (c.encode a) = some a :=
  (c.decode_eq_some_iff _ _).2 rfl

/-- A total reader for the reduction's final candidate. -/
@[expose] def read (b : β) : α := (c.decode b).getD c.fallback

@[simp] theorem read_encode (a : α) : c.read (c.encode a) = a := by
  simp [read]

theorem encode_injective : Function.Injective c.encode := by
  intro a b h
  have := congrArg c.decode h
  simpa using this

end CanonicalEncoding

namespace Wire

variable {ι : Type} {spec : OracleSpec ι} {M E PK WPK SK S WS : Type}

/-- A scheme with fixed message encoding and strict public-key and signature parsers.
The signing oracle receives only challenger-generated public keys. -/
@[expose] def scheme (alg : SignatureAlg (OracleComp spec) M PK SK S)
    (message : E → M) (pk : CanonicalEncoding PK WPK) (sig : CanonicalEncoding S WS) :
    SignatureAlg (OracleComp spec) E WPK SK WS where
  keygen := (fun keys => (pk.encode keys.1, keys.2)) <$> alg.keygen
  sign key sk msg := sig.encode <$> alg.sign (pk.read key) sk (message msg)
  verify key msg raw := match pk.decode key, sig.decode raw with
    | some key, some s => alg.verify key (message msg) s
    | _, _ => pure false

/-- Malformed public keys are rejected without invoking the underlying verifier. -/
theorem scheme_verify_of_publicKey_decode_none
    (alg : SignatureAlg (OracleComp spec) M PK SK S) (message : E → M)
    (pk : CanonicalEncoding PK WPK) (sig : CanonicalEncoding S WS)
    (key : WPK) (msg : E) (raw : WS) (h : pk.decode key = none) :
    (scheme alg message pk sig).verify key msg raw = pure false := by
  simp [scheme, h]

/-- Malformed signatures are rejected without invoking the underlying verifier. -/
theorem scheme_verify_of_signature_decode_none
    (alg : SignatureAlg (OracleComp spec) M PK SK S) (message : E → M)
    (pk : CanonicalEncoding PK WPK) (sig : CanonicalEncoding S WS)
    (key : WPK) (msg : E) (raw : WS) (h : sig.decode raw = none) :
    (scheme alg message pk sig).verify key msg raw = pure false := by
  cases hp : pk.decode key <;> simp [scheme, hp, h]

/-- Interpreting ambient oracles commutes with the canonical wire wrapper. -/
theorem map_scheme {ι' : Type} {spec' : OracleSpec ι'}
    (alg : SignatureAlg (OracleComp spec) M PK SK S) (message : E → M)
    (pk : CanonicalEncoding PK WPK) (sig : CanonicalEncoding S WS)
    (handler : QueryImpl spec (OracleComp spec')) :
    (scheme alg message pk sig).map (simulateQ' handler) =
      scheme (alg.map (simulateQ' handler)) message pk sig := by
  apply SignatureAlg.ext
  · simp [scheme]
  · funext key sk msg
    simp [scheme]
  · funext key msg raw
    cases hp : pk.decode key <;> cases hs : sig.decode raw <;> simp [scheme, hp, hs]

/-- Signing-query translation; every ambient query is forwarded unchanged. -/
@[expose] def signingImpl (message : E → M) (sig : CanonicalEncoding S WS) :
    QueryImpl (spec + (E →ₒ WS)) (OracleComp (spec + (M →ₒ S)))
  | .inl t => (query (spec := spec + (M →ₒ S)) (.inl t) : OracleComp _ (spec.Range t))
  | .inr msg => sig.encode <$>
      (query (spec := spec + (M →ₒ S)) (.inr (message msg)) : OracleComp _ S)

/-- The named wire-to-structured strong-unforgeability reduction. -/
@[expose] def reduce (alg : SignatureAlg (OracleComp spec) M PK SK S)
    (message : E → M) (pk : CanonicalEncoding PK WPK) (sig : CanonicalEncoding S WS)
    (adv : StrongUnforgeableAdversary (scheme alg message pk sig)) :
    StrongUnforgeableAdversary alg where
  main key := (fun pair => (message pair.1, sig.read pair.2)) <$>
    simulateQ (signingImpl message sig) (adv.main (pk.encode key))

/-- Translate the structured signing log back to wire signatures. -/
@[expose] def decodeLog (message : E → M) (sig : CanonicalEncoding S WS)
    (log : QueryLog (E →ₒ WS)) : QueryLog (M →ₒ S) :=
  log.filterMap fun entry => (fun s => ⟨message entry.1, s⟩) <$> sig.decode entry.2

/-- The signing-oracle transcript commutes with canonical encoding. -/
theorem runWithSigningOracle_signingImpl
    (alg : SignatureAlg (OracleComp spec) M PK SK S)
    (message : E → M) (pk : CanonicalEncoding PK WPK) (sig : CanonicalEncoding S WS)
    (key : PK) (sk : SK) {α : Type} (oa : OracleComp (spec + (E →ₒ WS)) α) :
    alg.runWithSigningOracle key sk (simulateQ (signingImpl message sig) oa) =
      (fun z => (z.1, decodeLog message sig z.2)) <$>
        (scheme alg message pk sig).runWithSigningOracle (pk.encode key) sk oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [runWithSigningOracle, decodeLog]
  | query_bind t k ih =>
    simp only [runWithSigningOracle, signingOracle, scheme,
      CanonicalEncoding.read_encode, QueryImpl.passthrough_add, decodeLog] at ih
    cases t with
    | inl t =>
      simp [runWithSigningOracle, signingImpl, signingOracle, scheme, QueryImpl.passthrough_add,
        ih, decodeLog]
    | inr msg =>
      simp [runWithSigningOracle, signingImpl, signingOracle, scheme,
        QueryImpl.passthrough_add, ih, decodeLog]

/-- An accepted fresh wire pair gives a fresh structured pair, including for a second
signature on an already signed message. -/
theorem fresh_of_fresh (message : E → M) (hinj : Function.Injective message)
    (sig : CanonicalEncoding S WS) (log : QueryLog (E →ₒ WS))
    (msg : E) (raw : WS) (s : S) (hparse : sig.decode raw = some s)
    (hfresh : (⟨msg, raw⟩ : (_ : E) × WS) ∉ log) :
    (⟨message msg, s⟩ : (_ : M) × S) ∉ decodeLog message sig log := by
  intro hm
  obtain ⟨⟨m, r⟩, hw, hdec⟩ := List.mem_filterMap.mp hm
  cases hd : sig.decode r with
  | none => simp [hd] at hdec
  | some t =>
    change (fun s => (⟨message m, s⟩ : (_ : M) × S)) <$> sig.decode r = _ at hdec
    rw [hd] at hdec
    have heq := Option.some.inj hdec
    have hm := hinj (congrArg Sigma.fst heq)
    subst m
    have hs : t = s := by simpa using heq
    subst t
    have hr : r = raw := ((sig.decode_eq_some_iff _ _).mp hd).trans
      ((sig.decode_eq_some_iff _ _).mp hparse).symm
    subst r
    exact hfresh hw

/-- Translating signing queries preserves both ROM budgets, including repeated hash calls. -/
theorem romQueryBound_reduce {ιh : Type} {hs : OracleSpec ιh}
    (alg : SignatureAlg (OracleComp (unifSpec + hs)) M PK SK S)
    (message : E → M) (pk : CanonicalEncoding PK WPK) (sig : CanonicalEncoding S WS)
    (adv : StrongUnforgeableAdversary (scheme alg message pk sig)) {qh qs : ℕ}
    (h : adv.RomQueryBound qh qs) : (reduce alg message pk sig adv).RomQueryBound qh qs := by
  intro key
  obtain ⟨hh, hs⟩ := h (pk.encode key)
  constructor
  · simp only [StrongUnforgeableAdversary.toUnforgeableAdversary, reduce, isQueryBoundP_map_iff]
    apply hh.simulateQ_of_step
    · rintro ((_ | _) | _) ht <;> simp_all [IsHashQuery, signingImpl]
    · rintro ((_ | _) | _) ht <;> simp_all [IsHashQuery, signingImpl]
  · simp only [StrongUnforgeableAdversary.toUnforgeableAdversary, reduce, isQueryBoundP_map_iff]
    apply hs.simulateQ_of_step
    · rintro ((_ | _) | _) ht <;> simp_all [IsSignQuery, signingImpl]
    · rintro ((_ | _) | _) ht <;> simp_all [IsSignQuery, signingImpl]

/-- Mapping an adversary's output leaves its signing log unchanged. -/
theorem runWithSigningOracle_map
    (alg : SignatureAlg (OracleComp spec) M PK SK S) (key : PK) (sk : SK)
    {α β : Type} (f : α → β) (oa : OracleComp (spec + (M →ₒ S)) α) :
    alg.runWithSigningOracle key sk (f <$> oa) =
      (Prod.map f id) <$> alg.runWithSigningOracle key sk oa := by
  simp [runWithSigningOracle]
  rfl

open scoped Classical in
/-- The reduced experiment shares its entire key generation and signing stage with the
wire experiment, and checks the decoded candidate against the decoded returned-pair log. -/
theorem strongUnforgeableExperiment_reduce
    (alg : SignatureAlg (OracleComp spec) M PK SK S)
    (message : E → M) (pk : CanonicalEncoding PK WPK) (sig : CanonicalEncoding S WS)
    (adv : StrongUnforgeableAdversary (scheme alg message pk sig)) :
    strongUnforgeableExperiment (reduce alg message pk sig adv) = do
      let (key, sk) ← alg.keygen
      let ((msg, raw), log) ←
        (scheme alg message pk sig).runWithSigningOracle (pk.encode key) sk
          (adv.main (pk.encode key))
      let verified ← alg.verify key (message msg) (sig.read raw)
      return !signingLogContains (decodeLog message sig log) (message msg) (sig.read raw) &&
        verified := by
  simp only [strongUnforgeableExperiment, reduce, runWithSigningOracle_map,
    bind_map_left]
  simp only [runWithSigningOracle_signingImpl alg message pk sig, bind_map_left]
  rfl

open scoped Classical in
/-- Strong wire unforgeability is bounded by the named structured reduction under any
stateful probabilistic oracle interpretation. No extra hash or signing query is introduced. -/
theorem prEvent_strongUnforgeableExperiment_le
    (alg : SignatureAlg (OracleComp spec) M PK SK S)
    (message : E → M) (hinj : Function.Injective message)
    (pk : CanonicalEncoding PK WPK) (sig : CanonicalEncoding S WS)
    (adv : StrongUnforgeableAdversary (scheme alg message pk sig))
    {σ : Type} (so : QueryImpl spec (StateT σ ProbComp)) (state : σ) :
    Pr{let z ← (simulateQ so (strongUnforgeableExperiment adv)).run state}[z.1 = true] ≤
      Pr{let z ← (simulateQ so
        (strongUnforgeableExperiment (reduce alg message pk sig adv))).run state}[z.1 = true] := by
  classical
  rw [strongUnforgeableExperiment_reduce]
  simp only [strongUnforgeableExperiment, scheme, simulateQ_bind,
    StateT.run_bind, bind_map_left]
  apply prEvent_bind_mono_of_forall_le
  rintro ⟨⟨key, sk⟩, st⟩
  apply prEvent_bind_mono_of_forall_le
  rintro ⟨⟨⟨msg, raw⟩, log⟩, st'⟩
  simp only [CanonicalEncoding.decode_encode]
  cases hd : sig.decode raw with
  | none => simp [simulateQ_pure, StateT.run_pure]
  | some s =>
    have hr : sig.read raw = s := by simp [CanonicalEncoding.read, hd]
    simp only [hr]
    apply prEvent_bind_mono_of_forall_le
    rintro ⟨verified, st''⟩
    simp only [simulateQ_pure, StateT.run_pure, prEvent_pure, Bool.and_eq_true,
      Bool.not_eq_true', decide_eq_false_iff_not, signingLogContains]
    by_cases hf : (⟨msg, raw⟩ : (_ : E) × WS) ∈ log
    · simp [hf]
    · have ht := fresh_of_fresh message hinj sig log msg raw s hd hf
      simp [hf, ht]

/-- The wire game's strong forging advantage is at most that of its budget-preserving
structured reduction in the same random-oracle model. -/
theorem strongUnforgeableAdvantage_le {ιh : Type} {hs : OracleSpec ιh}
    [DecidableEq ιh] [∀ t, SampleableType (hs.Range t)]
    (alg : SignatureAlg (OracleComp (unifSpec + hs)) M PK SK S)
    (message : E → M) (hinj : Function.Injective message)
    (pk : CanonicalEncoding PK WPK) (sig : CanonicalEncoding S WS)
    (adv : StrongUnforgeableAdversary (scheme alg message pk sig)) :
    strongUnforgeableAdvantage (ProbCompRuntime.rom hs) adv ≤
      strongUnforgeableAdvantage (ProbCompRuntime.rom hs)
        (reduce alg message pk sig adv) := by
  let : MeasurableSpace (Bool × hs.QueryCache) := ⊤
  have h := prEvent_strongUnforgeableExperiment_le alg message hinj pk sig adv
    (romImpl hs) (∅ : hs.QueryCache)
  rw [SignatureAlg.strongUnforgeableAdvantage, SignatureAlg.strongUnforgeableAdvantage,
    ProbCompRuntime.rom_evalDist, ProbCompRuntime.rom_evalDist]
  simp only [StateT.run'_eq, evalDist_map_of_discrete,
    MeasureTheory.Measure.map_apply Measurable.of_discrete (measurableSet_singleton true)]
  simpa only [prEvent_eq_evalDist_of_discrete, Set.preimage, Set.mem_singleton_iff] using h

end Wire
end SignatureAlg
