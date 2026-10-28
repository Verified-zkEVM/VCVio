/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.Schemes.Schnorr.AGM.Representation
public import VCVio.OracleComp.QueryTracking.ProgrammingOracle

/-! # Single-pass Schnorr AGM reduction

The first live hash explanation is retained across repeated queries. Simulated signing
commitments have the known representation `z • g - c • pk`. Final extraction uses the
retained explanation, so changing the final output's coefficients cannot change the
exceptional challenge event.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction GroupModel.LinearFunctional

namespace Schnorr.AGM.Reduction

variable {F G M : Type}

/-- `none` marks a simulator-programmed signing entry. -/
structure Entry (F : Type) where
  /-- The challenge returned at this point. -/
  challenge : F
  /-- The first live explanation; absent for simulated signing entries. -/
  representation : Option (AffineForm F)

/-- Reduction state: chronological input representations, first-explanation cache, and failure
flags. -/
structure State (F G M : Type) [Field F] where
  /-- Affine representations of the chronological received basis. -/
  representations : List (AffineForm F) := initialRepresentations
  /-- Challenges annotated with the first live explanation. -/
  cache : M × G → Option (Entry F) := fun _ => none
  /-- Messages requested from the signing oracle. -/
  signed : List M := []
  /-- Whether a malformed request was observed. -/
  malformed : Bool := false
  /-- Whether a fresh challenge canceled its pre-query coefficient. -/
  bad : Bool := false

/-- Cached live hashes retain the point's representation and, until bad, an
invertible extraction denominator. Programmed entries belong to signed messages. -/
@[expose] def State.Valid [Field F] [AddCommGroup G] [Module F G] (g pk : G) (s : State F G M)
    : Prop :=
  ∀ key e, s.cache key = some e →
    match e.representation with
    | none => key.1 ∈ s.signed
    | some a => evalPoint a g pk = key.2 ∧ (s.bad = false → a.lin + e.challenge ≠ 0)

/-- The empty hash cache satisfies the extraction invariant. -/
theorem initial_valid [Field F] [AddCommGroup G] [Module F G] (g pk : G) : ({}
    : State F G M).Valid g pk := by
  intro key e h
  cases h


/-- Used only for a fresh point. The representation is already fixed when c is drawn. -/
@[expose] def record [Field F] [DecidableEq F] [DecidableEq G] [DecidableEq M] (s : State F G M)
    (key : M × G) (a : AffineForm F) (c : F) : State F G M :=
  { s with cache := Function.update s.cache key (some ⟨c, some a⟩)
           bad := s.bad || decide (a.lin + c = 0) }

/-- Recording a fresh explained hash point preserves the extraction invariant. -/
theorem record_valid [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]
    [DecidableEq M] (g pk : G) (s : State F G M) (hs : s.Valid g pk)
    (key : M × G) (a : AffineForm F) (ha : evalPoint a g pk = key.2) (c : F) :
    (record s key a c).Valid g pk := by
  intro key' e he
  by_cases hk : key' = key
  · subst key'
    simp only [record, Function.update_self, Option.some.injEq] at he
    subst e
    refine ⟨ha, ?_⟩
    simp [record]
  · have he' : s.cache key' = some e := by simpa [record, hk] using he
    have h := hs key' e he'
    cases hr : e.representation with
    | none => simpa only [hr, record] using h
    | some a' =>
        simp only [hr] at h ⊢
        refine ⟨h.1, fun hb => h.2 ?_⟩
        simpa [record] using (Bool.or_eq_false_iff.mp hb).1

/-- Program an annotated signing entry through VCVio's cache-preserving programming oracle.
The oracle's flag records a fresh programming operation, not a signing collision. -/
@[expose] def programEntry [DecidableEq G] [DecidableEq M]
    (cache : M × G → Option (Entry F)) (key : M × G) (entry : Entry F) :
    M × G → Option (Entry F) :=
  let so : QueryImpl (M × G →ₒ Entry F) Id := fun _ => pure entry
  let result := (so.withProgramming (fun _ => some entry) key).run
    (QueryCache.ofFn cache, false)
  result.2.1.toFn

/-- Programming keeps a previous entry and inserts the proposed entry only on a cache miss. -/
theorem programEntry_eq [DecidableEq G] [DecidableEq M]
    (cache : M × G → Option (Entry F)) (key : M × G) (entry : Entry F) :
    programEntry cache key entry = match cache key with
      | some _ => cache
      | none => Function.update cache key (some entry) := by
  unfold programEntry QueryImpl.withProgramming QueryImpl.withCachingAux
  cases hc : cache key <;> simp [StateT.run, StateT.mk, hc, QueryCache.cacheQuery] <;> rfl

/-- Signing collisions keep the previous entry, exactly as the managed FS simulator. -/
@[expose] def signedState [Field F] [AddCommGroup G] [Module F G] [DecidableEq G]
    [DecidableEq M] (s : State F G M) (g pk : G) (m : M) (c z : F) : State F G M :=
  let R := z • g - c • pk
  { s with
      representations := s.representations ++ [signingRepresentation c z]
      signed := s.signed ++ [m]
      cache := programEntry s.cache (m, R) ⟨c, none⟩ }

/-- Signing marks new entries with their signed message and preserves live hash explanations. -/
theorem signedState_valid [Field F] [AddCommGroup G] [Module F G] [DecidableEq G]
    [DecidableEq M] (g pk : G) (s : State F G M) (hs : s.Valid g pk)
    (m : M) (c z : F) : (signedState s g pk m c z).Valid g pk := by
  intro key e he
  by_cases hc : s.cache (m, z • g - c • pk) = none
  · by_cases hk : key = (m, z • g - c • pk)
    · subst key
      simp [signedState, programEntry_eq, hc] at he
      subst e
      simp [signedState]
    · have he' : s.cache key = some e := by simpa [signedState, programEntry_eq, hc, hk] using he
      have h := hs key e he'
      cases hr : e.representation with
      | none => simp only [hr] at h ⊢; exact List.mem_append_left _ h
      | some a => simpa only [hr, signedState] using h
  · cases hcache : s.cache (m, z • g - c • pk) with
    | none => exact (hc hcache).elim
    | some old =>
        have he' : s.cache key = some e := by simpa [signedState, programEntry_eq, hcache] using he
        have h := hs key e he'
        cases hr : e.representation with
        | none => simp only [hr] at h ⊢; exact List.mem_append_left _ h
        | some a => simpa only [hr, signedState] using h

/-- Signing appends exactly the simulated commitment to the represented input basis. -/
theorem signedState_basis [Field F] [AddCommGroup G] [Module F G] [DecidableEq G]
    [DecidableEq M] (g pk : G) (s : State F G M) (m : M) (c z : F) :
    representedBasis g pk (signedState s g pk m c z).representations =
      extend (representedBasis g pk s.representations)
        (signingReply (z • g - c • pk) z).groups := by
  funext t
  simp [signedState, representedBasis, extend, signingReply, evalPoint_signingRepresentation]


/-- Answer a hash consistently, fixing a first explanation before sampling its challenge. -/
@[expose] def read [Field F] [DecidableEq F] [DecidableEq G] [DecidableEq M] [SampleableType F]
    (key : M × G) (a : AffineForm F) : StateT (State F G M) ProbComp F :=
  fun s => match s.cache key with
    | some e => pure (e.challenge, s)
    | none => do
        let c ← $ᵗ F
        pure (c, record s key a c)

/-- Mark a malformed request permanently. -/
@[expose] def rejected [Field F] (s : State F G M) : State F G M := { s with malformed := true }

/-- Rejecting a request preserves the extraction invariant. -/
theorem rejected_valid [Field F] [AddCommGroup G] [Module F G] (g pk : G) (s : State F G M)
    (hs : s.Valid g pk) :
    (rejected s).Valid g pk := hs

/-- Simulate algebraic requests with uniform challenges and programmed signing commitments. -/
@[expose] def handler [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]
    [DecidableEq M] [SampleableType F] (g pk : G) :
    QueryImpl (explainedSpec F (Group G) (Request M) (Reply F M))
      (StateT (State F G M) ProbComp) := by
  intro ⟨⟨request, groups⟩, coefficients⟩
  cases request with
  | random n => exact fun s => do
      let v ← unifSpec.query n
      pure (⟨v, fun _ => []⟩, if groups () = [] then s else rejected s)
  | hash m => exact fun s =>
      match groups (), coefficients () with
      | [R], [coeff] => do
          let (c, t) ← (read (m, R) (flatten coeff s.representations)).run s
          pure (scalarReply c, t)
      | _, _ => pure (scalarReply (0 : F), rejected s)
  | sign m => exact fun s =>
      if groups () ≠ [] then pure (scalarReply (0 : F), rejected s)
      else
        do
        let c ← $ᵗ F
        let z ← $ᵗ F
        pure (signingReply (z • g - c • pk) z, signedState s g pk m c z)

/-- The success flag is retained for the probability comparison; extraction uses
the first cached representation, never a new coefficient chosen after hashing. -/
@[expose] def finish [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]
    [DecidableEq M] [SampleableType F] (g pk : G) (out : Explained F (M × F) (Group G)) :
    StateT (State F G M) ProbComp (Bool × F) := do
  match out.value.groups (), out.coefficients () with
  | [R], [coeff] =>
      let (m, z) := out.value.data
      let s ← get
      let c ← read (m, R) (flatten coeff s.representations)
      let s ← get
      let accepted := !s.malformed && decide (m ∉ s.signed ∧ z • g = R + c • pk)
      let solution := match s.cache (m, R) with
        | some ⟨_, some a⟩ => (z - a.const) / (a.lin + c)
        | _ => 0
      pure (accepted, solution)
  | _, _ => pure (false, 0)

/-- Execute the algebraic adversary once, then verify and extract using the retained hash
explanation. -/
@[expose] def run [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]
    [DecidableEq M] [SampleableType F] (g pk : G) (adv : Schnorr.AlgebraicAdversary F G M)
    : ProbComp ((Bool × F) × State F G M) :=
  (do
    let out ← simulateQ (handler g pk) (adv.main (initial g pk))
    finish g pk out).run {}

end Schnorr.AGM.Reduction

namespace Schnorr

/-- The single-pass Schnorr AGM solver for the existing discrete-log experiment. It simulates
signing without a secret key and extracts from the first explanation of the forgery's hash. -/
@[expose] def agmReduction {F G M : Type} [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] [DecidableEq M] [SampleableType F]
    (g : G) (A : AlgebraicAdversary F G M) : DiffieHellman.DLogAdversary F G :=
  fun _ pk => (fun result => result.1.2) <$> AGM.Reduction.run g pk A

end Schnorr
