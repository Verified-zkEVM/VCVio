/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.PrfKeyBound
public import VCVio.CryptoFoundations.SignatureAlg.SigningHazard

/-!
# The message-`PRF` key events under hedged signing

For SLH-DSA in the three-oracle random-oracle model (`romScheme`) at a fixed public seed, this
module bounds a refinement of the message-`PRF` key event `RunPrfKeyHit` of
`HashSig.SLHDSA.Security.PrfKeyBound` that uses the randomness of `opt_rand`.

Over a single byte-string oracle, a signer's `PRF_msg` string `SK.prf ‖ opt_rand ‖ M` is the
string of an `H_msg` query `R ‖ PK.seed ‖ …` only when `R = SK.prf` and `opt_rand = PK.seed`. The
event `RunPrfKeyClash toY k o z` records both halves: the final cache holds an `H_msg` point whose
randomizer is `SK.prf` (read through `toY`) together with a `PRF_msg` point keyed by `SK.prf`
whose `opt_rand` is `o` (`PrfMsgAt`), or `SK.prf` is the fixed key `k`. At the SHAKE bundles, `o`
and `k` are the public seed.

## The bound

If `optRand pk` equals `o` with probability at most `ε` at every public key, a forger with hash
budget `qh` and signing budget `qs` wins strongly or fires `RunPrfKeyClash` with probability at most

`securityBound vp.params |Y| 2 1 qh qs + 1 / |Y| + qs * ε * (qh + qs + 1) / |Y|`

(`prEvent_romSchemeRun_strongWins_or_runPrfKeyClash_le`). For a uniform `opt_rand`, `ε = 1 / |Y|`
and the last term is `qs (qh + qs + 1) / |Y|^2`, in place of the `qs / |Y|` that `RunPrfKeyHit`
costs for the signer's `H_msg` points in every signing mode.

## The argument

The event is moved to the ideal hidden-seed game `idealDraw` by the chain of games of
`prEvent_romSchemeRun_strongWins_or_le_add`. There the merged cache reads a `PRF_msg` point keyed by
the drawn key from the derivation table, so the event is a cached `H_msg` point at the drawn key
together with a randomizer derivation at `opt_rand = o` (`RandDerivedAt`), or the drawn key is `k`
(`hmsgAtPrfKey_and_randDerivedAt_or_eq_of_runPrfKeyClash`).

* The fixed key is a hazard of the drawn seeds, charged `1 / |Y|` inside the joint potential of
  `prEvent_idealDraw_runTargetCollision_or_runHiddenHit_or_le_of_budget`, whose budget becomes
  `(2 (qh + V) + 1) / |Y|`.
* The derivation at `o` depends on the ideal run only. Only signing makes randomizer derivations,
  one per signature at the `opt_rand` it has just drawn, so it occurs with probability at most
  `qs * ε` (`prEvent_idealRun_randDerivedAt_le`, through
  `SignatureAlg.prEvent_run_unforgeableTranscriptExperiment_le`).
* Given the run, the drawn key is independent of it and hits one of the at most `qh + qs + 1`
  cached `H_msg` points (`isQueryBoundP_unforgeableTranscriptExperiment_deriveAdversary_hmsg`)
  with probability at most `(qh + qs + 1) / |Y|` (`prEvent_hmsgAtPrfKey_le`). The product is
  `prEvent_idealDraw_hmsgAtPrfKey_and_randDerivedAt_le`.

## Scope

* The statements are per public seed: the scheme is `romScheme core e optRand (pure pkSeed)`.
* `optRand` is arbitrary up to the bound `ε` on `Pr[optRand pk = o]`. Deterministic signing has
  `opt_rand = PK.seed`, so `ε = 1` there and `RunPrfKeyHit` is the sharper statement.
* Nothing here is quantum.
-/

public section

open OracleComp OracleSpec SignatureAlg MeasureTheory
open scoped ENNReal

namespace SLHDSA.Security

variable {vp : ValidatedParams} {core : CorePrimitives vp.params}

/-! ## The events -/

/-- A public cache holds a `PRF_msg` point keyed by `k` whose `opt_rand` is `o`. -/
@[expose] def PrfMsgAt (k : core.SkPrf) (o : core.Y) (C : (hashSpec core).QueryCache) : Prop :=
  ∃ msg, (C (.inr ⟨k, o, msg⟩)).isSome

/-- The message-`PRF` key of a run is hit at `opt_rand = o`: the final cache holds an `H_msg`
point whose randomizer is `SK.prf`, read as a node through `toY`, together with a `PRF_msg` point
keyed by `SK.prf` whose `opt_rand` is `o`; or `SK.prf` is the fixed key `k`. -/
@[expose] def RunPrfKeyClash (toY : core.SkPrf → core.Y) (k : core.SkPrf) (o : core.Y)
    (z : RomOutcome vp core × (hashSpec core).QueryCache) : Prop :=
  (RunHmsgAtPrfKey toY z ∧ PrfMsgAt z.1.sk.skPrf o z.2) ∨ z.1.sk.skPrf = k

/-- A derivation table holds a randomizer derivation whose `opt_rand` is `o`. -/
@[expose] def RandDerivedAt (o : core.Y) (D : (DeriveQuery core →ₒ core.Y).QueryCache) : Prop :=
  ∃ msg, (D (.inr (o, msg))).isSome

/-- On the transcript rebuilt with seeds `s` and the cache merged under `s` from a split cache
`st`, a hit of the message-`PRF` key at `opt_rand = o` is an `H_msg` point at `s.2` in the public
cache of `st` together with a randomizer derivation at `o` in its table, or `s.2 = k`: no merge
changes an `H_msg` point, and the merged cache reads a `PRF_msg` point keyed by `s.2` from the
table. -/
theorem hmsgAtPrfKey_and_randDerivedAt_or_eq_of_runPrfKeyClash (e : core.SkSeed ≃ core.Y)
    (pkSeed : core.PkSeed) (toY : core.SkPrf → core.Y) (k : core.SkPrf) (o : core.Y)
    (s : core.SkSeed × core.SkPrf) (z : DeriveOutcome core)
    (st : SecretEncoding.SplitCache (hashSpec core) (DeriveQuery core) core.Y)
    (h : RunPrfKeyClash toY k o (DeriveOutcome.fill core s z,
      (secretEncoding core e pkSeed).merge s st)) :
    (HmsgAtPrfKey toY s.2 st.1 ∧ RandDerivedAt o st.2) ∨ s.2 = k := by
  rw [RunPrfKeyClash, RunHmsgAtPrfKey, DeriveOutcome.fill, UnforgeableTranscript.mapSk_sk] at h
  refine h.imp_left fun ⟨⟨ps, pr, msg, h₁⟩, msg', h₂⟩ ↦ ⟨⟨ps, pr, msg, ?_⟩, msg', ?_⟩
  · rwa [(secretEncoding core e pkSeed).merge_apply_of_not_exists s _
      (by rintro ⟨x | ⟨o, m⟩, hx⟩ <;> cases hx)] at h₁
  · change ((secretEncoding core e pkSeed).merge s st
      ((secretEncoding core e pkSeed).enc s (.inr (o, msg')))).isSome = true at h₂
    rwa [SecretEncoding.merge_apply_enc, Option.isSome_map] at h₂

/-! ## Randomizer derivations at a fixed `opt_rand` in the ideal game -/

section Ideal

variable {o : core.Y}

/-- A program making no randomizer derivation makes none at `opt_rand = o`. -/
theorem allQueriesSatisfy_ne_of_isQueryBoundP_isRandQuery {α : Type}
    {oa : OracleComp (deriveSpec core) α} (h : IsQueryBoundP oa (Coverage.IsRandQuery core) 0) :
    AllQueriesSatisfy oa fun t ↦ ∀ msg, t ≠ .inr (.inr (o, msg)) := by
  classical
  refine (isQueryBoundP_zero_iff oa _).1 (h.of_imp fun t ht ↦ ?_)
  push Not at ht
  obtain ⟨msg, rfl⟩ := ht
  trivial

variable [SampleableType core.Y] [DecidableEq core.Y]
  (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeed : core.PkSeed)

section Budget

variable [SampleableType core.SkSeed] [SampleableType core.SkPrf]

/-- **The `H_msg` budget of the secret-free experiment.** For a forger with hash budget `qh` and
signing budget `qs`, the secret-free experiment at public seed `pkSeed` makes at most
`qh + qs + 1` `H_msg` queries: at most one per forger hash query, one per signature, and one for
verification. -/
theorem isQueryBoundP_unforgeableTranscriptExperiment_deriveAdversary_hmsg
    {e : core.SkSeed ≃ core.Y}
    {adv : UnforgeableAdversary (romScheme core e optRand (pure pkSeed))} {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    IsQueryBoundP (unforgeableTranscriptExperiment (deriveAdversary core adv pkSeed))
      (Coverage.IsHmsgQuery core) (qh + qs + 1) := by
  rw [deriveAdversary]
  exact isQueryBoundP_unforgeableTranscriptExperiment_mapOracles_add _
    (fun pk ↦ (hadv pk).1.or (hadv pk).2)
    (fun _ _ ↦ (isQueryBoundP_query_iff _ _ _).2 fun _ ↦ Nat.one_pos)
    (fun | .inl _, _ => (isQueryBoundP_query_iff _ _ _).2 False.elim
         | .inr _, ht => (ht (Or.inl trivial)).elim)
    ((Coverage.isQueryBoundP_deriveScheme_keygen_hmsg_rand core optRand pkSeed).of_imp
      fun _ ↦ Or.inl)
    (fun pk sk msg _ ↦ Coverage.isQueryBoundP_deriveScheme_sign_hmsg core optRand pkSeed pk sk msg)
    (fun _ _ _ h ↦ (h (Or.inr trivial)).elim)
    (Coverage.isQueryBoundP_deriveScheme_verify_hmsg core optRand pkSeed)

end Budget

variable [SampleableType (Bytes vp.params.m)] [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey]
  [DecidableEq core.SkPrf]

/-- A step of the ideal game at a query that is not a randomizer derivation at `opt_rand = o`
draws no such derivation. -/
theorem not_randDerivedAt_of_mem_support_idealImpl {t : (deriveSpec core).Domain}
    (ht : ∀ msg, t ≠ .inr (.inr (o, msg)))
    {st : SecretEncoding.SplitCache (hashSpec core) (DeriveQuery core) core.Y}
    (hst : ¬RandDerivedAt o st.2) {w}
    (hw : w ∈ support ((SecretEncoding.idealImpl (hashSpec core) (DeriveQuery core) core.Y t).run
      st)) :
    ¬RandDerivedAt o w.2.2 := by
  rintro ⟨msg, h⟩
  rcases (SecretEncoding.isSome_snd_apply_iff_of_mem_support_idealImpl hw _).1 h with h | h
  exacts [hst ⟨msg, h⟩, ht msg h.symm]

/-- A run in the ideal game of a program that makes no randomizer derivation at `opt_rand = o`
draws none. -/
theorem not_randDerivedAt_of_mem_support_simulateQ_idealImpl {α : Type}
    {oa : OracleComp (deriveSpec core) α}
    (h : AllQueriesSatisfy oa fun t ↦ ∀ msg, t ≠ .inr (.inr (o, msg)))
    {st : SecretEncoding.SplitCache (hashSpec core) (DeriveQuery core) core.Y}
    (hst : ¬RandDerivedAt o st.2) {z}
    (hz : z ∈ support ((simulateQ (SecretEncoding.idealImpl (hashSpec core) (DeriveQuery core)
      core.Y) oa).run st)) :
    ¬RandDerivedAt o z.2.2 :=
  h.holds_of_mem_support_run_simulateQ (fun st ↦ ¬RandDerivedAt o st.2)
    (fun _ ht _ hs _ hw ↦ not_randDerivedAt_of_mem_support_idealImpl ht hs hw) hst hz

/-- **One signature draws a randomizer derivation at `opt_rand = o` with probability at most
`ε`.** If `optRand pk` is `o` with probability at most `ε`, a run of signing of the secret-free
scheme in the ideal game, from a state without such a derivation, ends with one with probability
at most `ε`: signing makes one randomizer derivation, at the `opt_rand` it has just drawn. -/
theorem prEvent_run_simulateQ_idealImpl_sign_le {ε : ℝ≥0∞}
    (hε : ∀ pk, Pr{let r ← optRand pk}[r = o] ≤ ε) (pk sk : PublicKeyCore core)
    (msg : List Byte) {st : SecretEncoding.SplitCache (hashSpec core) (DeriveQuery core) core.Y}
    (hst : ¬RandDerivedAt o st.2) :
    Pr{let z ← (simulateQ (SecretEncoding.idealImpl (hashSpec core) (DeriveQuery core) core.Y)
      ((deriveScheme core optRand pkSeed).sign pk sk msg)).run st}[RandDerivedAt o z.2.2] ≤ ε := by
  rw [Coverage.deriveScheme_sign_eq, simulateQ_bind, StateT.run_bind,
    SecretEncoding.run_simulateQ_idealImpl_liftM, bind_map_left]
  refine (prEvent_bind_le_prEvent_add_of_support (optRand pk) _ (· = o) _ (ε := 0)
    fun a _ ha ↦ (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz ↦
      not_randDerivedAt_of_mem_support_simulateQ_idealImpl ?_ hst hz).le).trans
    (by simpa using hε pk)
  refine (allQueriesSatisfy_query_bind_iff _ _ _).2 ⟨fun msg' h ↦ ha ?_, fun R ↦ ?_⟩
  · simp only [Sum.inr.injEq, Prod.mk.injEq] at h
    exact h.1
  · exact allQueriesSatisfy_ne_of_isQueryBoundP_isRandQuery (isQueryBoundP_bind (n := 0) (m := 0)
      ((isQueryBoundP_query_iff _ _ _).2 False.elim) fun _ _ ↦
        (Coverage.isQueryBoundP_signTail core _ _ _).of_imp fun _ ↦ Or.inr)

variable [SampleableType core.SkSeed] [SampleableType core.SkPrf]

/-- **The ideal run draws a randomizer derivation at `opt_rand = o` with probability at most
`qs * ε`.** If `optRand pk` is `o` with probability at most `ε` at every public key, then for a
forger with signing budget `qs` the secret-free experiment at public seed `pkSeed`, run in the
ideal game from the empty state, ends with a randomizer derivation at `opt_rand = o` with
probability at most `qs * ε`: only signing makes randomizer derivations, one per signature. -/
theorem prEvent_idealRun_randDerivedAt_le {ε : ℝ≥0∞}
    (hε : ∀ pk, Pr{let r ← optRand pk}[r = o] ≤ ε) {e : core.SkSeed ≃ core.Y}
    {adv : UnforgeableAdversary (romScheme core e optRand (pure pkSeed))} {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    Pr{let z ← (simulateQ (SecretEncoding.idealImpl (hashSpec core) (DeriveQuery core) core.Y)
      (unforgeableTranscriptExperiment (deriveAdversary core adv pkSeed))).run (∅, ∅)}[
      RandDerivedAt o z.2.2] ≤ qs * ε :=
  prEvent_run_unforgeableTranscriptExperiment_le _ (fun st ↦ RandDerivedAt o st.2)
    (allowed := fun t ↦ t.isLeft = true)
    (fun _ hz ↦ not_randDerivedAt_of_mem_support_simulateQ_idealImpl
      (allQueriesSatisfy_ne_of_isQueryBoundP_isRandQuery
        ((Coverage.isQueryBoundP_deriveScheme_keygen_hmsg_rand core optRand pkSeed).of_imp
          fun _ ↦ Or.inr))
      (by simp [RandDerivedAt]) hz)
    (fun t ht _ hs _ hw ↦ not_randDerivedAt_of_mem_support_idealImpl
      (by rcases t with t | x <;> simp_all) hs hw)
    (fun pk sk msg _ hs ↦ prEvent_run_simulateQ_idealImpl_sign_le optRand pkSeed hε pk sk msg hs)
    (fun pk msg sig _ hs _ hz ↦ not_randDerivedAt_of_mem_support_simulateQ_idealImpl
      (allQueriesSatisfy_ne_of_isQueryBoundP_isRandQuery
        (Coverage.isQueryBoundP_deriveScheme_verify_rand core optRand pkSeed pk msg sig)) hs hz)
    _ (Coverage.allQueriesSatisfy_deriveAdversary_main core adv pkSeed)
    (p := fun t ↦ t.isRight = true) (fun _ ↦ rfl) fun pk ↦ by
      rw [deriveAdversary]
      exact isQueryBoundP_mapOracles_main_isRight _ adv (fun _ ↦ trivial) pk (hadv pk).2

/-- On every run of the secret-free experiment in the ideal game from the empty state, the
`H_msg` charge of the final public cache is at most `(qh + qs + 1) / |Y|`. -/
theorem hmsgCharge_le_of_mem_support_idealRun {e : core.SkSeed ≃ core.Y}
    {adv : UnforgeableAdversary (romScheme core e optRand (pure pkSeed))} {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) {z}
    (hz : z ∈ support ((simulateQ (SecretEncoding.idealImpl (hashSpec core) (DeriveQuery core)
      core.Y) (unforgeableTranscriptExperiment (deriveAdversary core adv pkSeed))).run (∅, ∅))) :
    hmsgCharge core z.2.1 ≤ ((qh : ℝ≥0∞) + qs + 1) / Nat.card core.Y := by
  have h :=
    SecretEncoding.idealImpl_cachesOnlyQueryPoint.encard_inter_le_add_of_mem_support_simulateQ
      (D := {t | IsHmsgPoint (core := core) t}) (by
        rintro ((n | t) | x) k ht hk <;> cases ht
        rcases t with (_ | _) | _ <;> exact hk)
      (isQueryBoundP_unforgeableTranscriptExperiment_deriveAdversary_hmsg optRand pkSeed hadv) hz
  simp only [QueryCache.empty_apply, Option.isSome_none, Bool.false_eq_true, Set.ofPred_false,
    Set.inter_empty, Set.encard_empty, zero_add] at h
  rw [hmsgCharge, show {t | (z.2.1 t).isSome ∧ IsHmsgPoint t} =
    {t | IsHmsgPoint (core := core) t} ∩ {t | (z.2.1 t).isSome} from Set.ext fun _ ↦ and_comm]
  exact ENNReal.div_le_div_right (by exact_mod_cast h) _

end Ideal

/-! ## The bounds -/

variable [SampleableType core.Y] [DecidableEq core.Y] [SampleableType core.SkSeed]
  [SampleableType core.SkPrf] [SampleableType (Bytes vp.params.m)] [DecidableEq core.PkSeed]
  [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf]

/-- **The product bound in the ideal hidden-seed game.** For `|Y| ≤ |SK.prf|`, injective `toY`,
`optRand pk` equal to `o` with probability at most `ε` at every public key, and a forger with hash
budget `qh` and signing budget `qs`, `idealDraw` at public seed `pkSeed` holds an `H_msg` point at
the drawn message-`PRF` key in its final public cache together with a randomizer derivation at
`opt_rand = o` with probability at most `qs * ε * (qh + qs + 1) / |Y|`: the derivation depends on
the run only, with probability at most `qs * ε`, and given the run the drawn key, independent of
it, hits one of its at most `qh + qs + 1` `H_msg` points with probability at most
`(qh + qs + 1) / |Y|`. -/
theorem prEvent_idealDraw_hmsgAtPrfKey_and_randDerivedAt_le
    (hcard : Nat.card core.Y ≤ Nat.card core.SkPrf) (e : core.SkSeed ≃ core.Y)
    (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeed : core.PkSeed)
    {toY : core.SkPrf → core.Y} (htoY : Function.Injective toY) {o : core.Y} {ε : ℝ≥0∞}
    (hε : ∀ pk, Pr{let r ← optRand pk}[r = o] ≤ ε)
    {adv : UnforgeableAdversary (romScheme core e optRand (pure pkSeed))} {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    Pr{let w ← idealDraw e optRand pkSeed adv}[
      HmsgAtPrfKey toY w.1.2 w.2.2.1 ∧ RandDerivedAt o w.2.2.2] ≤
    qs * ε * (((qh : ℝ≥0∞) + qs + 1) / Nat.card core.Y) := by
  rw [prEvent_idealDraw_eq e optRand pkSeed adv
    fun s z ↦ HmsgAtPrfKey toY s.2 z.2.1 ∧ RandDerivedAt o z.2.2, prEvent_bind_map_swap]
  have key := prEvent_bind_le_prEvent_mul_of_forall_le_of_support
    ((simulateQ (SecretEncoding.idealImpl (hashSpec core) (DeriveQuery core) core.Y)
      (unforgeableTranscriptExperiment (deriveAdversary core adv pkSeed))).run (∅, ∅))
    (fun z ↦ (·, z) <$> ($ᵗ (core.SkSeed × core.SkPrf) : ProbComp _))
    (fun z ↦ RandDerivedAt o z.2.2)
    (fun y ↦ HmsgAtPrfKey toY y.1.2 y.2.2.1 ∧ RandDerivedAt o y.2.2.2)
    (ε := ((qh : ℝ≥0∞) + qs + 1) / Nat.card core.Y)
    (fun z hz _ ↦ by
      rw [prEvent_map]
      exact (prEvent_mono _ _ _ fun s h ↦ h.1).trans ((prEvent_hmsgAtPrfKey_le htoY hcard _).trans
        (hmsgCharge_le_of_mem_support_idealRun optRand pkSeed hadv hz)))
    (fun z _ hO ↦ by
      rw [prEvent_map]
      exact prEvent_eq_zero_of_forall_not _ _ fun _ h ↦ hO h.2)
  refine (le_of_eq ?_).trans (key.trans
    (mul_le_mul_left (prEvent_idealRun_randDerivedAt_le optRand pkSeed hε hadv) _))
  simp only [prEvent_norm]

/-- **The joint bound with a hedged hit of the message-`PRF` key, in the ideal hidden-seed game.**
Under the key discipline and `|Y| ≤ |SK.prf|`, for injective `toY`, a fixed key `k`, `optRand pk`
equal to `o` with probability at most `ε` at every public key, and a forger with hash budget `qh`
and signing budget `qs`, `idealDraw` at public seed `pkSeed` fires, on the transcript rebuilt with
the drawn seeds and the cache merged under them, a same-key target collision, a hidden-value hit
or a hit of the message-`PRF` key at `opt_rand = o` (`RunPrfKeyClash`), or holds in its final
public cache a point encoding a derivation under the drawn seeds, with probability at most
`(2 (qh + V) + 1) / |Y| + qs * ε * (qh + qs + 1) / |Y|`, with `V` the verifier's query bound. The
fixed key is charged inside the joint potential, and the `H_msg` point with the derivation at `o`
by the product bound. -/
theorem prEvent_idealDraw_runTargetCollision_or_runHiddenHit_or_runPrfKeyClash_or_exists_isSome_le
    (hd : core.KeyDiscipline vp) (hcard : Nat.card core.Y ≤ Nat.card core.SkPrf)
    (e : core.SkSeed ≃ core.Y) (optRand : PublicKeyCore core → ProbComp core.Y)
    (pkSeed : core.PkSeed) {toY : core.SkPrf → core.Y} (htoY : Function.Injective toY)
    (k : core.SkPrf) {o : core.Y} {ε : ℝ≥0∞} (hε : ∀ pk, Pr{let r ← optRand pk}[r = o] ≤ ε)
    {adv : UnforgeableAdversary (romScheme core e optRand (pure pkSeed))} {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    Pr{let w ← idealDraw e optRand pkSeed adv}[
      ((RunTargetCollision core e (DeriveOutcome.fill core w.1 w.2.1,
          (secretEncoding core e pkSeed).merge w.1 w.2.2) ∨
        RunHiddenHit core e (DeriveOutcome.fill core w.1 w.2.1,
          (secretEncoding core e pkSeed).merge w.1 w.2.2)) ∨
        RunPrfKeyClash toY k o (DeriveOutcome.fill core w.1 w.2.1,
          (secretEncoding core e pkSeed).merge w.1 w.2.2)) ∨
      ∃ x, (w.2.2.1 ((secretEncoding core e pkSeed).enc w.1 x)).isSome] ≤
    (2 * ((qh : ℝ≥0∞) + GeneralScheme.verifyInternalQueryBound vp.params) + 1) /
        Nat.card core.Y + qs * ε * (((qh : ℝ≥0∞) + qs + 1) / Nat.card core.Y) := by
  set E := secretEncoding core e pkSeed
  refine (prEvent_mono _ _ (fun w ↦ ((((RunTargetCollision core e
      (DeriveOutcome.fill core w.1 w.2.1, E.merge w.1 w.2.2) ∨
      RunHiddenHit core e (DeriveOutcome.fill core w.1 w.2.1, E.merge w.1 w.2.2)) ∨
      w.1.2 = k) ∨ ∃ x, (w.2.2.1 (E.enc w.1 x)).isSome) ∨
      (HmsgAtPrfKey toY w.1.2 w.2.2.1 ∧ RandDerivedAt o w.2.2.2))) fun w h ↦ ?_).trans
    ((prEvent_or_le _ _ _).trans (add_le_add ?_
      (prEvent_idealDraw_hmsgAtPrfKey_and_randDerivedAt_le hcard e optRand pkSeed htoY hε hadv)))
  · rcases h with (h | h) | h
    · exact Or.inl (Or.inl (Or.inl h))
    · rcases hmsgAtPrfKey_and_randDerivedAt_or_eq_of_runPrfKeyClash e pkSeed toY k o w.1 w.2.1
        w.2.2 h with h | h
      exacts [Or.inr h, Or.inl (Or.inl (Or.inr h))]
    · exact Or.inl (Or.inr h)
  · refine prEvent_idealDraw_runTargetCollision_or_runHiddenHit_or_le_of_budget hd hcard e optRand
      pkSeed adv (fun s _ ↦ s.2 = k) (fun s _ ↦ s.2 = k) (fun _ ↦ (Nat.card core.Y : ℝ≥0∞)⁻¹)
      (fun _ _ h ↦ Or.inr (Or.inr h))
      (fun _ ↦ SampleableType.prEvent_uniformSample_prod_le_of_forall_fst _ fun _ ↦ by
        rw [SampleableType.prEvent_uniformSample_eq_singleton_natCard]
        exact ENNReal.inv_le_inv.2 (by exact_mod_cast hcard))
      _ (div_natCard_ne_top (by simp [ENNReal.mul_eq_top])) fun _ hz ↦ ?_
    rw [← add_assoc, ENNReal.add_div, inv_eq_one_div]
    exact add_le_add_left
      (two_mul_encard_keyEntries_div_add_seedCharge_le_of_mem_support hd.keySeparated hadv hz) _

/-- **The forging bound with a hedged hit of the message-`PRF` key, per public seed.** Under the
byte laws, the key discipline and `|Y| ≤ |SK.prf|`, for injective `toY`, a fixed key `k`, `optRand
pk` equal to `o` with probability at most `ε` at every public key, and a forger with hash budget
`qh` and signing budget `qs`, the run of SLH-DSA in the random-oracle model at public seed `pkSeed`
wins strongly or hits the message-`PRF` key at `opt_rand = o` (`RunPrfKeyClash`) with probability at
most `securityBound vp.params |Y| 2 1 qh qs + 1 / |Y| + qs * ε * (qh + qs + 1) / |Y|`. -/
theorem prEvent_romSchemeRun_strongWins_or_runPrfKeyClash_le (laws : core.ByteLaws)
    (hd : core.KeyDiscipline vp) (hcard : Nat.card core.Y ≤ Nat.card core.SkPrf)
    (e : core.SkSeed ≃ core.Y) (optRand : PublicKeyCore core → ProbComp core.Y)
    (pkSeed : core.PkSeed) {toY : core.SkPrf → core.Y} (htoY : Function.Injective toY)
    (k : core.SkPrf) {o : core.Y} {ε : ℝ≥0∞} (hε : ∀ pk, Pr{let r ← optRand pk}[r = o] ≤ ε)
    {adv : UnforgeableAdversary (romScheme core e optRand (pure pkSeed))} {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    Pr{let z ← romSchemeRun core e optRand (pure pkSeed) adv}[
      z.1.strongWins = true ∨ RunPrfKeyClash toY k o z] ≤
    securityBound vp.params (Nat.card core.Y) 2 1 qh qs + 1 / Nat.card core.Y +
      qs * ε * (((qh : ℝ≥0∞) + qs + 1) / Nat.card core.Y) := by
  refine (prEvent_romSchemeRun_strongWins_or_le_add laws e optRand pkSeed hadv _
    (prEvent_idealDraw_runTargetCollision_or_runHiddenHit_or_runPrfKeyClash_or_exists_isSome_le hd
      hcard e optRand pkSeed htoY k hε hadv)).trans (le_of_eq ?_)
  simp only [securityBound, ENNReal.div_eq_inv_mul]
  push_cast
  ring

end SLHDSA.Security
