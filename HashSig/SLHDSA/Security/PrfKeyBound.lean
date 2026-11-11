/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.CoverageBound
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# The message-`PRF` key events

For SLH-DSA in the three-oracle random-oracle model (`romScheme`) at a fixed public seed, this
module joins two events about the message-`PRF` key `SK.prf` to the joint potential of
`HashSig.SLHDSA.Security.JointBound`, so that they are charged inside it and not added to it.
`RunPrfKeyHit toY k z` is their disjunction:

* `RunHmsgAtPrfKey toY z`: the final cache of the run holds an `H_msg` point whose randomizer is
  `SK.prf`, read as a node through an injective `toY : SK.prf → Y`. The forger, the signer and the
  verifier all cache `H_msg` points, so this covers a forger or verifier `H_msg` query at `SK.prf`
  and a signature whose randomizer is `SK.prf`;
* `z.1.sk.skPrf = k`: the key is a fixed value `k`.

Over a single byte-string oracle, a message-`PRF` input `SK.prf ‖ opt ‖ M` coincides with an
`H_msg` input `R ‖ PK.seed ‖ …` at `R = SK.prf` and `opt = PK.seed`, or with a tweakable-hash input
when `SK.prf = PK.seed`; at the SHAKE bundles `toY` is the identity and `k` is the public seed.

For a forger with hash budget `qh` and signing budget `qs`, under the key discipline and
`|Y| ≤ |SK.prf|`, the joint term becomes `(2 (qh + V) + qs + 1) / |Y|`, with `V` the verifier's
query bound, in the ideal hidden-seed game
(`prEvent_idealDraw_runTargetCollision_or_runHiddenHit_or_runPrfKeyHit_or_exists_isSome_le`), and
the run wins strongly or fires `RunPrfKeyHit` with probability at most
`securityBound vp.params |Y| 2 1 qh qs + (qs + 1) / |Y|`
(`prEvent_romSchemeRun_strongWins_or_runPrfKeyHit_le`).

The event transports along the landed chain of games to a hazard of the drawn secret seeds and the
final public cache of the deferred lab run (`hmsgAtPrfKey_or_eq_of_runPrfKeyHit`; no merge changes
an `H_msg` point), where the cached `H_msg` points are charged `1 / |Y|` each (`hmsgCharge`,
`prEvent_hmsgAtPrfKey_le`) and the fixed key `1 / |Y|`. The widened pathwise budget is
`2 a + b + h + 1 ≤ (a + b) + (a + b + h) + 1 ≤ 2 (qh + V) + qs + 1`, with `a` the public entries
at node keys, `b` the derivable public points and `h` the `H_msg` points: `a + b ≤ qh + V`
(`encard_keyEntries_add_encard_setOf_isDerivablePublicQuery_le`) and, the three kinds being
disjoint public points, `a + b + h ≤ qh + qs + V`, the public queries of the lab experiment
(`isQueryBoundP_labExperiment_public`). A forger or verifier `H_msg` point is inside the
`qh + V` share, a signer `H_msg` point inside the `qs` share, and the fixed key is the `+ 1`.

## Scope

* The statements are per public seed: the scheme is `romScheme core e optRand (pure pkSeed)`.
* `optRand` is arbitrary, so they cover hedged and deterministic signing.
* The single-oracle model itself, and the coupling relating it to the three-oracle model, are not
  here. Nothing here is quantum.
-/

public section

open OracleComp OracleSpec SignatureAlg MeasureTheory
open scoped ENNReal

namespace SLHDSA.Security

/-! ## The events -/

variable {vp : ValidatedParams} {core : CorePrimitives vp.params}

/-- A public `H_msg` point. -/
@[expose] def IsHmsgPoint : (hashSpec core).Domain → Prop
  | .inl (.hmsg _ _ _ _) => True
  | _ => False

/-- A public cache holds an `H_msg` point whose randomizer is the message-`PRF` key `k`, read as a
node through `toY`. -/
@[expose] def HmsgAtPrfKey (toY : core.SkPrf → core.Y) (k : core.SkPrf)
    (C : (hashSpec core).QueryCache) : Prop :=
  ∃ ps pr msg, (C (.inl (.hmsg (toY k) ps pr msg))).isSome

/-- The final cache of a run holds an `H_msg` point whose randomizer is the run's message-`PRF`
key `SK.prf`, read as a node through `toY`. -/
@[expose] def RunHmsgAtPrfKey (toY : core.SkPrf → core.Y)
    (z : RomOutcome vp core × (hashSpec core).QueryCache) : Prop :=
  HmsgAtPrfKey toY z.1.sk.skPrf z.2

/-- The message-`PRF` key of a run is hit: the final cache holds an `H_msg` point whose
randomizer is `SK.prf`, read as a node through `toY`, or `SK.prf` is the fixed key `k`. -/
@[expose] def RunPrfKeyHit (toY : core.SkPrf → core.Y) (k : core.SkPrf)
    (z : RomOutcome vp core × (hashSpec core).QueryCache) : Prop :=
  RunHmsgAtPrfKey toY z ∨ z.1.sk.skPrf = k

variable (core) in
/-- The `H_msg` charge of a public cache: its cached `H_msg` points, over `|Y|`. -/
@[expose] noncomputable def hmsgCharge (C : (hashSpec core).QueryCache) : ℝ≥0∞ :=
  ({t | (C t).isSome ∧ IsHmsgPoint t}.encard : ℝ≥0∞) / Nat.card core.Y

/-! ## Transport and charges -/

/-- On the transcript rebuilt with seeds `s` and the cache merged under `s` from the split state
of a lab state `st`, a hit of the message-`PRF` key is an `H_msg` point at `s.2` in the public
cache of `st`, or `s.2 = k`: neither merge changes an `H_msg` point, and the rebuilt key's
message-`PRF` key is `s.2`. -/
theorem hmsgAtPrfKey_or_eq_of_runPrfKeyHit (e : core.SkSeed ≃ core.Y) (pkSeed : core.PkSeed)
    (toY : core.SkPrf → core.Y) (k : core.SkPrf) (s : core.SkSeed × core.SkPrf)
    (o : DeriveOutcome core) (st : LabState core)
    (h : RunPrfKeyHit toY k (DeriveOutcome.fill core s o,
      (secretEncoding core e pkSeed).merge s ((slhGraph core pkSeed).toSplitCache st))) :
    HmsgAtPrfKey toY s.2 st.1 ∨ s.2 = k := by
  rw [RunPrfKeyHit, RunHmsgAtPrfKey, DeriveOutcome.fill, UnforgeableTranscript.mapSk_sk] at h
  refine h.imp_left fun ⟨ps, pr, msg, h⟩ ↦ ⟨ps, pr, msg, ?_⟩
  rw [(secretEncoding core e pkSeed).merge_apply_of_not_exists s _
    (by rintro ⟨x | ⟨o, m⟩, hx⟩ <;> cases hx)] at h
  rwa [CanonicalGraph.toSplitCache, CanonicalGraph.merge_apply_of_not_exists _
    (by rintro ⟨k, vs, -, hk⟩; cases hk)] at h

section Charges

variable [SampleableType core.SkSeed] [SampleableType core.SkPrf]

/-- **An `H_msg` point at the message-`PRF` key is charged by `hmsgCharge`.** Under uniform secret
seeds, for injective `toY` and `|Y| ≤ |SK.prf|`, a public cache holds an `H_msg` point whose
randomizer is the drawn message-`PRF` key with probability at most its cached `H_msg` points over
`|Y|`. -/
theorem prEvent_hmsgAtPrfKey_le {toY : core.SkPrf → core.Y} (htoY : Function.Injective toY)
    (hcard : Nat.card core.Y ≤ Nat.card core.SkPrf) (C : (hashSpec core).QueryCache) :
    Pr{let s ← $ᵗ (core.SkSeed × core.SkPrf)}[HmsgAtPrfKey toY s.2 C] ≤ hmsgCharge core C := by
  rw [hmsgCharge, ENNReal.div_eq_inv_mul]
  refine (prEvent_mono _ _
      (fun s ↦ ∃ t ∈ {t | (C t).isSome ∧ IsHmsgPoint t},
        ∃ ps pr msg, t = .inl (.hmsg (toY s.2) ps pr msg)) ?_).trans
    (prEvent_exists_mem_le_encard_mul _ _ _ fun t ht ↦ ?_)
  · rintro s ⟨ps, pr, msg, h⟩
    exact ⟨_, ⟨h, trivial⟩, ps, pr, msg, rfl⟩
  · rcases t with (_ | ⟨r, ps, pr, msg⟩) | _
    · exact ht.2.elim
    · refine SampleableType.prEvent_uniformSample_prod_le_of_forall_fst _ fun _ ↦ ?_
      calc _ ≤ Pr{let y ← $ᵗ core.SkPrf}[toY y = r] := prEvent_mono _ _ _ fun y ↦ by
            rintro ⟨_, _, _, h⟩
            simp only [Sum.inl.injEq, PublicHashQuery.hmsg.injEq] at h
            exact h.1.symm
        _ ≤ (Nat.card core.SkPrf : ℝ≥0∞)⁻¹ :=
            SampleableType.prEvent_uniformSample_apply_eq_le htoY r
        _ ≤ _ := ENNReal.inv_le_inv.2 (by exact_mod_cast hcard)
    · exact ht.2.elim

end Charges

/-! ## The budget -/

variable [SampleableType core.Y] [DecidableEq core.Y] [SampleableType core.SkSeed]
  [SampleableType core.SkPrf] [SampleableType (Bytes vp.params.m)] [DecidableEq core.PkSeed]
  [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf]

/-- **The budget with the `H_msg` charge.** Under key separation, on every run of the lab
experiment in the deferred game from the empty state, twice the public entries at node keys over
`|Y|`, plus the seed charge, the `H_msg` charge and `1 / |Y|`, is at most
`(2 (qh + V) + qs + 1) / |Y|` for a forger with hash budget `qh` and signing budget `qs`. -/
theorem two_mul_encard_keyEntries_div_add_seedCharge_add_hmsgCharge_le_of_mem_support
    (hsep : core.KeySeparated) {e : core.SkSeed ≃ core.Y}
    {optRand : PublicKeyCore core → ProbComp core.Y} {pkSeed : core.PkSeed}
    {adv : UnforgeableAdversary (romScheme core e optRand (pure pkSeed))} {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs)
    {z : DeriveOutcome core × LabState core × List (DeriveQuery core ⊕ NodeKey core)}
    (hz : z ∈ support ((simulateQ (slhGraph core pkSeed).deferredImpl
      (labExperiment core adv pkSeed)).run ((∅, ∅), []))) :
    2 * (((slhNodeKeys core pkSeed).keyEntries z.2.1.1).encard : ℝ≥0∞) / Nat.card core.Y +
        (seedCharge core pkSeed z.2.1.1 + (hmsgCharge core z.2.1.1 + (Nat.card core.Y : ℝ≥0∞)⁻¹)) ≤
      (2 * ((qh : ℝ≥0∞) + GeneralScheme.verifyInternalQueryBound vp.params) + qs + 1) /
        Nat.card core.Y := by
  set V := GeneralScheme.verifyInternalQueryBound vp.params
  set A := (slhNodeKeys core pkSeed).keyEntries z.2.1.1
  set B := {t | (z.2.1.1 t).isSome ∧ IsDerivablePublicQuery core pkSeed (.inl (.inr t))}
  set H := {t | (z.2.1.1 t).isSome ∧ IsHmsgPoint (core := core) t}
  have hABH : Disjoint (A ∪ B) H := by
    refine Set.disjoint_left.2 fun t ht ⟨_, hh⟩ => ?_
    rcases t with (_ | ⟨R, s, r, m⟩) | _
    · exact hh.elim
    · rcases ht with ⟨_, hk⟩ | ⟨_, hd⟩
      · rw [slhNodeKeys_node_eq_none_of_forall_ne_thash core (by simp)] at hk; cases hk
      · exact hd
    · exact hh.elim
  have h1 : A.encard + B.encard ≤ qh + V :=
    encard_keyEntries_add_encard_setOf_isDerivablePublicQuery_le hsep hadv hz
  have hpub : {t | (z.2.1.1 t).isSome}.encard ≤ qh + qs + V := by
    simpa using
      (slhGraph core pkSeed).encard_inter_setOf_isSome_le_add_of_mem_support_simulateQ_deferredImpl
        (D := Set.univ) (p := IsPublicLabQuery core) (fun _ _ => trivial)
        (isQueryBoundP_labExperiment_public pkSeed hadv) hz
  have h2 : A.encard + B.encard + H.encard ≤ qh + qs + V := by
    rw [← Set.encard_union_eq (disjoint_keyEntries_setOf_isDerivablePublicQuery hsep pkSeed _),
      ← Set.encard_union_eq hABH]
    exact (Set.encard_le_encard (by rintro t ((⟨hC, _⟩ | ⟨hC, _⟩) | ⟨hC, _⟩) <;> exact hC)).trans
      hpub
  have hR := ENat.toENNReal_le.2 (show 2 * A.encard + B.encard + H.encard ≤ 2 * (qh + V) + qs by
    calc 2 * A.encard + B.encard + H.encard
        ≤ 2 * A.encard + B.encard + H.encard + B.encard := le_self_add
      _ = (A.encard + B.encard) + (A.encard + B.encard + H.encard) := by ring
      _ ≤ (qh + V) + (qh + qs + V) := add_le_add h1 h2
      _ = 2 * (qh + V) + qs := by ring)
  push_cast at hR
  rw [seedCharge, hmsgCharge, inv_eq_one_div, ENNReal.div_add_div_same, ENNReal.div_add_div_same,
    ENNReal.div_add_div_same]
  refine ENNReal.div_le_div_right ?_ _
  calc 2 * (A.encard : ℝ≥0∞) + (B.encard + (H.encard + 1))
      = (2 * (A.encard : ℝ≥0∞) + B.encard + H.encard) + 1 := by ring
    _ ≤ _ := by gcongr

/-! ## The bounds -/

/-- **The joint bound with a hit of the message-`PRF` key, in the ideal hidden-seed game.** Under
the key discipline and `|Y| ≤ |SK.prf|`, for injective `toY`, a fixed key `k` and a forger with hash
budget `qh` and signing budget `qs`, `idealDraw` at public seed `pkSeed` fires, on the transcript
rebuilt with the drawn seeds and the cache merged under them, a same-key target collision, a
hidden-value hit or a hit of the message-`PRF` key (`RunPrfKeyHit`), or holds in its final public
cache a point encoding a derivation under the drawn seeds, with probability at most
`(2 (qh + V) + qs + 1) / |Y|`, with `V` the verifier's query bound. -/
theorem prEvent_idealDraw_runTargetCollision_or_runHiddenHit_or_runPrfKeyHit_or_exists_isSome_le
    (hd : core.KeyDiscipline vp) (hcard : Nat.card core.Y ≤ Nat.card core.SkPrf)
    (e : core.SkSeed ≃ core.Y) (optRand : PublicKeyCore core → ProbComp core.Y)
    (pkSeed : core.PkSeed) {toY : core.SkPrf → core.Y} (htoY : Function.Injective toY)
    (k : core.SkPrf) {adv : UnforgeableAdversary (romScheme core e optRand (pure pkSeed))}
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    Pr{let w ← idealDraw e optRand pkSeed adv}[
      ((RunTargetCollision core e (DeriveOutcome.fill core w.1 w.2.1,
          (secretEncoding core e pkSeed).merge w.1 w.2.2) ∨
        RunHiddenHit core e (DeriveOutcome.fill core w.1 w.2.1,
          (secretEncoding core e pkSeed).merge w.1 w.2.2)) ∨
        RunPrfKeyHit toY k (DeriveOutcome.fill core w.1 w.2.1,
          (secretEncoding core e pkSeed).merge w.1 w.2.2)) ∨
      ∃ x, (w.2.2.1 ((secretEncoding core e pkSeed).enc w.1 x)).isSome] ≤
    (2 * ((qh : ℝ≥0∞) + GeneralScheme.verifyInternalQueryBound vp.params) + qs + 1) /
      Nat.card core.Y :=
  prEvent_idealDraw_runTargetCollision_or_runHiddenHit_or_le_of_budget hd hcard e optRand pkSeed
    adv (fun s z ↦ RunPrfKeyHit toY k (DeriveOutcome.fill core s z.1,
      (secretEncoding core e pkSeed).merge s z.2)) (fun s C ↦ HmsgAtPrfKey toY s.2 C ∨ s.2 = k)
    (fun C ↦ hmsgCharge core C + (Nat.card core.Y : ℝ≥0∞)⁻¹)
    (fun _ _ h ↦ Or.inr (Or.inr (hmsgAtPrfKey_or_eq_of_runPrfKeyHit e pkSeed toY k _ _ _ h)))
    (fun C ↦ (prEvent_or_le _ _ _).trans <| add_le_add (prEvent_hmsgAtPrfKey_le htoY hcard C) <|
      SampleableType.prEvent_uniformSample_prod_le_of_forall_fst _ fun _ ↦ by
        rw [SampleableType.prEvent_uniformSample_eq_singleton_natCard]
        exact ENNReal.inv_le_inv.2 (by exact_mod_cast hcard))
    _ (div_natCard_ne_top (by simp [ENNReal.mul_eq_top]))
    fun _ hz ↦ two_mul_encard_keyEntries_div_add_seedCharge_add_hmsgCharge_le_of_mem_support
      hd.keySeparated hadv hz

/-- **The forging bound with a hit of the message-`PRF` key, per public seed.** Under the byte laws,
the key discipline and `|Y| ≤ |SK.prf|`, for injective `toY`, a fixed key `k` and a forger with hash
budget `qh` and signing budget `qs`, the run of SLH-DSA in the random-oracle model at public seed
`pkSeed` wins strongly or hits the message-`PRF` key (`RunPrfKeyHit`: an `H_msg` point at `SK.prf`,
or `SK.prf = k`) with probability at most `securityBound vp.params |Y| 2 1 qh qs + (qs + 1) / |Y|`.
The union is split after the first game hop, so the hit and a seed guess are charged once, inside
the joint term `(2 (qh + V) + qs + 1) / |Y|`. -/
theorem prEvent_romSchemeRun_strongWins_or_runPrfKeyHit_le (laws : core.ByteLaws)
    (hd : core.KeyDiscipline vp) (hcard : Nat.card core.Y ≤ Nat.card core.SkPrf)
    (e : core.SkSeed ≃ core.Y) (optRand : PublicKeyCore core → ProbComp core.Y)
    (pkSeed : core.PkSeed) {toY : core.SkPrf → core.Y} (htoY : Function.Injective toY)
    (k : core.SkPrf) {adv : UnforgeableAdversary (romScheme core e optRand (pure pkSeed))}
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    Pr{let z ← romSchemeRun core e optRand (pure pkSeed) adv}[
      z.1.strongWins = true ∨ RunPrfKeyHit toY k z] ≤
    securityBound vp.params (Nat.card core.Y) 2 1 qh qs + ((qs : ℝ≥0∞) + 1) / Nat.card core.Y := by
  refine (prEvent_romSchemeRun_strongWins_or_le_add laws e optRand pkSeed hadv _
    (prEvent_idealDraw_runTargetCollision_or_runHiddenHit_or_runPrfKeyHit_or_exists_isSome_le hd
      hcard e optRand pkSeed htoY k hadv)).trans (le_of_eq ?_)
  simp only [securityBound, ENNReal.div_eq_inv_mul]
  push_cast
  ring

end SLHDSA.Security
