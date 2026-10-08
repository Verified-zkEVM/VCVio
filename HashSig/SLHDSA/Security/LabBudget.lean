/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.LabScheme
public import HashSig.SLHDSA.Security.SeedCouplingBound
public import VCVio.OracleComp.QueryTracking.RandomOracle.Defer
import HashSig.SLHDSA.GeneralSchemeQueryBound

/-!
# The query budget of the lab experiment

The lab experiment `labExperiment core adv pkSeed` runs in the deferred game of the canonical
graph `slhGraph core pkSeed` (`CanonicalGraph.deferredImpl`). Two kinds of public entries of its
final cache are charged at `1 / |Y|` each by the joint potential and the hidden-seed bound:

* entries at node keys (`CanonicalGraph.NodeKeys.keyEntries` of `slhNodeKeys core pkSeed`), each
  charged twice, once for a conflict and once for a target collision;
* cached derivable public points (`IsDerivablePublicQuery`), charged once by `seedCharge`, the
  bound of `prEvent_exists_isSome_apply_secretEncoding_enc_le_seedCharge`.

A *charged point* (`IsChargedPoint`) is a public point of either kind. The deferred game caches
only the point of a public query, so the charged entries of every run are at most its charged
queries (`CanonicalGraph.encard_inter_setOf_isSome_le_add_of_mem_support_simulateQ_deferredImpl`).
The lab experiment makes at most `qh + V` of them (`isQueryBoundP_labExperiment`), where `qh` is
the forger's hash budget and `V = GeneralScheme.verifyInternalQueryBound`:

* lab key generation touches and reads cells and makes no public query
  (`isQueryBoundP_labScheme_keygen`);
* lab signing draws its randomizer as a derivation, touches and reads cells, and makes one public
  query, `H_msg`, which is neither at a node key nor derivable (`isQueryBoundP_labScheme_sign`);
* each forger hash query is one query, and verification makes at most `V` queries
  (`isQueryBoundP_labScheme_verify`).

Under key separation no point at a node key is derivable, so the two kinds are disjoint and
`2 a + b ≤ 2 (a + b) ≤ 2 (qh + V)` (`two_mul_encard_keyEntries_div_add_seedCharge_le`). This is
the pathwise budget of `CanonicalGraph.NodeKeys.prEvent_deferredFillDraw_le_of_budget`, with the
hazard charge `seedCharge core pkSeed`.
-/

public section

open OracleComp OracleSpec SignatureAlg
open scoped ENNReal

namespace SLHDSA.Security

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

/-! ## Charged points -/

/-- A public point charged at public seed `pkSeed`: a point at a node key
(`slhNodeKeys core pkSeed`) or a derivable public point (`IsDerivablePublicQuery`). -/
def IsChargedPoint (pkSeed : core.PkSeed) (t : (hashSpec core).Domain) : Prop :=
  ((slhNodeKeys core pkSeed).node t).isSome ∨ IsDerivablePublicQuery core pkSeed (.inl (.inr t))

/-- A query of a lab program at a charged public point. -/
def IsChargedLabQuery (pkSeed : core.PkSeed) : (labSpec core).Domain → Prop
  | .inl (.inl (.inr t)) => IsChargedPoint core pkSeed t
  | _ => False

/-- Charged lab queries are decided classically. -/
noncomputable instance instDecidablePredIsChargedLabQuery (pkSeed : core.PkSeed) :
    DecidablePred (IsChargedLabQuery core pkSeed) :=
  fun _ => Classical.dec _

/-- The seed charge of a public cache at public seed `pkSeed`: its cached derivable public points,
over `|Y|`. -/
noncomputable def seedCharge (pkSeed : core.PkSeed) (C : (hashSpec core).QueryCache) : ℝ≥0∞ :=
  ({t | (C t).isSome ∧ IsDerivablePublicQuery core pkSeed (.inl (.inr t))}.encard : ℝ≥0∞) /
    Nat.card core.Y

variable {core}

/-- Under uniform secret seeds, a public cache holds a point encoding a derivation with
probability at most its seed charge, when `|Y| ≤ |SK.prf|`. -/
theorem prEvent_exists_isSome_apply_secretEncoding_enc_le_seedCharge [SampleableType core.SkSeed]
    [SampleableType core.SkPrf] (e : core.SkSeed ≃ core.Y) (pkSeed : core.PkSeed)
    (hcard : Nat.card core.Y ≤ Nat.card core.SkPrf) (C : (hashSpec core).QueryCache) :
    Pr{let s ← $ᵗ (core.SkSeed × core.SkPrf)}[
      ∃ x, (C ((secretEncoding core e pkSeed).enc s x)).isSome] ≤ seedCharge core pkSeed C :=
  prEvent_exists_isSome_apply_secretEncoding_enc_le e pkSeed hcard C

/-! ## The lab experiment makes at most `qh + V` charged queries -/

variable [SampleableType core.Y] (pkSeed : core.PkSeed)

/-- Lab key generation makes no charged query: it only touches and reads cells. -/
theorem isQueryBoundP_labKeygen :
    IsQueryBoundP (labKeygen core) (IsChargedLabQuery core pkSeed) 0 :=
  labKeygen_pred core (Q := (IsQueryBoundP · (IsChargedLabQuery core pkSeed) 0))
    (isQueryBoundP_pure _ · 0)
    (fun _ _ h h' => isQueryBoundP_bind h fun x _ => h' x)
    (fun _ => (isQueryBoundP_query_iff _ _ _).2 False.elim)
    (fun | .inl _ | .inr _ => (isQueryBoundP_query_iff _ _ _).2 False.elim)

/-- Lab signing makes no charged query: besides touches and reads of cells, its only query is
`H_msg`, at no node key and not derivable. -/
theorem isQueryBoundP_labSignInternal (msg : List Byte) (pkRoot R : core.Y) :
    IsQueryBoundP (labSignInternal core pkSeed msg pkRoot R) (IsChargedLabQuery core pkSeed) 0 :=
  labSignInternal_pred core (Q := (IsQueryBoundP · (IsChargedLabQuery core pkSeed) 0))
    (isQueryBoundP_pure _ · 0)
    (fun _ _ h h' => isQueryBoundP_bind h fun x _ => h' x)
    (fun _ => (isQueryBoundP_query_iff _ _ _).2 False.elim)
    (fun | .inl _ | .inr _ => (isQueryBoundP_query_iff _ _ _).2 False.elim) _ _ _ _
    ((isQueryBoundP_query_iff _ _ _).2 fun h => by
      change IsChargedPoint core pkSeed (.inl (.hmsg R pkSeed pkRoot msg)) at h
      rcases h with h | h
      · rw [slhNodeKeys_node_eq_none_of_forall_ne_thash core (by simp)] at h
        exact absurd h (by simp)
      · exact h.elim)

variable [DecidableEq core.Y] (optRand : PublicKeyCore core → ProbComp core.Y)

/-- Key generation of the lab scheme makes no charged query. -/
theorem isQueryBoundP_labScheme_keygen :
    IsQueryBoundP (labScheme core optRand pkSeed).keygen (IsChargedLabQuery core pkSeed) 0 :=
  isQueryBoundP_bind (isQueryBoundP_labKeygen pkSeed) fun _ _ => isQueryBoundP_pure _ _ 0

/-- Signing with the lab scheme makes no charged query: the randomizer is a derivation query
after uniform sampling, and lab signing makes none. -/
theorem isQueryBoundP_labScheme_sign (pk sk : PublicKeyCore core) (msg : List Byte) :
    IsQueryBoundP ((labScheme core optRand pkSeed).sign pk sk msg)
      (IsChargedLabQuery core pkSeed) 0 := by
  refine isQueryBoundP_bind ?_ fun R _ => isQueryBoundP_labSignInternal pkSeed msg sk.pkRoot R
  have h : IsQueryBoundP ((do
      let addrnd ← (optRand pk : ProbComp core.Y)
      query (spec := deriveSpec core) (.inr (.inr (addrnd, msg)))) :
        OracleComp (deriveSpec core) core.Y) (fun t => IsChargedLabQuery core pkSeed (.inl t)) 0 :=
    isQueryBoundP_bind (n := 0) (m := 0) (isQueryBoundP_liftM_withDerivations (fun _ => id) _)
      fun _ _ => (isQueryBoundP_query_iff _ _ _).2 False.elim
  rw [liftComp_def]
  exact IsQueryBoundP.simulateQ_of_step h
    (fun _ _ => (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)
    fun t ht => by
      rcases t with (_ | _) | _ <;> exact (isQueryBoundP_query_iff _ _ _).2 fun h => (ht h).elim

/-- Verification with the lab scheme makes at most `V = verifyInternalQueryBound` charged
queries: it makes at most `V` queries in all. -/
theorem isQueryBoundP_labScheme_verify (pk : PublicKeyCore core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp core) :
    IsQueryBoundP ((labScheme core optRand pkSeed).verify pk msg sig)
      (IsChargedLabQuery core pkSeed) (GeneralScheme.verifyInternalQueryBound vp.params) := by
  let F : HasQuery.QueryHom (publicHashSpec core) (OracleComp (publicHashSpec core))
      (OracleComp (labSpec core)) :=
    { toMonadHom := simulateQ' (QueryImpl.ofLift (publicHashSpec core) (OracleComp (labSpec core)))
      map_query' _ := rfl }
  change IsQueryBoundP (GeneralScheme.verifyInternalM vp core msg sig pk :
    OracleComp (labSpec core) Bool) _ _
  rw [← GeneralScheme.verifyInternalM_natural vp core F]
  have h := IsQueryBoundP.simulateQ_of_step_le_total (q := IsChargedLabQuery core pkSeed)
    (impl := QueryImpl.ofLift (publicHashSpec core) (OracleComp (labSpec core)))
    (GeneralScheme.verifyInternalM_isTotalQueryBound vp core msg sig pk) fun t =>
      show IsQueryBoundP (query (spec := labSpec core) (.inl (.inl (.inr (.inl t))))) _ 1 from
        (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
  rw [mul_one] at h
  exact h

variable [SampleableType core.SkSeed] [SampleableType core.SkPrf]

/-- **The lab experiment makes at most `qh + V` charged queries**, for a forger with hash budget
`qh`: each forger hash query is one query, key generation and signing make none, and
verification makes at most `V`. -/
theorem isQueryBoundP_labExperiment {e : core.SkSeed ≃ core.Y}
    {optRand : PublicKeyCore core → ProbComp core.Y} {pkSeedDist : ProbComp core.PkSeed}
    {adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist)} {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    IsQueryBoundP (labExperiment core adv pkSeed) (IsChargedLabQuery core pkSeed)
      (qh + GeneralScheme.verifyInternalQueryBound vp.params) := by
  have hG (t : (unifSpec + hashSpec core).Domain) :
      (QueryImpl.ofLift (deriveSpec core) (OracleComp (labSpec core)) ∘ₛ
        (hashSpec core).withDerivationsLift (DeriveQuery core) core.Y) t =
        query (spec := labSpec core) (.inl (.inl t)) := by
    simp only [QueryImpl.apply_compose, OracleSpec.withDerivationsLift]
    rfl
  rw [labExperiment, labAdversary, deriveAdversary, UnforgeableAdversary.mapOracles_mapOracles]
  refine isQueryBoundP_unforgeableTranscriptExperiment_mapOracles_add _ (fun pk => (hadv pk).1)
    (fun t _ => hG t ▸ (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)
    (fun | .inl _, _ => hG _ ▸ (isQueryBoundP_query_iff _ _ _).2 False.elim
         | .inr _, ht => (ht trivial).elim)
    (isQueryBoundP_labScheme_keygen pkSeed optRand)
    (isQueryBoundP_labScheme_sign pkSeed optRand)
    (isQueryBoundP_labScheme_verify pkSeed optRand)

/-! ## The budget on every deferred run -/

variable [SampleableType (Bytes vp.params.m)] [DecidableEq core.PkSeed]
  [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf]

/-- On every run of the lab experiment in the deferred game from the empty state, the public cache
holds at most `qh + V` charged points. -/
theorem encard_setOf_isChargedPoint_inter_le {e : core.SkSeed ≃ core.Y}
    {optRand : PublicKeyCore core → ProbComp core.Y} {pkSeedDist : ProbComp core.PkSeed}
    {adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist)} {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs)
    {z : DeriveOutcome core ×
      RelabelState (hashSpec core) (DeriveQuery core) (NodeKey core) core.Y ×
        List (DeriveQuery core ⊕ NodeKey core)}
    (hz : z ∈ support ((simulateQ (slhGraph core pkSeed).deferredImpl
      (labExperiment core adv pkSeed)).run ((∅, ∅), []))) :
    ({t | IsChargedPoint core pkSeed t} ∩ {t | (z.2.1.1 t).isSome}).encard ≤
      qh + GeneralScheme.verifyInternalQueryBound vp.params := by
  simpa using
    (slhGraph core pkSeed).encard_inter_setOf_isSome_le_add_of_mem_support_simulateQ_deferredImpl
    (D := {t | IsChargedPoint core pkSeed t}) (fun _ ht => ht)
    (isQueryBoundP_labExperiment pkSeed hadv) hz

/-- **The budget of the lab experiment.** Under key separation, on every run of the lab
experiment in the deferred game from the empty state, twice the public entries at node keys over
`|Y|`, plus the seed charge, is at most `2 (qh + V) / |Y|` for a forger with hash budget `qh`: no
entry at a node key is derivable, and the two kinds together number at most `qh + V`. -/
theorem two_mul_encard_keyEntries_div_add_seedCharge_le (hsep : core.KeySeparated)
    {e : core.SkSeed ≃ core.Y} {optRand : PublicKeyCore core → ProbComp core.Y}
    {pkSeedDist : ProbComp core.PkSeed}
    {adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist)} {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs)
    {z : DeriveOutcome core ×
      RelabelState (hashSpec core) (DeriveQuery core) (NodeKey core) core.Y ×
        List (DeriveQuery core ⊕ NodeKey core)}
    (hz : z ∈ support ((simulateQ (slhGraph core pkSeed).deferredImpl
      (labExperiment core adv pkSeed)).run ((∅, ∅), []))) :
    2 * (((slhNodeKeys core pkSeed).keyEntries z.2.1.1).encard : ℝ≥0∞) / Nat.card core.Y +
        seedCharge core pkSeed z.2.1.1 ≤
      2 * ((qh : ℝ≥0∞) + GeneralScheme.verifyInternalQueryBound vp.params) / Nat.card core.Y := by
  set A := (slhNodeKeys core pkSeed).keyEntries z.2.1.1
  set B := {t | (z.2.1.1 t).isSome ∧ IsDerivablePublicQuery core pkSeed (.inl (.inr t))}
  have hdisj : Disjoint A B := by
    refine Set.disjoint_left.2 fun t ⟨_, hk⟩ ⟨_, hd⟩ => ?_
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hk
    rcases t with (⟨s, κ, xs⟩ | _) | _
    · obtain ⟨rfl, rfl⟩ := (slhNodeKeys_node_thash_eq_some_iff core).1 hk
      exact prfKey_val_ne_nodeKey_val core hsep ⟨_, hd.2⟩ k rfl
    all_goals
      rw [slhNodeKeys_node_eq_none_of_forall_ne_thash core (by simp)] at hk
      cases hk
  have hab : A.encard + B.encard ≤ qh + GeneralScheme.verifyInternalQueryBound vp.params := by
    rw [← Set.encard_union_eq hdisj]
    refine (Set.encard_le_encard ?_).trans (encard_setOf_isChargedPoint_inter_le pkSeed hadv hz)
    rintro t (⟨hC, hk⟩ | ⟨hC, hd⟩)
    exacts [⟨Or.inl hk, hC⟩, ⟨Or.inr hd, hC⟩]
  have hab' : (A.encard : ℝ≥0∞) + B.encard ≤
      (qh : ℝ≥0∞) + GeneralScheme.verifyInternalQueryBound vp.params := by
    simpa only [← ENat.toENNReal_add, ← Nat.cast_add, ENat.toENNReal_coe] using
      ENat.toENNReal_le.2 hab
  rw [seedCharge, ENNReal.div_add_div_same]
  gcongr
  calc 2 * (A.encard : ℝ≥0∞) + B.encard ≤ 2 * ((A.encard : ℝ≥0∞) + B.encard) := by
        rw [mul_add]; gcongr; exact le_mul_of_one_le_left' one_le_two
    _ ≤ _ := by gcongr

end SLHDSA.Security
