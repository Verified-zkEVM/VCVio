/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coupling.Guarded
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Work.Verification
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Work.Verification
import all HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Joint
import VCVio.OracleComp.SimSemantics.StateT.StateSeparating
public import HashSig.SLHDSA.Security.LabBudget
public import HashSig.SLHDSA.Security.NativeRelative
import HashSig.SLHDSA.Security.PrfKeyBound
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Work.HashQuery
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Work.Signing
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Work.Signing

/-! # Charging the public cache entries of the deferred verification graph -/

public section

open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open scoped ENNReal

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.DeferredReserve
open Guarded

/-- A point at a node key cannot also encode a private derivation. -/
private theorem node_point_not_derivable
    (s : FIPS205.core.PkSeed) (point : H.Domain)
    (hnode : ((slhNodeKeys FIPS205.core s).node point).isSome) :
    ¬IsDerivablePublicQuery FIPS205.core s (.inl (.inr point)) := by
  classical
  let answer : H.Range point := Classical.choice inferInstance
  let cache : H.QueryCache := (∅ : H.QueryCache).cacheQuery point answer
  have present : (cache point).isSome := by
    simp only [cache, QueryCache.cacheQuery_self, Option.isSome_some]
  have separated := disjoint_keyEntries_setOf_isDerivablePublicQuery
    (SLHDSA.Concrete.keySeparated_shakePrimitives FIPS205.params.params) s cache
  intro derives
  exact (Set.disjoint_left.1 separated) ⟨present, hnode⟩ ⟨present, derives⟩

/-- One original raw marker pays its routed point weight and selected-Hmsg metadata. -/
theorem reserve_raw_marker_weight
    (s : FIPS205.core.PkSeed) (phase : SigningView.Phase) (raw : Raw.Domain)
    (hphase : phase = .adversary ∨ phase = .verification) :
    let event : Ev := .ambient phase (.inr raw)
    let pointWeight := fun point : H.Domain =>
      32 * (if ((slhNodeKeys FIPS205.core s).node point).isSome then 1 else 0) +
        16 * (if IsDerivablePublicQuery FIPS205.core s (.inl (.inr point)) then 1 else 0)
    (match (encoding s).route raw with
      | none => 0
      | some point => pointWeight point) + 31 * metadataCost true s event ≤
        (policy true s event).1 ∧ (policy true s event).2 = 0 := by
  classical
  let pointWeight := fun point : H.Domain =>
    32 * (if ((slhNodeKeys FIPS205.core s).node point).isSome then 1 else 0) +
      16 * (if IsDerivablePublicQuery FIPS205.core s (.inl (.inr point)) then 1 else 0)
  have routed :
      (match (encoding s).route raw with
        | none => 0
        | some point => pointWeight point) +
          31 * (match (encoding s).route raw with
            | some (.inl (.hmsg ..)) => 1
            | _ => 0) ≤
        1 + (match (encoding s).route raw with
          | none => 0
          | some (.inl (.hmsg ..)) => 30
          | some point =>
              if ((slhNodeKeys FIPS205.core s).node point).isSome then 31 else 15) := by
    cases route : (encoding s).route raw with
    | none => simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_le]
    | some point =>
        rcases point with (⟨seed, key, inputs⟩ | ⟨randomness, seed, root, message⟩) | nonce
        · by_cases atNode :
              ((slhNodeKeys FIPS205.core s).node (.inl (.thash seed key inputs))).isSome
          · have notDerivable :=
              node_point_not_derivable s (.inl (.thash seed key inputs)) atNode
            norm_num [pointWeight, atNode, notDerivable]
          · by_cases derives :
                IsDerivablePublicQuery FIPS205.core s (.inl (.inr (.inl (.thash seed key inputs))))
            · norm_num [pointWeight, atNode, derives]
            · norm_num [pointWeight, atNode, derives]
        · have noNode := slhNodeKeys_node_eq_none_of_forall_ne_thash
            FIPS205.core (pkSeed := s)
            (t := .inl (.hmsg randomness seed root message)) (by simp)
          simp [pointWeight, noNode, IsDerivablePublicQuery]
        · have noNode := slhNodeKeys_node_eq_none_of_forall_ne_thash
            FIPS205.core (pkSeed := s) (t := .inr nonce) (by simp)
          simp [pointWeight, noNode, IsDerivablePublicQuery]
  constructor
  · cases route : (encoding s).route raw with
    | none =>
      rcases hphase with rfl | rfl <;>
        simp [route, policy, originalPolicy, Game.Counted.sourcePolicy,
          Game.Counted.sourceKind, Game.hashCost, RandomOracleModel.hashCost,
          reserveExtra, metadataCost, selectedRaw]
    | some point =>
      rcases point with (⟨seed, key, values⟩ | ⟨R, seed, root, message⟩) | nonce
      all_goals rcases hphase with rfl | rfl
      all_goals
        simpa [route, pointWeight, policy, originalPolicy, Game.Counted.sourcePolicy,
          Game.Counted.sourceKind, Game.hashCost, RandomOracleModel.hashCost,
          reserveExtra, metadataCost, selectedRaw] using routed
  · rcases hphase with rfl | rfl <;>
      simp [policy, originalPolicy, Game.Counted.sourcePolicy, Game.Counted.sourceKind,
        Game.hashCost, RandomOracleModel.hashCost]

/-- The deferred state of the SHAKE-128s hash graph. -/
abbrev Graph := CoverageDeferred.D FIPS205.core
/-- The raw query cache, phase metadata, deferred graph and budget guard. -/
abbrev State := (Raw.QueryCache × (Meta × Graph)) × Paid
private noncomputable abbrev ordinary (s : FIPS205.core.PkSeed) :=
  QueryImpl.Stateful.link (observeLab s true) (slhGraph FIPS205.core s).deferredImpl
private noncomputable abbrev routed (s : FIPS205.core.PkSeed) :=
  QueryImpl.Stateful.link (routeLab s) (ordinary s)
/-- The budget-guarded handler that routes public and marked queries through the deferred graph. -/
noncomputable def engine (s : FIPS205.core.PkSeed) (caps : Nat × Nat)
    (fallback : (i : LabCommon.Domain) → LabCommon.Range i) :
    QueryImpl LabCommon (StateT State ProbComp) :=
  QueryImpl.guardQueryBudget caps (Sum.elim (fun _ : A.Domain => (0, 0)) (policy true s))
    (routed s) fallback

/-- The deferred graph, metadata and paid work are observations of the same guarded execution. -/
theorem deferred_run_eq_guarded (s : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (caps : Nat × Nat) (fallback : (i : LabCommon.Domain) → LabCommon.Range i) :
    (fun z : GuardedFill.Value × Graph =>
      (z.1.1.1.1, ((z.1.1.2, (z.1.2, z.2)), z.1.1.1.2.2))) <$>
        (simulateQ (slhGraph FIPS205.core s).deferredImpl
          (GuardedFill.labProgram s adv true true caps fallback)).run ((∅, ∅), []) =
      (simulateQ (engine s caps fallback) (commonSource true s adv)).run
        ((∅, ((0, .keygen), ((∅, ∅), []))), ((0, 0), false)) := by
  let _ : MonadLiftT (OracleComp LabCommon) (StateT PUnit.{1} (OracleComp LabCommon)) :=
    ⟨fun action => StateT.lift action⟩
  have square := QueryImpl.map_run_simulateQ_guardQueryBudget_free_eq caps
    (Sum.elim (fun _ : A.Domain => (0, 0)) (policy true s)) (routed s)
    fallback (commonSource true s adv) (∅, ((0, .keygen), ((∅, ∅), []))) (0, 0) false
  simpa only [engine, routed, ordinary, GuardedFill.labProgram, guardedRoutedSource, observeLab,
    QueryImpl.Stateful.simulateQ_link_run,
    QueryImpl.Stateful.Frame.linkReshape, QueryImpl.Stateful.Frame.prod, Functor.map_map,
    Function.comp_def, Prod.map, id_eq, Equiv.coe_fn_mk, PFunctor.Lens.State.fst_put,
    PFunctor.Lens.State.snd_put] using square

open Classical in
/-- The cache charge, with weight 32 for a node-key entry and 16 for a derivable public point. -/
noncomputable abbrev entries (s : FIPS205.core.PkSeed) (cache : H.QueryCache) : ℝ≥0∞ :=
  32 * (((slhNodeKeys FIPS205.core s).keyEntries cache).encard : ℝ≥0∞) +
    16 * ({q | (cache q).isSome ∧ IsDerivablePublicQuery FIPS205.core s (.inl (.inr q))}.encard :
      ℝ≥0∞)

open Classical in
private noncomputable abbrev pointWeight (s : FIPS205.core.PkSeed) (p : H.Domain) : Nat :=
  32 * (if ((slhNodeKeys FIPS205.core s).node p).isSome then 1 else 0) +
    16 * (if IsDerivablePublicQuery FIPS205.core s (.inl (.inr p)) then 1 else 0)

private abbrev pointOf : Lab.Domain → Option H.Domain :=
  Sum.elim (Sum.elim (Sum.elim (fun _ => none) some) (fun _ => none)) (fun _ => none)

private theorem graph_point (s : FIPS205.core.PkSeed) (n : Lab.Domain) (before : Graph)
    (out : Lab.Range n × Graph) (mem : out ∈ support
      (((slhGraph FIPS205.core s).deferredImpl n).run before)) :
    entries s out.2.1.1 ≤ entries s before.1.1 +
      ((pointOf n).elim 0 (pointWeight s) : Nat) := by
  classical
  have count (D : Set H.Domain) :
      ({q | (out.2.1.1 q).isSome ∧ q ∈ D}.encard : ℝ≥0∞) ≤
        ({q | (before.1.1 q).isSome ∧ q ∈ D}.encard : ℝ≥0∞) +
          (if (pointOf n).elim False (· ∈ D) then 1 else 0) := by
    let selects (i : Lab.Domain) := (pointOf i).elim False (· ∈ D)
    have step := (slhGraph FIPS205.core s).deferredImpl_cachesOnlyQueryPoint
      |>.encard_inter_le_add_of_mem_support (D := D) (p := selects) (fun i q hq hD => by
        change pointOf i = some q at hq
        simpa only [selects, hq, Option.elim_some] using hD) mem
    rw [Set.inter_comm D, Set.inter_comm D] at step
    simpa only [Set.inter_def, Set.mem_ofPred_eq, ENat.toENNReal_add, apply_ite ENat.toENNReal,
      ENat.toENNReal_one, ENat.toENNReal_zero, selects] using ENat.toENNReal_mono step
  let nodes : Set H.Domain := {q | ((slhNodeKeys FIPS205.core s).node q).isSome}
  let derivable : Set H.Domain := {q | IsDerivablePublicQuery FIPS205.core s (.inl (.inr q))}
  have combined := add_le_add
    (mul_le_mul_of_nonneg_left (count nodes) (zero_le : 0 ≤ (32 : ℝ≥0∞)))
    (mul_le_mul_of_nonneg_left (count derivable) (zero_le : 0 ≤ (16 : ℝ≥0∞)))
  refine combined.trans_eq ?_
  cases h : pointOf n with
  | none => simp [entries, CanonicalGraph.NodeKeys.keyEntries, nodes, derivable]
  | some q =>
    simp only [Option.elim_some, entries, pointWeight, CanonicalGraph.NodeKeys.keyEntries,
      nodes, derivable, Set.mem_ofPred_eq, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    by_cases node : ((slhNodeKeys FIPS205.core s).node q).isSome <;>
      by_cases derives : IsDerivablePublicQuery FIPS205.core s (.inl (.inr q)) <;>
      simp [node, derives] <;> ring

private theorem ordinary_native (s : FIPS205.core.PkSeed) (n : Lab.Domain) (m : Meta)
    (g : Graph) :
    (ordinary s (.inl n)).run (m, g) = (fun v => (v.1, (m, v.2))) <$>
      ((slhGraph FIPS205.core s).deferredImpl n).run g := by
  simp [ordinary, QueryImpl.Stateful.link_impl_apply_run, observeLab, QueryImpl.add,
    QueryImpl.id', StateT.run_map, Functor.map_map, QueryImpl.Stateful.Frame.linkReshape,
    QueryImpl.Stateful.Frame.prod]

private abbrev Front := Raw.QueryCache × (Meta × Graph)
open Classical in
private noncomputable abbrev ambientWeight (s : FIPS205.core.PkSeed) : A.Domain → Nat
  | .inl n => (pointOf n).elim 0 (pointWeight s)
  | .inr raw => ((encoding s).route raw).elim 0 (pointWeight s)

private theorem raw_query (s : FIPS205.core.PkSeed) (raw : Raw.Domain) (st : Front)
    (v : Raw.Range raw × Front) (mem : v ∈ support ((routed s (.inl (.inr raw))).run st)) :
    v.2.2.1 = st.2.1 ∧ entries s v.2.2.2.1.1 ≤
      entries s st.2.2.1.1 + (ambientWeight s (.inr raw) : Nat) := by
  let transport := QueryImpl.ofLift (unifSpec + H) (OracleComp (Lab + O))
  let handler := ordinary s ∘ₛ transport
  have included (i : (unifSpec + H).Domain) :
      transport i = (liftM ((Lab + O).query (.inl (.inl (.inl i)))) :
        OracleComp (Lab + O) _) := by
    rcases i with n | (p | p) <;> (try cases p) <;> rfl
  have step (i : (unifSpec + H).Domain) (w : Meta × Graph) : (handler i).run w =
      (fun a => (a.1, (w.1, a.2))) <$> ((slhGraph FIPS205.core s).deferredImpl
        (.inl (.inl i))).run w.2 := by
    change (simulateQ (ordinary s) (transport i)).run w = _
    rw [included, simulateQ_spec_query, ordinary_native]
  have uniform {β : Type} (p : ProbComp β) (w : Meta × Graph) :
      (simulateQ handler (liftComp p (unifSpec + H))).run w = (fun a => (a, w)) <$> p := by
    apply QueryImpl.Stateful.simulateQ_liftComp_run_of_query
    intro n state
    rw [liftComp_liftM_query]
    change (simulateQ handler (liftM ((unifSpec + H).query (.inl n)))).run state = _
    rw [simulateQ_spec_query, step]
    rcases state with ⟨m, graph, pending⟩
    have law := (slhGraph FIPS205.core s).deferredImpl_run_inl (.inl (.inl n)) (graph, pending)
    rw [law, (slhGraph FIPS205.core s).relabelImpl_run_unif n graph]
    simp only [Functor.map_map]
  have front : (routed s (.inl (.inr raw))).run st =
      (fun x => (x.1.1, (x.1.2, x.2))) <$> (simulateQ handler
        (((encoding s).tableRouter raw).run st.1)).run st.2 := by
    rw [QueryImpl.Stateful.link_impl_apply_run]
    change _ <$> (simulateQ (ordinary s)
      (simulateQ transport (((encoding s).tableRouter raw).run st.1))).run st.2 = _
    rw [← QueryImpl.simulateQ_compose]
    rfl
  rw [front, support_map] at mem
  obtain ⟨v, hv, rfl⟩ := mem
  simp only [RandomOracleEncoding.tableRouter, StateT.run_mk, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff] at hv
  obtain ⟨draw, hd, hv⟩ := hv
  change draw ∈ support ((simulateQ handler
    (liftComp ((Raw.randomOracle raw).run st.1) (unifSpec + H))).run st.2) at hd
  rw [uniform, support_map] at hd
  obtain ⟨draw, _, rfl⟩ := hd
  cases which : (encoding s).route raw with
  | none =>
    simp only [which, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hv
    subst v
    simp [ambientWeight, which]
  | some q =>
    simp only [which, simulateQ_map, StateT.run_map, support_map] at hv
    obtain ⟨a, ha, rfl⟩ := hv
    change a ∈ support ((simulateQ handler (liftM ((unifSpec + H).query (.inr q)))).run st.2) at ha
    rw [simulateQ_spec_query, step, support_map] at ha
    obtain ⟨p, hp, rfl⟩ := ha
    refine ⟨rfl, ?_⟩
    simpa only [ambientWeight, which, Option.elim_some, pointOf, Sum.elim_inl, Sum.elim_inr] using
      graph_point s (.inl (.inl (.inr q))) st.2.2 p hp

private theorem ambient_query (s : FIPS205.core.PkSeed) (i : A.Domain) (st : Front)
    (z : A.Range i × Front) (mem : z ∈ support ((routed s (.inl i)).run st)) :
    z.2.2.1 = st.2.1 ∧ entries s z.2.2.2.1.1 ≤
      entries s st.2.2.1.1 + (ambientWeight s i : Nat) := by
  cases i with
  | inr raw => exact raw_query s raw st z mem
  | inl n =>
    have point : (routed s (.inl (.inl n))).run st =
        (fun v => (v.1, (st.1, (st.2.1, v.2)))) <$>
          ((slhGraph FIPS205.core s).deferredImpl n).run st.2.2 := by
      rcases st with ⟨cache, metaState, graph⟩
      simp [routed, QueryImpl.Stateful.link_impl_apply_run, routeLab, QueryImpl.add,
        observeLab, QueryImpl.id', QueryImpl.Stateful.Frame.linkReshape,
        QueryImpl.Stateful.Frame.prod,
        Functor.map_map, StateT.run_map]
    rw [point, support_map] at mem
    obtain ⟨p, hp, rfl⟩ := mem
    exact ⟨rfl, graph_point s n st.2.2 p hp⟩

/-- The paid work covers the weighted graph entries, the observed hash work and signing requests. -/
noncomputable abbrev good (s : FIPS205.core.PkSeed) (st : State) :=
  entries s st.1.2.2.1.1 + (31 * st.1.2.1.1 + 32 * st.2.1.2 : Nat) ≤ (st.2.1.1 : ℝ≥0∞)

private noncomputable def marker (s : FIPS205.core.PkSeed) (e : Ev) (st : Front) : Front :=
  (st.1, (aux (spec := Lab) (metadataCost true s) (.inr e)
    PUnit.unit PUnit.unit PUnit.unit st.2.1, st.2.2))

private theorem marker_query (s : FIPS205.core.PkSeed) (e : Ev) (st : Front) :
    (routed s (.inr e)).run st = pure (PUnit.unit, marker s e st) := by
  rcases st with ⟨raw, m, g⟩
  simp [routed, ordinary, QueryImpl.Stateful.link_impl_apply_run, routeLab, QueryImpl.add,
    observeLab, marker, QueryImpl.Stateful.Frame.linkReshape, QueryImpl.Stateful.Frame.prod]

private abbrev transaction (e : Ev) (i : A.Domain) : OracleComp LabCommon (A.Range i) := do
  let _ ← (liftM (LabCommon.query (.inr e)) : OracleComp LabCommon PUnit)
  liftM (LabCommon.query (.inl i))

private theorem paid_transaction (s : FIPS205.core.PkSeed) (caps : Nat × Nat)
    (fallback : (i : LabCommon.Domain) → LabCommon.Range i) (e : Ev) (i : A.Domain)
    (funded : ambientWeight s i + 31 * metadataCost true s e + 32 * (policy true s e).2 ≤
      (policy true s e).1) (st : State) (prior : good s st) (out : A.Range i × State)
    (mem : out ∈ support ((simulateQ (engine s caps fallback) (transaction e i)).run st)) :
    good s out.2 := by
  classical
  let proposed := st.2.1 + policy true s e
  cases stopped : st.2.2 with
  | true =>
    have eqOut : out = (fallback (.inl i), st) := by
      simpa [transaction, engine, QueryImpl.guardQueryBudget, stopped,
        StateT.run_bind] using mem
    exact eqOut ▸ prior
  | false =>
    by_cases fits : proposed ≤ caps
    · have alsoFits : st.2.1 + policy true s e ≤ caps := fits
      have zero : proposed + (0, 0) = proposed := add_zero _
      have computed : (simulateQ (engine s caps fallback) (transaction e i)).run st =
          (fun z => (z.1, z.2, (proposed, false))) <$>
            ((routed s (.inl i)).run (marker s e st.1)) := by
        have mark := marker_query s e st.1
        simp [transaction, engine, QueryImpl.guardQueryBudget, stopped, proposed, alsoFits,
          StateT.run_bind, show ((0, 0) : Nat × Nat) = 0 from rfl, mark]
      rw [computed, support_map] at mem
      obtain ⟨v, hv, rfl⟩ := mem
      obtain ⟨same, weight⟩ := ambient_query s i (marker s e st.1) v hv
      have tracker : v.2.2.1.1 = st.1.2.1.1 + metadataCost true s e := by
        rw [same]
        cases e <;> rfl
      have spent : (ambientWeight s i : ℝ≥0∞) +
          (31 * metadataCost true s e + 32 * (policy true s e).2 : Nat) ≤
          ((policy true s e).1 : ℝ≥0∞) := by
        exact_mod_cast (show ambientWeight s i +
          (31 * metadataCost true s e + 32 * (policy true s e).2) ≤ (policy true s e).1 by omega)
      change entries s v.2.2.2.1.1 + (31 * v.2.2.1.1 + 32 * proposed.2 : Nat) ≤
        (proposed.1 : ℝ≥0∞)
      rw [tracker]
      calc
        _ ≤ (entries s st.1.2.2.1.1 + (ambientWeight s i : Nat)) +
            (31 * (st.1.2.1.1 + metadataCost true s e) + 32 * proposed.2 : Nat) :=
              add_le_add weight le_rfl
        _ = (entries s st.1.2.2.1.1 + (31 * st.1.2.1.1 + 32 * st.2.1.2 : Nat)) +
            ((ambientWeight s i : ℝ≥0∞) +
              (31 * metadataCost true s e + 32 * (policy true s e).2 : Nat)) := by
                simp only [proposed, Prod.snd_add, Nat.cast_add, Nat.cast_mul]
                ring
        _ ≤ _ := by simpa only [proposed, Prod.fst_add, Nat.cast_add] using add_le_add prior spent
    · have overflow : ¬st.2.1 + policy true s e ≤ caps := fits
      have eqOut : out = (fallback (.inl i), st.1, (st.2.1, true)) := by
        simpa [transaction, engine, QueryImpl.guardQueryBudget, stopped, overflow,
          StateT.run_bind] using mem
      exact eqOut ▸ prior

/-- An actual adversarial raw transaction reserves the cache weight of its routed point and
the cost of its selected digest marker together. -/
theorem marked_raw_graph_reserve (s : FIPS205.core.PkSeed) (caps : Nat × Nat)
    (fallback : (i : LabCommon.Domain) → LabCommon.Range i) (raw : Raw.Domain) (st : State)
    (prior : good s st) (out : Raw.Range raw × State)
    (mem : out ∈ support ((simulateQ (engine s caps fallback)
      (simulateQ commonProjection (SigningView.Events.phaseImpl A Message .adversary
        (.inr raw)))).run st)) : good s out.2 := by
  have payment := reserve_raw_marker_weight s .adversary raw (Or.inl rfl)
  refine paid_transaction s caps fallback (.ambient .adversary (.inr raw)) (.inr raw) ?_ st
    prior out ?_
  · rw [payment.2, Nat.mul_zero, Nat.add_zero]
    cases route : (encoding s).route raw <;> simpa only [ambientWeight, route,
      Option.elim_none, Option.elim_some, pointWeight] using payment.1
  · have eq := (show simulateQ commonProjection
        (SigningView.Events.phaseImpl A Message .adversary (.inr raw)) =
        transaction (.ambient .adversary (.inr raw)) (.inr raw) by
        simp [transaction, SigningView.Events.phaseImpl, SigningView.Events.emit, commonProjection,
          commonEvent, QueryImpl.add, seqRight_eq_bind])
    rwa [← eq]

/-- An honestly constructed verification point is either routed identically or is an H_msg query
at the generated key. H_msg never adds a node-key or derivable cache entry. -/
theorem verify_point_graph_reserve (s : FIPS205.core.PkSeed) (root : FIPS205.core.Y)
    (q : (publicHashSpec FIPS205.core).Domain)
    (allowed : (encoding s).route (encode FIPS205.params (.inl q)) = some (.inl q) ∨
      ∃ r msg, q = .hmsg r s root msg)
    (caps : Nat × Nat) (fallback : (i : LabCommon.Domain) → LabCommon.Range i)
    (st : State) (prior : good s st) (out : (publicHashSpec FIPS205.core).Range q × State)
    (mem : out ∈ support ((simulateQ (engine s caps fallback) (simulateQ commonProjection
      (SigningView.Events.phaseImpl A Message .verification
        (.inl (.inl (.inl (.inr (.inl q)))))))).run st)) : good s out.2 := by
  let raw := encode FIPS205.params (.inl q)
  let e : Ev := .ambient .verification (.inr raw)
  let i : A.Domain := .inl (.inl (.inl (.inr (.inl q))))
  have rule := reserve_raw_marker_weight s .verification raw (Or.inr rfl)
  have sufficient : pointWeight s (.inl q) ≤ ((encoding s).route raw).elim 0 (pointWeight s) := by
    rcases allowed with fixed | ⟨r, msg, rfl⟩
    · change (encoding s).route raw = some (.inl q) at fixed
      rw [fixed]
      rfl
    · have none := slhNodeKeys_node_eq_none_of_forall_ne_thash FIPS205.core (pkSeed := s)
        (t := .inl (.hmsg r s root msg)) (by simp)
      simp [pointWeight, none, IsDerivablePublicQuery]
  have amount : ((encoding s).route raw).elim 0 (pointWeight s) +
        31 * metadataCost true s e ≤ (policy true s e).1 := by
    cases route : (encoding s).route raw <;> simpa only [route, Option.elim_none,
      Option.elim_some, e, pointWeight] using rule.1
  refine paid_transaction s caps fallback e i ?_ st prior out ?_
  · change pointWeight s (.inl q) + 31 * metadataCost true s e + 32 * (policy true s e).2 ≤ _
    rw [show (policy true s e).2 = 0 from rule.2, Nat.mul_zero, Nat.add_zero]
    exact (Nat.add_le_add_right sufficient _).trans amount
  · have eq : simulateQ commonProjection (SigningView.Events.phaseImpl A Message .verification i) =
        transaction e i := by
      simp [i, e, raw, transaction, SigningView.Events.phaseImpl, SigningView.Events.emit,
        commonProjection, commonEvent, sourceInput, QueryImpl.add, seqRight_eq_bind]
    rwa [← eq]

/-- Executing the program preserves the graph-entry budget on every supported result. -/
abbrev Safe {α : Type} (s : FIPS205.core.PkSeed) (caps : Nat × Nat)
    (fb : (i : LabCommon.Domain) → LabCommon.Range i) (p : OracleComp LabCommon α) :=
  ∀ st, good s st → ∀ z ∈ support ((simulateQ (engine s caps fb) p).run st), good s z.2

private theorem safe_pure {α : Type} {s caps fb} (x : α) : Safe s caps fb (pure x) := by
  intro st prior z mem
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at mem
  exact mem ▸ prior

private theorem safe_bind {α β : Type} {s caps fb} {p : OracleComp LabCommon α}
    {f : α → OracleComp LabCommon β} (hp : Safe s caps fb p) (hf : ∀ a, Safe s caps fb (f a)) :
    Safe s caps fb (p >>= f) := by
  intro st prior z mem
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at mem
  obtain ⟨mid, hm, hz⟩ := mem
  exact hf mid.1 mid.2 (hp st prior mid hm) z hz

/-- The actual rejecting verifier preserves the graph reserve for every decoded wire output;
framing and signature decoding rejections return false before spending any reserve. -/
theorem verify_graph_reserve (s : FIPS205.core.PkSeed) (root : FIPS205.core.Y)
    (request : Message) (wire : List Byte) (caps : Nat × Nat)
    (fallback : (i : LabCommon.Domain) → LabCommon.Range i)
    (st : State) (prior : good s st) (out : Bool × State)
    (mem : out ∈ support ((simulateQ (engine s caps fallback)
      (VerificationOffsets.verifySource s ⟨s, root⟩ request wire)).run st)) : good s out.2 := by
  refine VerificationOffsets.verifySource_preserves s root request wire
    (fun action => Safe s caps fallback action) (fun x => safe_pure x)
    (fun first next => safe_bind first next) ?_ ?_ st prior out mem
  · intro address allowed values
    have honest : IsHonestKey FIPS205.params FIPS205.core (FIPS205.core.adrsToKey address) :=
      ⟨address, Or.inl allowed, rfl⟩
    exact verify_point_graph_reserve s root (.thash s (FIPS205.core.adrsToKey address) values)
      (Or.inl (shakeRoute_encode_thash _ _ honest)) caps fallback
  · intro randomness message
    exact verify_point_graph_reserve s root (.hmsg randomness s root message)
      (Or.inr ⟨randomness, message, rfl⟩) caps fallback

private theorem safe_query {s caps fb} (i : LabCommon.Domain)
    (admitted : ∀ st : State, good s st → ∀ v ∈ support ((routed s i).run st.1),
      good s (v.2, (st.2.1 + Sum.elim (fun _ : A.Domain => (0, 0)) (policy true s) i, false))) :
    Safe s caps fb (liftM (LabCommon.query i)) := by
  intro st prior z mem
  rw [simulateQ_spec_query] at mem
  exact QueryImpl.guardQueryBudget_cases_of_mem_support (P := fun out => good s out.2) mem
    (fun _ => prior) (fun _ _ v hv => admitted st prior v hv)

private theorem safe_free {s caps fb} (i : A.Domain) (free : ambientWeight s i = 0) :
    Safe s caps fb (liftM (LabCommon.query (.inl i))) := by
  apply safe_query
  intro st prior v hv
  obtain ⟨same, weight⟩ := ambient_query s i st.1 v hv
  simp only [free, Nat.cast_zero, add_zero] at weight
  simpa only [Sum.elim_inl, show ((0, 0) : Nat × Nat) = 0 from rfl, add_zero, good, same] using
    (add_le_add weight le_rfl).trans prior

private theorem safe_event {s caps fb} (e : Ev)
    (funded : 31 * metadataCost true s e + 32 * (policy true s e).2 ≤ (policy true s e).1) :
    Safe s caps fb (liftM (LabCommon.query (.inr e))) := by
  apply safe_query
  intro st prior z mem
  rw [marker_query, support_pure, Set.mem_singleton_iff] at mem
  subst z
  have m : (marker s e st.1).2.1.1 = st.1.2.1.1 + metadataCost true s e := by cases e <;> rfl
  change entries s st.1.2.2.1.1 +
    (31 * (marker s e st.1).2.1.1 + 32 * (st.2.1.2 + (policy true s e).2) : Nat) ≤ _
  rw [m]
  have increase : ((31 * metadataCost true s e + 32 * (policy true s e).2 : Nat) : ℝ≥0∞)
      ≤ ((policy true s e).1 : ℝ≥0∞) := by exact_mod_cast funded
  convert add_le_add prior increase using 1 <;>
    simp only [Sum.elim_inr, Prod.fst_add, Nat.cast_add, Nat.cast_mul]; ring

private theorem uncharged_zero {s} (n : Lab.Domain)
    (h : ¬IsChargedLabQuery FIPS205.core s n) : ambientWeight s (.inl n) = 0 := by
  classical
  rcases n with (((sample | pt) | der) | lab) <;> try rfl
  change ¬(_ ∨ _) at h
  simp [ambientWeight, pointOf, pointWeight, not_or.mp h |>.1, not_or.mp h |>.2]

private theorem body_uncharged (s : FIPS205.core.PkSeed) (pk sk : PK) (request : Message) :
    (SigningCounts.body s pk sk request).AllQueriesSatisfy
      (fun t => ¬IsChargedLabQuery FIPS205.core s t) := by
  apply (isQueryBoundP_zero_iff _ _).mp
  cases framing : (External.encodePureMessage request.context request.message).toOption with
  | none => simp [SigningCounts.body, partialView, SigningView.rejectingEncoding_sign, framing]
  | some msg =>
    simpa only [SigningCounts.body, partialView, ite_true, SigningView.rejectingEncoding_sign,
      framing, isQueryBoundP_map_iff, not_not] using
      isQueryBoundP_labScheme_sign (core := FIPS205.core) s (fun pk => pure pk.pkSeed) pk sk msg

/-- The attempt marker pays for its signing unit even if framing rejects the request. Every
actual private signer call preserves the remaining cache reserve. -/
theorem signing_graph_reserve (s : FIPS205.core.PkSeed) (pk sk : PK) (request : Message)
    (caps : Nat × Nat) (fb : (i : LabCommon.Domain) → LabCommon.Range i) :
    Safe s caps fb (SigningCounts.signSource s pk sk request) := by
  rw [SigningCounts.callback_eq]
  simp only [SigningCounts.smallCallback, simulateQ_bind, simulateQ_spec_query]
  apply safe_bind
  · apply safe_event
    norm_num [policy, originalPolicy, Game.Counted.sourcePolicy, reserveExtra, metadataCost,
      selectedRaw]
  · intro _
    let src := SigningCounts.body s pk sk request
    have allowed := body_uncharged s pk sk request
    change src.AllQueriesSatisfy _ at allowed
    change Safe s caps fb (simulateQ SigningCounts.embed
      (simulateQ (NativeCounts.phaseObservation FIPS205.core SigningCounts.observe .signer) src))
    rw [← QueryImpl.simulateQ_compose]
    let handler := SigningCounts.embed ∘ₛ
      (NativeCounts.phaseObservation FIPS205.core SigningCounts.observe .signer)
    change Safe s caps fb (simulateQ handler src)
    intro st prior out mem
    rw [← QueryImpl.simulateQ_compose] at mem
    refine allowed.holds_of_mem_support_run_simulateQ (good s) (fun t uncharged => ?_) prior mem
    have native := safe_free (caps := caps) (fb := fb) (.inl t) (uncharged_zero t uncharged)
    change Safe s caps fb (handler t)
    cases obs : SigningCounts.observe t with
    | none =>
      simp only [handler, QueryImpl.apply_compose, NativeCounts.phaseObservation,
        QueryImpl.preInsert_apply, obs, pure_bind]
      exact native
    | some label =>
      have event := safe_event (s := s) (caps := caps) (fb := fb) (.ambient .signer label) (by
        cases label <;> simp [metadataCost, selectedRaw, policy, reserveExtra, originalPolicy,
          Game.Counted.sourcePolicy, Game.Counted.sourceKind])
      simp only [handler, QueryImpl.apply_compose, NativeCounts.phaseObservation,
        QueryImpl.preInsert_apply, obs, simulateQ_bind, simulateQ_spec_query]
      exact safe_bind event (fun _ => native)

private theorem logged_graph_reserve {s caps fb} (pk sk : PK) {α : Type}
    (program : OracleComp (R + Sign) α) :
    Safe s caps fb (simulateQ (SigningCounts.clientHandler s pk sk) program).run := by
  refine SigningCounts.clientHandler_preserves (fun action => Safe s caps fb action)
    (fun x => safe_pure x) (fun first next => safe_bind first next) ?_
    (fun request => signing_graph_reserve s pk sk request caps fb) program
  rintro (n | raw)
  · let i : A.Domain := .inl (.inl (.inl (.inl n)))
    let e : Ev := .ambient .adversary (.inl n)
    have eqn : SigningCounts.clientAmbient (.inl n) = transaction e i := by
      simp [SigningCounts.clientAmbient, e, i, transaction, SigningView.Events.phaseImpl,
        SigningView.Events.emit, commonProjection, commonEvent, sourceInput, QueryImpl.add,
        seqRight_eq_bind]
    rw [eqn]
    apply paid_transaction s caps fb e i
    simp [e, i, ambientWeight, pointOf, metadataCost, selectedRaw, policy, originalPolicy,
      Game.Counted.sourcePolicy, Game.Counted.sourceKind, reserveExtra]
  · exact marked_raw_graph_reserve s caps fb raw

private theorem suffix_graph_reserve {s caps fb} (root : FIPS205.core.Y) (sk : PK)
    (adv : Game.Adversary FIPS205.Answer PK) :
    Safe s caps fb (SLHDSA.SHAKE128s.MarkedPrefix.suffixSource s adv ⟨s, root⟩ sk) := by
  have client := logged_graph_reserve (s := s) (caps := caps) (fb := fb) ⟨s, root⟩ sk
    (Game.Counted.externalMain adv ⟨s, root⟩)
  rw [← SigningCounts.actual_client_eq] at client
  simp only [SLHDSA.SHAKE128s.MarkedPrefix.suffixSource, simulateQ_bind, simulateQ_pure]
  apply safe_bind client
  rintro ⟨forgery, log⟩
  exact safe_bind (verify_graph_reserve s root forgery.1 forgery.2 caps fb) (fun _ => safe_pure _)

private theorem private_input_graph_reserve {s caps fb} (i : LabCommon.Domain)
    (hi : SLHDSA.SHAKE128s.MarkedPrefix.PrivateCommon i) (st : State) (prior : good s st)
    (out : LabCommon.Range i × State) (mem : out ∈ support ((engine s caps fb i).run st)) :
    good s out.2 := by
  rcases i with (n | raw) | event
  · have free : ambientWeight s (.inl n) = 0 := by
      rcases n with (((sample | point) | (privateD | publicD)) | lab) <;>
        first | rfl | exact hi.elim
    apply safe_free (.inl n) free st prior out
    simpa only [simulateQ_spec_query] using mem
  · exact hi.elim
  · exact hi.elim

private theorem keygen_seed {s caps fb} (st : State) (z : (PK × PK) × State)
    (mem : z ∈ support ((simulateQ (engine s caps fb)
      (SLHDSA.SHAKE128s.MarkedPrefix.keygenSource s)).run st)) : z.1.1.pkSeed = s := by
  have keyMem := SigningCounts.source_support (engine s caps fb) _ st z mem
  have key := support_simulateQ_subset commonProjection _ keyMem
  have key := support_simulateQ_subset (SigningView.Events.phaseImpl A Message .keygen) _ key
  have key := support_simulateQ_subset (fun input : Lab.Domain =>
    (liftM (A.query (.inl input)) : OracleComp A (Lab.Range input))) _ key
  change z.1 ∈ support ((labScheme FIPS205.core (fun pk => pure pk.pkSeed) s).keygen) at key
  simp only [labScheme, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at key
  obtain ⟨root, _, same⟩ := key
  exact congrArg (fun keys : PK × PK => keys.1.pkSeed) same

/-- On each supported deferred whole run the same cap pays for node entries, derivable entries,
routed digest observations and admitted signing requests. Rejected outputs are included. -/
theorem whole_graph_reserve (s : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (caps : Nat × Nat) (fb : (i : LabCommon.Domain) → LabCommon.Range i)
    (out : GuardedFill.Value × Graph)
    (mem : out ∈ support ((simulateQ (slhGraph FIPS205.core s).deferredImpl
      (GuardedFill.labProgram s adv true true caps fb)).run ((∅, ∅), []))) :
    entries s out.2.1.1 + (31 * out.1.2.1 + 32 * out.1.1.1.2.2.1.2 : Nat)
      ≤ (out.1.1.1.2.2.1.1 : ℝ≥0∞) ∧ out.1.1.1.2.2.1 ≤ caps := by
  let initial : State := ((∅, ((0, .keygen), ((∅, ∅), []))), ((0, 0), false))
  let z : Full × State := (out.1.1.1.1, ((out.1.1.2, (out.1.2, out.2)), out.1.1.1.2.2))
  have hz : z ∈ support ((simulateQ (engine s caps fb) (commonSource true s adv)).run initial) := by
    rw [deferred_run_eq_guarded s adv caps fb |>.symm, support_map]
    exact ⟨out, mem, rfl⟩
  have capped := QueryImpl.guardQueryBudget_counts_le_caps caps
    (Sum.elim (fun _ : A.Domain => (0,0)) (policy true s)) (routed s) fb
    (commonSource true s adv) initial.1 z hz
  refine ⟨?_, capped⟩
  have source : commonSource true s adv = (SLHDSA.SHAKE128s.MarkedPrefix.keygenSource s >>= fun k =>
      SLHDSA.SHAKE128s.MarkedPrefix.suffixSource s adv k.1 k.2) := by
    simp only [commonSource, SLHDSA.SHAKE128s.MarkedPrefix.keygenSource,
      SLHDSA.SHAKE128s.MarkedPrefix.suffixSource, SigningView.Events.fullExperiment,
      simulateQ_bind, simulateQ_pure, Prod.eta]
  rw [source, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨mid, first, rest⟩ := hz
  have cold : good s initial := by
    simp [initial, good, entries, CanonicalGraph.NodeKeys.keyEntries, QueryCache.empty_apply]
  have src := SLHDSA.SHAKE128s.MarkedPrefix.keygen_source_private s
  have inv := src.holds_of_mem_support_run_simulateQ
    (good s) (private_input_graph_reserve (caps := caps) (fb := fb)) cold first
  obtain ⟨⟨⟨seed, root⟩, sk⟩, state⟩ := mid
  obtain rfl : seed = s := keygen_seed initial _ first
  exact suffix_graph_reserve root sk adv state inv z rest

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.DeferredReserve

open SLHDSA.SHAKE128s.Bridge.SharedExperiment.DeferredReserve
