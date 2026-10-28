/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.Schemes.BLS.AGM.Adversary
public import VCVio.CryptoFoundations.HardnessAssumptions.DLog11
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.LazyExecution
import VCVio.CryptoFoundations.GroupModel.LinearFunctional.Interaction
import all VCVio.CryptoFoundations.GroupModel.LinearFunctional.LazyCover
import all VCVio.Schemes.BLS.Games
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import VCVio.Schemes.BLS.GameIdentification

/-! # The two straight-line BLS algebraic reductions

This follows Gurkan's linear-functional proof of BLS security in the algebraic group model
of Fuchsbauer, Kiltz and Loss (CRYPTO 2018). Both reductions keep a shared lazy scalar cache
and a chronological list of representations of received inputs. Neither enumerates messages.

The good reduction programs hashes as known multiples of the generator and signs using the
first challenge point. The bad reduction chooses its own signing key and programs each hash
as an independently masked affine function of the challenge. The public-key coefficient enters
the good denominator and the bad numerator because BLS supplies a public key in both source groups.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction

namespace BLS

private def reductionRun {F M G₁ G₂ R V : Type} [Zero F]
    [AddMonoid G₁] [SMul F G₁] [AddMonoid G₂] [SMul F G₂]
    [DecidableEq M] [SampleableType R]
    (A : GroupModel.Interaction.Adversary F (AGM.Group G₁ G₂) Unit
      (AGM.Query M) AGM.Reply M)
    (g₁ : G₁) (g₂ : G₂) (pk : G₁ × G₂) (hash sign : R → G₁)
    (hashRep signRep : R → V) (basis : List V) :
    ProbComp (Explained F M (AGM.Group G₁ G₂) × List V × R) :=
  (simulateQ (M →ₒ R).romImpl
    (GroupModel.LinearFunctional.extractionProgram (fun out => out.value.data)
      hash sign hashRep signRep basis
      (simulateQ (fun q => AGM.oracle q.value)
        (A.main (AGM.initialInput g₁ g₂ pk))))).run' ∅

private def coefficients {F M G₁ G₂ : Type}
    (out : Explained F M (AGM.Group G₁ G₂)) : List F :=
  if (out.value.groups false).isEmpty then [] else (out.coefficients false).headD []

/-- Program every hash as `ρ • g₁`, sign with `ρ • X₁`, and divide the represented constant
by the verification gap. The linear coefficient includes the received public-key point. -/
def goodReduction {F M G₁ G₂ Gₜ : Type} [Field F] [SampleableType F]
    [DecidableEq M] [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F M G₁ G₂ e g₁ g₂) : DLog11.Adversary F G₁ G₂ :=
  fun g X h Y => do
    let (out, basis, target) ← reductionRun A.toAdversary g h (X, Y)
      (fun ρ : F => ρ • g) (fun ρ => ρ • X)
      (fun ρ => (ρ, (0 : F))) (fun ρ => ((0 : F), ρ)) [(1, 0), (0, 1)]
    let repr := evaluate (coefficients out) basis
    return repr.1 / (target - repr.2)

/-- Choose a fresh signing key and program hashes as `a • X₁ + b • g₁`. A zero good-branch
verification gap becomes an affine equation in the challenge scalar; divide its constant
by its slope. Only coefficients on signing replies and the public key enter that equation. -/
def badReduction {F M G₁ G₂ Gₜ : Type} [Field F] [SampleableType F]
    [DecidableEq M] [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F M G₁ G₂ e g₁ g₂) : DLog11.Adversary F G₁ G₂ :=
  fun g X h _ => do
    let κ ← $ᵗ F
    let point := fun r : F × F => r.1 • X + r.2 • g
    let (out, basis, target) ← reductionRun A.toAdversary g h (κ • g, κ • h)
      point (fun r => κ • point r) (fun _ => ((0 : F), (0 : F))) id [(0, 0), (0, 1)]
    let repr := evaluate (coefficients out) basis
    return (repr.2 - target.2) / (target.1 - repr.1)

end BLS

/-! ## Fixed-table algebraic executions -/

open GroupModel.LinearFunctional

namespace BLS.AGM

private def rawMain {F M G₁ G₂ Gₜ : Type} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F M G₁ G₂ e g₁ g₂) (pk : G₁ × G₂) :=
  simulateQ (fun q => oracle q.value) (A.main (initialInput g₁ g₂ pk))

private def received {M G₁ G₂ : Type} (initial : Groups (Group G₁ G₂))
    (hash sign : M → G₁) (tr : Transcript M) : Groups (Group G₁ G₂) :=
  groupInputs (initial false ++ tr.map (fun q => if q.1 then sign q.2 else hash q.2))
    (initial true)

private def fixedPlainOracle {M G₁ G₂ : Type} (hash sign : M → G₁) :
    QueryImpl (plainSpec (Group G₁ G₂) (Query M) Reply) ProbComp := by
  intro ⟨q, _⟩
  rcases q with ((n | m) | m)
  · exact (fun r => ⟨r, groupInputs [] []⟩) <$> (unifSpec.query n : ProbComp _)
  · exact pure ⟨(), groupInputs [hash m] []⟩
  · exact pure ⟨(), groupInputs [sign m] []⟩

private theorem received_empty {M G₁ G₂ : Type} (initial : Groups (Group G₁ G₂))
    (hash sign : M → G₁) : received initial hash sign [] = initial := by
  funext s
  cases s <;> simp [received, groupInputs]

private theorem fixedRun_groups {F M G₁ G₂ Gₜ : Type} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F M G₁ G₂ e g₁ g₂) (pk : G₁ × G₂)
    (hash sign : M → G₁) :
    (fun z => (z.1, received (initialInput g₁ g₂ pk).groups hash sign z.2)) <$>
      fixedRun hash sign (rawMain A pk) =
      A.toAdversary.run (fixedPlainOracle hash sign) (initialInput g₁ g₂ pk) := by
  let input := initialInput g₁ g₂ pk
  let impl₁ := (fixedOracle hash sign) ∘ₛ (fun q => oracle q.value
    : QueryImpl (explainedSpec F (Group G₁ G₂) (Query M) Reply) (OracleComp (rawSpec M G₁)))
  let impl₂ : QueryImpl (explainedSpec F (Group G₁ G₂) (Query M) Reply)
      (StateT (Groups (Group G₁ G₂)) ProbComp) := fun q => StateT.mk fun basis => do
    let reply ← fixedPlainOracle hash sign q.value
    return (reply, extend basis reply.groups)
  have hstep : ∀ q tr, Prod.map id (received input.groups hash sign) <$>
      (impl₁ q).run tr = (impl₂ q).run (received input.groups hash sign tr) := by
    intro ⟨⟨q, groups⟩, coeff⟩ tr
    rcases q with ((n | m) | m) <;>
      simp only [impl₁, impl₂, QueryImpl.apply_compose, oracle, fixedPlainOracle,
        simulateQ_map, simulateQ_spec_query, StateT.run_map, StateT.run_mk,
        bind_pure_comp, Functor.map_map]
    · rw [fixedOracle_run_random]
      change (fun r : Fin (n + 1) =>
          ((⟨r, groupInputs [] []⟩ : Message _ (Group G₁ G₂)),
            received input.groups hash sign tr)) <$> (unifSpec.query n : ProbComp _) =
        (fun r : Fin (n + 1) =>
          ((⟨r, groupInputs [] []⟩ : Message _ (Group G₁ G₂)),
            extend (received input.groups hash sign tr) (groupInputs [] []))) <$>
          (unifSpec.query n : ProbComp _)
      congr 1
      funext r
      apply Prod.ext
      · rfl
      · funext s
        cases s <;> simp [received, groupInputs, extend]
    · rw [fixedOracle_run_hash]
      simp only [map_pure, Prod.map_apply', id_eq]
      apply congrArg pure
      apply Prod.ext
      · rfl
      · funext s
        cases s <;> simp [received, groupInputs, extend, List.append_assoc]
    · rw [fixedOracle_run_sign]
      simp only [map_pure, Prod.map_apply', id_eq]
      apply congrArg pure
      apply Prod.ext
      · rfl
      · funext s
        cases s <;> simp [received, groupInputs, extend, List.append_assoc]
  have h := map_run_simulateQ_eq_of_query_map_eq impl₁ impl₂
    (received input.groups hash sign) hstep (A.main input) []
  rw [received_empty] at h
  simpa only [impl₁, QueryImpl.simulateQ_compose, impl₂, Adversary.run,
    fixedRun, rawMain, input, Prod.map_def, id_eq] using h

private theorem fixedRun_valid {F M G₁ G₂ Gₜ : Type} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F M G₁ G₂ e g₁ g₂) (pk : G₁ × G₂)
    (hash sign : M → G₁) (z : Explained F M (Group G₁ G₂) × Transcript M)
    (hz : z ∈ support (fixedRun hash sign (rawMain A pk))) :
    z.1.Valid (received (initialInput g₁ g₂ pk).groups hash sign z.2) := by
  apply A.toAdversary.run_valid (fixedPlainOracle hash sign) (initialInput g₁ g₂ pk)
    (z.1, received (initialInput g₁ g₂ pk).groups hash sign z.2)
  rw [← fixedRun_groups]
  rw [support_map]
  exact ⟨z, hz, rfl⟩

private theorem valid_head {F M G₁ G₂ : Type} [Semiring F]
    [AddCommMonoid G₁] [Module F G₁] [AddCommMonoid G₂] [Module F G₂]
    (out : Explained F M (Group G₁ G₂)) (inputs : Groups (Group G₁ G₂))
    (h : out.Valid inputs) : evaluate (BLS.coefficients out) (inputs false) = (forgery out).2 := by
  have hv := h false
  cases hg : out.value.groups false with
  | nil => simp [BLS.coefficients, forgery, hg, evaluate, List.mapIdx_eq_ofFn]
  | cons σ rest =>
      cases hc : out.coefficients false with
      | nil => simp [hg, hc] at hv
      | cons c cs =>
          rw [hg, hc] at hv
          have he := (List.forall₂_cons.mp hv).1.2
          simpa [BLS.coefficients, forgery, hg, hc] using he

private theorem fixedRun_good_sound {F M G₁ G₂ Gₜ : Type} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F M G₁ G₂ e g₁ g₂) (κ : F) (ρ : M → F)
    (z : Explained F M (Group G₁ G₂) × Transcript M)
    (hz : z ∈ support (fixedRun (fun m => ρ m • g₁) (fun m => κ • (ρ m • g₁))
      (rawMain A (κ • g₁, κ • g₂)))) :
    let repr := evaluate (BLS.coefficients z.1) ([(1, 0), (0, 1)] ++
      z.2.map (fun q => if q.1 then (0, ρ q.2) else (ρ q.2, 0)))
    (forgery z.1).2 = (repr.1 + repr.2 * κ) • g₁ := by
  let f : (F × F) →ₗ[F] G₁ :=
    (LinearMap.fst F F F).smulRight g₁ + (LinearMap.snd F F F).smulRight (κ • g₁)
  have hv := valid_head z.1 _ (fixedRun_valid A (κ • g₁, κ • g₂) _ _ z hz)
  let basis : List (F × F) := [(1, 0), (0, 1)] ++
    z.2.map (fun q => if q.1 then (0, ρ q.2) else (ρ q.2, 0))
  have hb : (received (initialInput g₁ g₂ (κ • g₁, κ • g₂)).groups
      (fun m => ρ m • g₁) (fun m => κ • (ρ m • g₁)) z.2) false = basis.map f := by
    simp only [received, initialInput, groupInputs, basis, List.map_append, List.map_cons,
      List.map_nil, List.map_map]
    congr 1
    · simp [f]
    · apply List.map_congr_left
      intro q _
      cases hq : q.1 <;> simp [hq, f, smul_smul, mul_comm]
  rw [hb, evaluate_map] at hv
  dsimp only
  rw [← hv]
  simp [f, basis, add_smul, mul_smul]

/-! ## Indexed and chronological execution -/

private def signedMessages {M : Type} (tr : Transcript M) : List M :=
  tr.filterMap (fun q => if q.1 then some q.2 else none)

private def cachedOracle {M R G : Type} [DecidableEq M] [SampleableType R]
    (hash sign : R → G) : QueryImpl (interfaceSpec M G)
      (StateT (List M × (M →ₒ R).QueryCache) ProbComp) := by
  intro q st
  rcases q with ((n | m) | m)
  · exact (fun r => (r, st)) <$> (unifSpec.query n : ProbComp _)
  · exact (fun z => (hash z.1, st.1, z.2)) <$> ((M →ₒ R).randomOracle m).run st.2
  · exact (fun z => (sign z.1, st.1 ++ [m], z.2)) <$> ((M →ₒ R).randomOracle m).run st.2

private theorem indexed_cached_step {M R G : Type} [DecidableEq M] [SampleableType R]
    (hash sign : R → G) (q : (interfaceSpec M G).Domain) (st : OracleState R M) :
    (fun z => (z.1, z.2.signed, valueCache z.2)) <$>
      (indexedOracle (fun _ => $ᵗ R) hash sign none q).run st =
      (cachedOracle hash sign q).run (st.signed, valueCache st) := by
  rcases q with ((n | m) | m)
  · change (fun z => (z.1, z.2.signed, valueCache z.2)) <$>
      ((fun r => (r, st)) <$> (unifSpec.query n : ProbComp _)) = _
    simp only [Functor.map_map, cachedOracle, StateT.run]
    rfl
  · rw [indexedOracle_run_hash]
    simp only [Functor.map_map]
    rw [indexedEntry_signed none m st (fun v c l => (hash v, l, c))]
    have h := congrArg (fun oa => (fun z => (hash z.1, st.signed, z.2)) <$> oa)
      (indexedEntry_valueCache none m st)
    simpa only [Functor.map_map, cachedOracle, StateT.run] using h
  · rw [indexedOracle_run_sign]
    simp only [Functor.map_map]
    change (fun z => (sign z.1.1, z.2.signed ++ [m], valueCache z.2)) <$>
      (indexedEntry (fun _ => $ᵗ R) none m).run st = _
    rw [indexedEntry_signed none m st (fun v c l => (sign v, l ++ [m], c))]
    have h := congrArg (fun oa => (fun z => (sign z.1, st.signed ++ [m], z.2)) <$> oa)
      (indexedEntry_valueCache none m st)
    simpa only [Functor.map_map, cachedOracle, StateT.run] using h

private def cachedTranscriptOracle {M R G : Type} [DecidableEq M] [SampleableType R]
    (hash sign : R → G) : QueryImpl (interfaceSpec M G)
      (StateT (Transcript M × (M →ₒ R).QueryCache) ProbComp) := by
  intro q st
  rcases q with ((n | m) | m)
  · exact (fun r => (r, st)) <$> (unifSpec.query n : ProbComp _)
  · exact (fun z => (hash z.1, st.1 ++ [(false, m)], z.2)) <$>
      ((M →ₒ R).randomOracle m).run st.2
  · exact (fun z => (sign z.1, st.1 ++ [(true, m)], z.2)) <$>
      ((M →ₒ R).randomOracle m).run st.2

private theorem transcript_cached_step {M R G : Type} [DecidableEq M] [SampleableType R]
    (hash sign : R → G) (q : (interfaceSpec M G).Domain)
    (st : Transcript M × (M →ₒ R).QueryCache) :
    Prod.map id (fun s => (signedMessages s.1, s.2)) <$>
      (cachedTranscriptOracle hash sign q).run st =
      (cachedOracle hash sign q).run (signedMessages st.1, st.2) := by
  rcases q with ((n | m) | m) <;>
    simp [cachedTranscriptOracle, cachedOracle, StateT.run, Functor.map_map,
      signedMessages, List.filterMap_append]

private theorem transcript_cached_compose {M R G α : Type}
    [DecidableEq M] [SampleableType R] (hash sign : R → G)
    (oa : OracleComp (interfaceSpec M G) α) (tr : Transcript M) (c : (M →ₒ R).QueryCache) :
    (simulateQ (M →ₒ R).romImpl ((simulateQ (transcriptOracle hash sign) oa).run tr)).run c =
      (fun z => ((z.1, z.2.1), z.2.2)) <$>
        (simulateQ (cachedTranscriptOracle hash sign) oa).run (tr, c) := by
  apply simulateQ_StateT_StateT_compose
  intro q tr c
  rcases q with ((n | m) | m)
  · rw [transcriptOracle_random]
    simp [cachedTranscriptOracle, romImpl, unifFwdImpl, Functor.map_map]
  · rw [transcriptOracle_hash]
    simp [cachedTranscriptOracle, Functor.map_map]
  · rw [transcriptOracle_sign]
    simp [cachedTranscriptOracle, Functor.map_map]

private theorem indexed_transcript {M R G α : Type} [DecidableEq M] [SampleableType R]
    (hash sign : R → G) (oa : OracleComp (interfaceSpec M G) α) :
    (fun z => (z.1, z.2.signed)) <$>
      (simulateQ (indexedOracle (fun _ => $ᵗ R) hash sign none) oa).run OracleState.empty =
      (simulateQ (M →ₒ R).romImpl
        ((fun z => (z.1, signedMessages z.2)) <$>
          (simulateQ (transcriptOracle hash sign) oa).run [])).run' ∅ := by
  have hi := map_run_simulateQ_eq_of_query_map_eq _ _
    (fun st : OracleState R M => (st.signed, valueCache st))
    (indexed_cached_step hash sign) oa OracleState.empty
  have ht := map_run_simulateQ_eq_of_query_map_eq _ _
    (fun st : Transcript M × (M →ₒ R).QueryCache => (signedMessages st.1, st.2))
    (transcript_cached_step hash sign) oa ([], ∅)
  have hempty : (OracleState.empty : OracleState R M).signed = [] := rfl
  have hcache : valueCache (OracleState.empty : OracleState R M) = ∅ := rfl
  simp only [hempty, hcache, signedMessages, List.filterMap_nil] at hi ht
  have he := congrArg (fun p => (fun z => (z.1, z.2.1)) <$> p) (hi.trans ht.symm)
  simp only [Functor.map_map, Prod.map_def, id_eq] at he
  rw [simulateQ_map, StateT.run'_eq, StateT.run_map, transcript_cached_compose]
  simpa only [Functor.map_map, signedMessages] using he

/-! ## Identifying the standard experiment -/

private theorem unforgeableAdvantage_eq_target {F M G₁ G₂ Gₜ : Type}
    [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    [DecidableEq Gₜ] [DecidableEq M]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F M G₁ G₂ e g₁ g₂)
    (hg₁ : Function.Bijective (· • g₁ : F → G₁)) (he : e g₁ g₂ ≠ 0) :
    SignatureAlg.unforgeableAdvantage (ProbCompRuntime.rom (M →ₒ G₁))
      A.toUnforgeableAdversary =
    Pr{let κ ← ($ᵗ F : ProbComp F)
       let z ← (simulateQ (M →ₒ F).romImpl
         (targetProgram (fun out => out.value.data) (· • g₁) (fun ρ => κ • (ρ • g₁))
           (rawMain A (κ • g₁, κ • g₂)))).run' ∅}[
      z.1.value.data ∉ signedMessages z.2.1 ∧ (forgery z.1).2 = κ • (z.2.2 • g₁)] := by
  rw [unforgeableAdvantage_eq_indexed A.toUnforgeableAdversary hg₁ he]
  let : MeasurableSpace F := ⊤
  rw [prEvent_bind_of_discrete, prEvent_bind_of_discrete]
  apply MeasureTheory.lintegral_congr
  intro κ
  have h := indexed_transcript (fun ρ : F => ρ • g₁) (fun ρ => κ • (ρ • g₁))
    (withFinalHash (A.toUnforgeableAdversary.main (κ • g₁, κ • g₂)))
  have hp := congrArg (fun oa => Pr{let z ← oa}[
    z.1.1.1 ∉ z.2 ∧ z.1.1.2 = κ • z.1.2]) h
  simp only [prEvent_map] at hp
  rw [show (fun z => Winning (κ • ·) z) =
      (fun z => z.1.1.1 ∉ z.2.signed ∧ z.1.1.2 = κ • z.1.2) from rfl]
  rw [hp]
  simp only [withFinalHash, AlgebraicAdversary.toUnforgeableAdversary, rawMain,
    targetProgram, bind_map_left, simulateQ_bind, simulateQ_map,
    simulateQ_spec_query, StateT.run_bind, StateT.run_map,
    transcriptOracle_hash, map_bind,
    OracleComp.liftM_map, signedMessages, List.filterMap_append, List.filterMap_cons,
    Bool.false_eq_true, ↓reduceIte, List.filterMap_nil, List.append_nil,
    forgery, prEvent_norm]
  simp only [StateT.run'_eq, StateT.run_bind, StateT.run_map, prEvent_norm]
  rfl

private theorem unforgeableAdvantage_eq_table {F M G₁ G₂ Gₜ : Type}
    [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    [DecidableEq Gₜ] [DecidableEq M]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F M G₁ G₂ e g₁ g₂)
    (hg₁ : Function.Bijective (· • g₁ : F → G₁)) (he : e g₁ g₂ ≠ 0)
    (S : Finset M) (hS : ∀ κ : F, InterfaceCovered S (fun out => out.value.data)
      (rawMain A (κ • g₁, κ • g₂))) :
    SignatureAlg.unforgeableAdvantage (ProbCompRuntime.rom (M →ₒ G₁))
      A.toUnforgeableAdversary =
    Pr{let κ ← ($ᵗ F : ProbComp F); let ρ ← $ᵗ (S → F)
       let z ← fixedRun (fun m => GroupModel.LinearFunctional.extendTable S 0 ρ m • g₁)
         (fun m => κ • (GroupModel.LinearFunctional.extendTable S 0 ρ m • g₁))
         (rawMain A (κ • g₁, κ • g₂))}[
      z.1.value.data ∉ signedMessages z.2 ∧
        (forgery z.1).2 =
          κ • (GroupModel.LinearFunctional.extendTable S 0 ρ z.1.value.data • g₁)] := by
  rw [unforgeableAdvantage_eq_target A hg₁ he]
  let : MeasurableSpace F := ⊤
  rw [prEvent_bind_of_discrete, prEvent_bind_of_discrete]
  apply MeasureTheory.lintegral_congr
  intro κ
  have h := simulateQ_romImpl_evalDistEq_finite_table S _
    (targetProgram_covered S _ (· • g₁) (fun ρ => κ • (ρ • g₁)) _ (hS κ)) (0 : F)
  have hp := h.prEvent_eq (fun z => z.1.value.data ∉ signedMessages z.2.1 ∧
    (forgery z.1).2 = κ • (z.2.2 • g₁))
  simpa only [targetProgram_table, prEvent_norm, Function.comp_def] using hp

private theorem reductionRun_eq_table {F M G₁ G₂ Gₜ R V : Type}
    [Field F] [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    [DecidableEq M] [SampleableType R]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F M G₁ G₂ e g₁ g₂) (pk : G₁ × G₂)
    (hash sign : R → G₁) (hashRep signRep : R → V) (basis : List V)
    (S : Finset M) (hS : InterfaceCovered S (fun out => out.value.data) (rawMain A pk))
    (fallback : R) :
    BLS.reductionRun A.toAdversary g₁ g₂ pk hash sign hashRep signRep basis =ᵈ
      (do let ρ ← $ᵗ (S → R)
          let z ← fixedRun (hash ∘ GroupModel.LinearFunctional.extendTable S fallback ρ)
            (sign ∘ GroupModel.LinearFunctional.extendTable S fallback ρ) (rawMain A pk)
          return (z.1, basis ++ z.2.map (fun q : Bool × M => if q.1 then
            signRep (GroupModel.LinearFunctional.extendTable S fallback ρ q.2) else
              hashRep (GroupModel.LinearFunctional.extendTable S fallback ρ q.2)),
            GroupModel.LinearFunctional.extendTable S fallback ρ z.1.value.data)) := by
  have h := simulateQ_romImpl_evalDistEq_finite_table S _
    (extractionProgram_covered S _ hash sign hashRep signRep basis _ hS) fallback
  simpa only [BLS.reductionRun, rawMain, extractionProgram_table, bind_pure_comp] using h

end BLS.AGM
