/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.CryptoFoundations.SignatureAlg
public import VCVio.OracleComp.SimSemantics.QueryImpl.Compose
public import VCVio.OracleComp.SimSemantics.WriterT.Core

/-!
# Naturality of the unforgeability experiment

An oracle interpretation `G : QueryImpl spec (OracleComp spec')` acts on a signature scheme over
`spec` by mapping each algorithm through `simulateQ G` (`SignatureAlg.map (simulateQ' G)`), and on
an unforgeability adversary by answering its ambient queries through `G` while passing its
signing queries on unchanged (`UnforgeableAdversary.mapOracles`). The unforgeability experiment
commutes with these actions (`simulateQ_unforgeableExperiment`): interpreting the ambient oracles
of the whole experiment through `G` is the experiment of the interpreted scheme against the
interpreted adversary.

The actions compose (`map_simulateQ'_map_simulateQ'`, `UnforgeableAdversary.mapOracles_mapOracles`)
and the identity interpretation acts trivially (`map_simulateQ'_id'`,
`UnforgeableAdversary.mapOracles_id'`), so the experiment can be re-read through any interpretation
with a left inverse. `SignatureAlg.Tagged` uses this to re-read an experiment with every query
tagged by the party that issued it.

`UnforgeableAdversary` records only its program, not the scheme it indexes, so `mapOracles`
produces an adversary for any scheme over `spec'`; the target scheme is fixed by the context.
-/

public section

open OracleSpec OracleComp

namespace SignatureAlg

variable {ι ι' ι'' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
  {spec'' : OracleSpec ι''} {M PK SK S : Type}

/-! ## Mapping a scheme along composed interpretations -/

/-- Mapping a scheme through `simulateQ` twice is mapping it through the composed handler. -/
lemma map_simulateQ'_map_simulateQ' (G : QueryImpl spec (OracleComp spec'))
    (G' : QueryImpl spec' (OracleComp spec'')) (sigAlg : SignatureAlg (OracleComp spec) M PK SK S) :
    (sigAlg.map (simulateQ' G)).map (simulateQ' G') = sigAlg.map (simulateQ' (G' ∘ₛ G)) := by
  ext <;> simp

/-- Mapping a scheme through the identity handler leaves it unchanged. -/
@[simp]
lemma map_simulateQ'_id' (sigAlg : SignatureAlg (OracleComp spec) M PK SK S) :
    sigAlg.map (simulateQ' (QueryImpl.id' spec)) = sigAlg := by
  ext <;> simp

/-! ## Interpreting the oracles of an adversary -/

/-- The adversary whose ambient queries are answered through `G` and whose signing queries are
passed on unchanged. It is an adversary against any scheme `sigAlg'` over `spec'`. -/
def UnforgeableAdversary.mapOracles (G : QueryImpl spec (OracleComp spec'))
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    {sigAlg' : SignatureAlg (OracleComp spec') M PK SK S}
    (adv : UnforgeableAdversary sigAlg) : UnforgeableAdversary sigAlg' where
  main pk := simulateQ (G.addLift (QueryImpl.id' (M →ₒ S))) (adv.main pk)

namespace UnforgeableAdversary

variable {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
  {sigAlg' : SignatureAlg (OracleComp spec') M PK SK S}
  {sigAlg'' : SignatureAlg (OracleComp spec'') M PK SK S}

@[simp]
lemma mapOracles_main (G : QueryImpl spec (OracleComp spec')) (adv : UnforgeableAdversary sigAlg)
    (pk : PK) :
    (adv.mapOracles G (sigAlg' := sigAlg')).main pk =
      simulateQ (G.addLift (QueryImpl.id' (M →ₒ S))) (adv.main pk) := by
  unfold mapOracles; rfl

/-- Interpreting the oracles of an adversary twice is interpreting them through the composed
handler. -/
lemma mapOracles_mapOracles (G : QueryImpl spec (OracleComp spec'))
    (G' : QueryImpl spec' (OracleComp spec'')) (adv : UnforgeableAdversary sigAlg) :
    (adv.mapOracles G (sigAlg' := sigAlg')).mapOracles G' (sigAlg' := sigAlg'') =
      adv.mapOracles (G' ∘ₛ G) := by
  obtain ⟨main⟩ := adv
  have key : (G'.addLift (QueryImpl.id' (M →ₒ S)) :
      QueryImpl _ (OracleComp (spec'' + (M →ₒ S)))) ∘ₛ
      (G.addLift (QueryImpl.id' (M →ₒ S)) : QueryImpl _ (OracleComp (spec' + (M →ₒ S)))) =
      (G' ∘ₛ G).addLift (QueryImpl.id' (M →ₒ S)) := by
    ext (t | msg) <;>
      simp only [QueryImpl.apply_compose, QueryImpl.addLift_def, QueryImpl.add_apply_inl,
        QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply, QueryImpl.simulateQ_add_liftM_left,
        QueryImpl.simulateQ_add_liftM_right, simulateQ_liftTarget, simulateQ_id']
  unfold mapOracles
  simp only [mk.injEq]
  funext pk
  rw [← QueryImpl.simulateQ_compose, key]

/-- Interpreting the oracles of an adversary through the identity handler leaves it unchanged. -/
@[simp]
lemma mapOracles_id' (adv : UnforgeableAdversary sigAlg) :
    adv.mapOracles (QueryImpl.id' spec) = adv := by
  obtain ⟨main⟩ := adv
  have key : ((QueryImpl.id' spec).addLift (QueryImpl.id' (M →ₒ S)) :
      QueryImpl _ (OracleComp (spec + (M →ₒ S)))) = QueryImpl.id' (spec + (M →ₒ S)) := by
    ext (t | msg) <;> rfl
  unfold mapOracles
  simp only [mk.injEq]
  funext pk
  rw [key, simulateQ_id']

end UnforgeableAdversary

/-! ## Naturality -/

/-- **Naturality of the unforgeability experiment.** Interpreting the ambient oracles of the
experiment through `G` gives the experiment of the scheme mapped through `G` against the adversary
whose ambient oracles are interpreted through `G`. -/
theorem simulateQ_unforgeableExperiment (G : QueryImpl spec (OracleComp spec'))
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S} (adv : UnforgeableAdversary sigAlg) :
    simulateQ G (unforgeableExperiment adv) =
      unforgeableExperiment (sigAlg := sigAlg.map (simulateQ' G)) (adv.mapOracles G) := by
  simp only [unforgeableExperiment, runWithSigningOracle, simulateQ_bind, simulateQ_pure,
    map_keygen, map_verify, UnforgeableAdversary.mapOracles_main]
  refine bind_congr fun kp => ?_
  rw [simulateQ_WriterT_compose (spec.passthrough + sigAlg.signingOracle kp.1 kp.2) G
    ((spec'.passthrough + (sigAlg.map (simulateQ' G)).signingOracle kp.1 kp.2) ∘ₛ
      G.addLift (QueryImpl.id' (M →ₒ S))), QueryImpl.simulateQ_compose]
  rintro (t | msg)
  · simp [QueryImpl.simulateQ_add_liftM_left, writerT_run_simulateQ_liftTarget]
  · simp [QueryImpl.simulateQ_add_liftM_right, signingOracle]

end SignatureAlg
