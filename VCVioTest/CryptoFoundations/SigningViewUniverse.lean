/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.CryptoFoundations.SignatureAlg.CountedExperiment
public import VCVio.OracleComp.EvalDist.Measure
public import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Shared counted execution with type-valued oracle indices

The uniform summand supplies the existing public-randomness lift. The other summand has
small Boolean answers and Type1 indices. No equality, finiteness or smallness of those
indices is required by the runner or the deterministic path interpreter.
-/

public section

open OracleComp OracleSpec SignatureAlg
open scoped ENNReal

universe i r

namespace VCVioTest.CryptoFoundations.SigningViewUniverse

variable {ι : Type i} {spec : OracleSpec.{i, 0} ι}
variable {Request PK SK Sig C : Type} [AddMonoid C]

open Classical in
/-- The ordinary message-freshness observer retains unconditional final verification. -/
private theorem euf_program (policy : SigningView.Event spec Request → C)
    (alg : SignatureAlg (OracleComp spec) Request PK SK Sig)
    (adv : UnforgeableAdversary alg) :
    (fun observed => !observed.rawLog.wasQueried observed.forgery.1 && observed.verified) <$>
      SigningView.countedExperiment policy (SigningView.ofTotal alg) adv.main =
        unforgeableExperiment adv := by
  calc
    _ = (fun outcome : SigningView.Outcome Request Sig Sig =>
        !outcome.rawLog.wasQueried outcome.forgery.1 && outcome.verified) <$>
          (SigningView.erase <$>
            SigningView.countedExperiment policy (SigningView.ofTotal alg) adv.main) := by
      rw [Functor.map_map]
      rfl
    _ = _ := by
      rw [SigningView.countedExperiment_erases]
      simp only [SigningView.experiment, map_bind, map_pure,
        SigningView.ofTotal_runWithSigningOracle, unforgeableExperiment]
      rfl

open Classical in
/-- The original generic inequality is recovered for arbitrary independent runtime carrier. -/
private theorem generic_recovery (policy : SigningView.Event spec Request → C)
    (alg : SignatureAlg (OracleComp spec) Request PK SK Sig)
    (runtime : ProbCompRuntime.{i, r} (OracleComp spec)) (adv : UnforgeableAdversary alg) :
    runtime.evalDist
      ((fun observed => !observed.rawLog.wasQueried observed.forgery.1 && observed.verified) <$>
        SigningView.countedExperiment policy (SigningView.ofTotal alg) adv.main) {true} ≤
      runtime.evalDist
        ((fun observed => decide (SigningView.Wins (SigningView.ofTotal alg).readback
          (SigningView.erase observed))) <$>
          SigningView.countedExperiment policy (SigningView.ofTotal alg) adv.main) {true} := by
  rw [euf_program]
  rw [SigningView.ofTotal_countedWinningProgram policy alg
    (⟨adv.main⟩ : StrongUnforgeableAdversary alg)]
  exact unforgeableAdvantage_le_strongUnforgeableAdvantage runtime adv


section trace

variable {ι : Type 1} {spec : OracleSpec.{1, 1} ι} {m : Type 1 → Type 2} [Monad m]
variable {ω : Type 1} [Monoid ω] (impl : QueryImpl spec m) (cost : spec.Domain → ω)

/-- Old explicit trace parameters mean result/input level1 and monad output level2. -/
private def before : QueryImpl spec (WriterT ω m) := QueryImpl.withTraceBefore.{1, 2} impl cost

/-- The response-dependent trace preserves the same existing universe positions. -/
private def after (observe : (input : spec.Domain) → spec.Range input → ω) :
    QueryImpl spec (WriterT ω m) := QueryImpl.withTrace.{1, 2} impl observe

/-- Old explicit cost applications keep their original diagonal index interpretation. -/
private def costed : QueryImpl spec (WriterT ω m) := QueryImpl.withCost.{1, 2} impl cost

end trace

section append

variable {ι : Type 1} {spec : OracleSpec.{1, 1} ι} {m : Type 1 → Type 2} [Monad m]
variable {ω : Type 1} [EmptyCollection ω] [Append ω] (impl : QueryImpl spec m)

/-- Append-before tracing retains old explicit universe positions. -/
private def appendBefore (cost : spec.Domain → ω) : QueryImpl spec (WriterT ω m) :=
  QueryImpl.withTraceAppendBefore.{1, 2} impl cost

/-- Append-after tracing retains old explicit universe positions. -/
private def appendAfter (cost : (input : spec.Domain) → spec.Range input → ω) :
    QueryImpl spec (WriterT ω m) := QueryImpl.withTraceAppend.{1, 2} impl cost

end append

/-- The old additive wrapper's sole explicit universe controls the monad output. -/
private def additive {ι : Type} {spec : OracleSpec.{0, 0} ι} {m : Type → Type 2} [Monad m]
    {C : Type} [AddMonoid C] (impl : QueryImpl spec m) (cost : spec.Domain → C) :
    QueryImpl spec (AddWriterT C m) := QueryImpl.withAddCost.{2} impl cost

/-- Old explicit event range universes remain independent of its zero index. -/
private def ambient {ι : Type} {spec : OracleSpec.{0, 1} ι} {Request : Type}
    (phase : SignatureAlg.SigningView.Phase) (input : spec.Domain) :
    SignatureAlg.SigningView.Event.{1} spec Request :=
  SignatureAlg.SigningView.Event.ambient.{1} phase input

/-- The recursor keeps its old motive/range parameters and complete event fields. -/
private noncomputable def eventRec {ι : Type} {spec : OracleSpec.{0, 1} ι} {Request : Type}
    (motive : SignatureAlg.SigningView.Event.{1} spec Request → Sort 2)
    (ambientCase : ∀ phase input, motive (.ambient phase input))
    (attemptCase : ∀ request, motive (.signingAttempt request))
    (event : SignatureAlg.SigningView.Event.{1} spec Request) : motive event :=
  SignatureAlg.SigningView.Event.rec.{2, 1} ambientCase attemptCase event


private abbrev LargeBool := Type →ₒ Bool
private abbrev World := unifSpec + LargeBool
private abbrev Cost := FreeAddMonoid (Nat × Nat)

private noncomputable instance : UniformAnswerMeasure LargeBool :=
  UniformAnswerMeasure.ofFiniteNonempty _

private noncomputable def runtime : ProbCompRuntime.{1, 1} (OracleComp World) where
  toSemanticsVia := SemanticsVia.ofEvalDistSemantics (OracleComp World)
  toProbCompLift := ProbCompLift.ofMonadLift (OracleComp World)
  evalDist_map_eq _f hf body := _root_.evalDist_map body hf

/-- The public lift reaches the actual standard uniform summand, rather than ignoring it. -/
private theorem public_lift_query (n : Nat) :
    runtime.liftProbComp (ProbComp.uniformFin n) =
      (liftM (World.query (.inl n)) : OracleComp World (Fin (n + 1))) := rfl

/-- The same canonical measure assigns a ternary uniform answer its exact mass. -/
private theorem uniform_third :
    OracleSpec.AnswerMeasure.toMeasure (spec := World) (.inl 2) {(0 : Fin 3)} =
      (3 : ENNReal)⁻¹ := by
  simpa using (UniformAnswerMeasure.toMeasure_singleton (spec := World) (.inl 2) (0 : Fin 3))

/-- The faithful lifted ternary draw is interpreted by the same canonical runtime. -/
private theorem runtime_uniform_third :
    let : MeasurableSpace (Fin 3) := ⊤
    runtime.evalDist (runtime.liftProbComp (ProbComp.uniformFin 2)) {(0 : Fin 3)} =
      (3 : ENNReal)⁻¹ := by
  let : MeasurableSpace (Fin 3) := ⊤
  change runtime.evalDist (runtime.liftProbComp (ProbComp.uniformFin 2)) {(0 : Fin 3)} = _
  rw [public_lift_query]
  change 𝒟[(liftM (World.query (.inl 2)) : OracleComp World (Fin 3))] {(0 : Fin 3)} = _
  calc
    _ = OracleSpec.AnswerMeasure.toMeasure (spec := World) (.inl 2) {(0 : Fin 3)} :=
      @OracleComp.evalDist_liftM_query_apply (Nat ⊕ Type) World _ (.inl 2)
        ⊤ {(0 : Fin 3)} MeasurableSpace.measurableSet_top
    _ = _ := uniform_third

private def phaseCode : SigningView.Phase → Nat
  | .keygen => 1 | .adversary => 2 | .signer => 3 | .verification => 4

private def policy : SigningView.Event World Nat → Cost
  | .ambient phase (.inl n) => .of (phaseCode phase, 100 + n)
  | .ambient phase (.inr _) => .of (phaseCode phase, 200)
  | .signingAttempt request => .of (5, request)

private def scheme : SignatureAlg (OracleComp World) Nat Nat Nat Nat where
  keygen := do
    let draw ← (liftM (ProbComp.uniformFin 2) : OracleComp World (Fin 3))
    let bit : Bool ← query (spec := LargeBool) Nat
    return (10 + draw.val + (if bit then 1 else 0), 100)
  sign pk sk request := do
    let bit : Bool ← query (spec := LargeBool) Bool
    return pk + sk + request + (if bit then 3 else 5)
  verify _ _ _ := do
    let bit : Bool ← query (spec := LargeBool) (Fin 2)
    return bit

private def adversary : UnforgeableAdversary scheme where
  main _ := do
    let bit : Bool ← query (spec := LargeBool) (List Nat)
    let request := if bit then 1 else 0
    let signature : Nat ← query (spec := Nat →ₒ Nat) request
    return (request, signature + 1)

private def handler : QueryImpl World (StateT (List Nat) Id)
  | .inl n => fun log => pure (⟨0, Nat.zero_lt_succ n⟩, log ++ [100 + n])
  | .inr _ => fun log => pure (true, log ++ [200])

private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)

/-- Execute the actual shared runner with a large index and small payloads and ordered costs. -/
def run : IO Unit := do
  let (observed, log) := (simulateQ handler
    (SigningView.countedExperiment policy (SigningView.ofTotal scheme) adversary.main)).run []
  check (observed.cost.toList ==
    [(1, 102), (1, 200), (2, 200), (5, 1), (3, 200), (4, 200)])
    "large-index chronological noncommutative phase cost"
  check (log == [102, 200, 200, 200, 200]) "actual uniform and type-index backend calls"
  check (decide (observed.rawLog = [⟨1, 115⟩])) "actual supplied key and adaptive signing reply"
  check (observed.forgery == (1, 116) && observed.verified) "actual distinct-signature candidate"
  check (observed.rawLog.wasQueried observed.forgery.1) "ordinary message is not fresh"
  check (!(SigningView.returnedPairs (SigningView.ofTotal scheme).readback
    observed.rawLog).contains observed.forgery) "different-signature pair remains fresh"
  IO.println "Type1-index shared counted runner, faithful uniform lift, \
    and exact ordered cost: PASS"

end VCVioTest.CryptoFoundations.SigningViewUniverse
