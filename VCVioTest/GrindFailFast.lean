/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio

/-!
# Fail-fast and opt-in gates for `grind` on probability goals

Companion to the probability benchmarks (`VCVioTest/ProbabilityTactics.lean`,
`VCVioTest/MonadProbability.lean`, `VCVioTest/LongChainPrograms.lean`), which gate what
`grind` *solves*. This file gates the other half of the design: what `grind` deliberately does
**not** solve, and that it fails **fast** when it doesn't.

Each support characterization kept out of the default `grind` set gets one example of the form

```
example : <the lemma's own statement> := by
  fail_if_success grind   -- the lemma is really out of the default set
  grind [<the lemma>]     -- and the documented opt-in really closes the goal
```

The gate is loud in both failure directions:

* If someone tags one of these lemmas `@[grind]`, bare `grind` starts *succeeding* on its statement
  and `fail_if_success` fails the build.
* If a change to the default set makes bare `grind` *saturate* instead of failing fast on one of
  these statements, the resulting `(deterministic) timeout` is a runtime exception that escapes
  `fail_if_success` and fails the build. The unbounded support quantifiers in these statements are
  why they stay opt-in.
-/

public section

open OracleComp ProbComp ENNReal

namespace VCVioTest.GrindFailFast

/-! ## Support characterizations under uniform answers

Bare `grind` must fail (fast); the documented opt-in `grind [<lemma>]` must close the goal. -/

section uniform

variable {ι : Type} {spec : OracleSpec ι} [OracleSpec.UniformAnswerMeasure spec] {α : Type}
  (p : α → Prop) (mx : OracleComp spec α) (x : α)

example : Pr{let y ← mx}[p y] = 0 ↔ ∀ y ∈ support mx, ¬ p y := by
  fail_if_success grind
  grind [OracleComp.prEvent_eq_zero_iff]

example : Pr{let y ← mx}[p y] ≠ 0 ↔ ∃ y ∈ support mx, p y := by
  fail_if_success grind
  grind [OracleComp.prEvent_eq_zero_iff]

example : 0 < Pr{let y ← mx}[p y] ↔ ∃ y ∈ support mx, p y := by
  fail_if_success grind
  grind [OracleComp.prEvent_pos_iff]

example : Pr{let y ← mx}[p y] = 1 ↔ ∀ y ∈ support mx, p y := by
  fail_if_success grind
  grind [OracleComp.prEvent_eq_one_iff]

example : 1 = Pr{let y ← mx}[p y] ↔ ∀ y ∈ support mx, p y := by
  fail_if_success grind
  grind [OracleComp.prEvent_eq_one_iff]

example : Pr{let y ← mx}[y = x] = 1 ↔ ∀ y ∈ support mx, y = x := by
  fail_if_success grind
  grind [OracleComp.prEvent_eq_one_iff]

-- mirror: `mem_support_bind_iff` is a default `grind` rule.
example (my : α → OracleComp spec α) (y : α) :
    y ∈ support (mx >>= my) ↔ ∃ z ∈ support mx, y ∈ support (my z) := by grind

end uniform

/-! ## `finSupport` gates and `ProbComp` mirrors -/

section probComp

variable (p : Bool → Prop) [DecidablePred p] (mx : ProbComp Bool)

example : Pr{let y ← mx}[p y] = 0 ↔ ∀ y ∈ finSupport mx, ¬ p y := by
  fail_if_success grind
  grind [OracleComp.prEvent_eq_zero_iff]

-- mirror: the kept `finSupport` bind rule closes this under bare `grind`
example (my : Bool → ProbComp Bool) (y : Bool) :
    y ∈ finSupport (mx >>= my) ↔ ∃ z ∈ finSupport mx, y ∈ finSupport (my z) := by grind

end probComp

/-! ## Structural additions to the default `grind` set

Capability gates for the confluent structural rewrites tagged `@[grind =]` beyond the original
monad-law block: `replicate` unfolds, `Functor.map_map`, and the `simulateQ` routing layer
(`QueryImpl.add` / instrumentation wrappers). Each example is a shape bare `grind` could not close
before the corresponding tag (the routing example previously *saturated* — it is also a fail-fast
gate). -/

section structural

variable (oa : ProbComp Bool)

example : oa.replicate 1 = (do let x ← oa; pure [x]) := by grind
example (x : Bool) : (pure x : ProbComp Bool).replicate 3 = pure [x, x, x] := by grind
example (xs : List Bool) : xs ∈ support (oa.replicate 0) ↔ xs = [] := by grind
example : oa.replicateTR 1 = (do let x ← oa; pure [x]) := by grind

section mapMap

variable {α : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m]

example (mx : m α) (f g : α → α) : g <$> (f <$> mx) = (fun x => g (f x)) <$> mx := by grind
example (mx : m α) (f g : α → α) :
    Pr{let _ ← g <$> (f <$> mx)}[True] = Pr{let _ ← mx}[True] := by grind

end mapMap

section routing

variable {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {α β σ : Type}
  {m : Type → Type} [Monad m] [LawfulMonad m]
  (impl₁ : QueryImpl spec₁ m) (impl₂ : QueryImpl spec₂ m)

-- formerly a saturating shape: bare `grind` timed out here before
-- `simulateQ_add_liftComp_left` was tagged `@[grind =]`
example (oa : OracleComp spec₁ α) :
    simulateQ (impl₁ + impl₂) (do let x ← liftComp oa (spec₁ + spec₂); pure x) =
      simulateQ impl₁ oa := by grind

example (ob : OracleComp spec₂ α) :
    simulateQ (impl₁ + impl₂) (liftComp ob (spec₁ + spec₂) >>= pure) =
      simulateQ impl₂ ob := by grind

example (impl : QueryImpl spec₁ (StateT σ m)) (t : spec₁.Domain) (s : σ) (b : Bool) :
    (impl.withBadFlag t).run (s, b) =
      (fun (vs : spec₁.Range t × σ) => (vs.1, vs.2, b)) <$> (impl t).run s := by grind

example (impl : QueryImpl spec₁ m) (x : Option α) (my : OracleComp spec₁ β)
    (my' : α → OracleComp spec₁ β) :
    simulateQ impl (x.elim my my' >>= pure) =
      x.elim (simulateQ impl my) (fun a => simulateQ impl (my' a)) := by grind

end routing

end structural

end VCVioTest.GrindFailFast

/-! ## Shared construction interface simplification gates -/

open OracleComp OracleSpec SignatureAlg
universe reuseU reuseV reuseW reuseIdx

namespace VCVioTest.GrindFailFast

section writerMaps
variable {m : Type reuseU → Type reuseV} [Monad m] [LawfulMonad m]
variable {ω τ α : Type reuseU} [Monoid ω] [Monoid τ]

example (f : ω →* τ) (body : WriterT ω m α) :
    (WriterT.mapOutputHom f body).run = Prod.map id f <$> body.run := by simp

end writerMaps

section costMaps
variable {m : Type reuseU → Type reuseV} [Monad m] [LawfulMonad m]
variable {C D α : Type reuseU} [AddMonoid C] [AddMonoid D]

example (f : C →+ D) (body : AddWriterT C m α) :
    (AddWriterT.mapCostHom f body).runAdd = Prod.map id f <$> body.runAdd := by simp

end costMaps

example {m : Type reuseU → Type reuseV} {n : Type reuseU → Type reuseW} [Monad m] [Monad n]
    [LawfulMonad m] [LawfulMonad n] {ω α : Type reuseU} [EmptyCollection ω] [Append ω]
    (morphism : m →ᵐ n) (body : WriterT ω m α) :
    (WriterT.mapBaseAppendHom morphism body).run = morphism body.run := by simp

example {ι : Type reuseIdx} {spec : OracleSpec.{reuseIdx, 0} ι} {Request C α : Type}
    [AddMonoid C] (policy : SigningView.Event spec Request → C)
    (phase : SigningView.Phase) (value : α) :
    SigningView.costed policy phase (pure value) = pure value := by simp

example {Request Sig Reply : Type} (readback : Reply → Option Sig)
    (firstLog secondLog : QueryLog (Request →ₒ Reply)) :
    SigningView.returnedPairs readback (firstLog ++ secondLog) =
      SigningView.returnedPairs readback firstLog ++
        SigningView.returnedPairs readback secondLog := by
  simp

example {ι : Type reuseIdx} {spec : OracleSpec.{reuseIdx, 0} ι} {Request PK SK Sig Reply α : Type}
    (view : SigningView (OracleComp spec) Request PK SK Sig Reply)
    (pk : PK) (sk : SK) (value : α) :
    view.runWithSigningOracle pk sk (pure value) = pure (value, []) := by simp

section rejectingEncoding
variable {m : Type → Type reuseV} [Monad m]
variable {Request Msg PK SK Sig WireSig : Type}
variable (alg : SignatureAlg m Msg PK SK Sig) (frame : Request → Option Msg)
variable (encode : Sig → WireSig) (decode : WireSig → Option Sig)

example : (SigningView.rejectingEncoding alg frame encode decode).keygen = alg.keygen := by simp

example (pk : PK) (sk : SK) (request : Request) :
    (SigningView.rejectingEncoding alg frame encode decode).sign pk sk request =
      match frame request with
      | none => pure none
      | some message => (some ∘ encode) <$> alg.sign pk sk message :=
  SigningView.rejectingEncoding_sign alg frame encode decode pk sk request

example (pk : PK) (request : Request) (wire : WireSig) :
    (SigningView.rejectingEncoding alg frame encode decode).verify pk request wire =
      match frame request with
      | none => pure false
      | some message => match decode wire with
        | none => pure false
        | some signature => alg.verify pk message signature :=
  SigningView.rejectingEncoding_verify alg frame encode decode pk request wire

example (pk : PK) (sk : SK) (request : Request) (hFrame : frame request = none) :
    (SigningView.rejectingEncoding alg frame encode decode).sign pk sk request = pure none := by
  simp [hFrame]

example (pk : PK) (sk : SK) (request : Request) (message : Msg)
    (hFrame : frame request = some message) :
    (SigningView.rejectingEncoding alg frame encode decode).sign pk sk request =
      (some ∘ encode) <$> alg.sign pk sk message := by simp [hFrame]

example (pk : PK) (request : Request) (wire : WireSig) (hFrame : frame request = none) :
    (SigningView.rejectingEncoding alg frame encode decode).verify pk request wire =
      pure false := by
  simp [hFrame]

example (pk : PK) (request : Request) (wire : WireSig) (message : Msg)
    (hFrame : frame request = some message) (hDecode : decode wire = none) :
    (SigningView.rejectingEncoding alg frame encode decode).verify pk request wire =
      pure false := by
  simp [hFrame, hDecode]

example (pk : PK) (request : Request) (wire : WireSig) (message : Msg) (signature : Sig)
    (hFrame : frame request = some message) (hDecode : decode wire = some signature) :
    (SigningView.rejectingEncoding alg frame encode decode).verify pk request wire =
      alg.verify pk message signature := by simp [hFrame, hDecode]

example : (SigningView.rejectingEncoding alg frame encode decode).readback = id := by simp

end rejectingEncoding

section answerMaps
variable {ι : Type reuseU} {R S : OracleSpec.{reuseU, reuseV} ι}

example (f : ∀ input, R input → S input) (cache : R.QueryCache) (input : ι) :
    QueryCache.mapAnswers f cache input = (cache input).map (f input) := by simp

example (e : ∀ input, R input ≃ S input) :
    QueryLog.mapAnswers e ([] : QueryLog R) = [] := by simp

example (e : ∀ input, R input ≃ S input) (input : ι) (answer : R input) :
    QueryLog.mapAnswers e [⟨input, answer⟩] = [⟨input, (e input) answer⟩] := by simp

example (e : ∀ input, R input ≃ S input) (input : ι) :
    QueryImpl.relabel e input =
      (e input).symm <$> (liftM (S.query input) : OracleComp S (S input)) := by simp

-- Requires the documented production tag @[simp, grind =] on QueryImpl.relabel_apply.

example (e : ∀ input, R input ≃ S input) (input : ι) :
    QueryImpl.relabel e input =
      (e input).symm <$> (liftM (S.query input) : OracleComp S (S input)) := by grind

end answerMaps

end VCVioTest.GrindFailFast
