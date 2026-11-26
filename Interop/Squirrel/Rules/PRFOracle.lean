/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Squirrel.Rules.PRF
public import Interop.Squirrel.Rules.Oracle
import VCVio.EvalDist.ProbabilityBounds
import VCVio.OracleComp.EvalDist.Measure
import VCVio.OracleComp.Constructions.SampleableType.Measure
import ToMathlib.Data.Nat.Log

/-!
# The hash oracle on the left: PRF.R

CCS26's last PRF rules (Fig. 4) put the hash oracle `o_h^k = λx. h(x, k)` on the left of `⊬`. This
file gives the attacker that oracle as an input answered by a compiled arrow, and proves PRF.R
(App. C.3.2):

```
u⃗, o_h^k ⊬ m    [ψ_key(u⃗, m)]    [ψ_msg^{m,k}(u⃗)]
---------------------------------------------------
                u⃗, o_h^k ⊬ h(m, k)
```

## The oracle as an input

`PRFSymbols.hashOracle` is the term `λx. h(x, k)`; `PRFSymbols.callOracle` is `λx. call x`, a term
with calls that closes up to it. A reduction runs the attacker's machine (`Machine.simulate`) and
answers its first input by `PRFSymbols.arrowIn`: a query `x` Kleisli-applies the compiled reading
of `λx. call x` (`PRFSymbols.kapp`), a free program over the compiled reading's interface whose one
query is the hash of `x` (`PRFSymbols.kapp_callOracle`). Forwarded by `PRFSymbols.fwd`, that query
goes to the PRF game's oracle. The fusion lemma (`PRFSymbols.evalWithAnswerFn_simulate_arrowIn`,
an instance of `Machine.evalWithAnswerFn_simulate`) says that with the keyed hash's answers the run
is the machine's run on the true function `h(·, k)`
(`PRFSymbols.simulateQ_prfRealQueryImpl_simulate_callOracle`), and the attacker's hashes are its
oracle queries (`PRFSymbols.exists_firstArgs_of_hashed`, from VCVio's `mem_runLog_simulateQ`). No
side condition is checked on the oracle: as CCS26 says, it "is handled in an ad hoc way by the
rule".

## The proof of PRF.R

The reductions follow App. C.3.2's hops, with two changes forced or allowed by the setting.

1. **The vector hashes `m`** (the first hop): bounded by `Pr[¬ψ_msg(u⃗)]`, since the compiled
   vector hashes only values of its call arguments (`PRFSymbols.cbvVec_spec`).
2. **The attacker queries `m`** (the second hop, guessing `A₃`'s call): `2 ^ ⌈log₂ q(η)⌉` times
   the success of `AdvMachine.rwGuess` against the premise `u⃗, o_h^k ⊢ m`
   (`prEvent_exists_firstArgs_le`), the uniform guess of Rw-Oracle.
3. **`m` hashed by its own run.** App. C.3.2 isolates `A₂`'s call on `m̃` by guessing it, at a
   factor `q(η)`. Here `m` is a first-order term, so its hashes are values of its call arguments
   (`PRFSymbols.exists_mem_calls_of_hashed`): among `m` and the arguments of its calls, some
   candidate `t` has `m`'s value and is not hashed by its own run (`PRFSymbols.exists_unhashed`).
   There is one reduction per candidate, `PRFSymbols.rightReduction η hmg hh u t g`, and no guess.
4. **The ideal world.** Each reduction runs the vector, then the attacker, then the candidate, and
   queries the oracle at the candidate's value last; it succeeds when the attacker's output is the
   answer and the value was not hashed before. In the ideal world that answer is a fresh draw
   (`PRFSymbols.eq_none_of_mem_support_run`), so the reduction succeeds with probability at most
   `2^{-cη}` for a `large` hash type (`PRFSymbols.prEvent_prfIdealExperiment_rightReduction_le`).
   CCS26's `B` runs the attacker after computing the message; running it first makes the challenge
   the last query.

`PRFSymbols.rightAdvantage_le` is the statement at one `η`; `Valid.nonDed_prfR` is the rule, and
`PRFRInstance` packages its data for derivations.

## References

* [CCS26] Hérouard, Jacomme, Koutsos, Lallemand, *Secrecy in Squirrel and the Post-Compromise
  Security of a Ratchet*, CCS 2026: Fig. 4 and App. C.3.2.
-/

public section

namespace Interop.Squirrel

open IPFunctor IPFunctor.ScopedSignature OracleComp OracleSpec PRFScheme

variable {B : Type} {D : Decl B}

namespace PRFSymbols

variable (P : PRFSymbols D)

/-! ## The hash oracle -/

/-- CCS26's hash oracle `o_h^k = λx. h(x, k)` (Fig. 4), a term of the logic. -/
@[expose] def hashOracle {Γ : List (Kind B)} : FTerm D Γ (.arrow P.msgTy P.hTy) :=
  FTerm.lam (P.hashTerm (Term.var .zero))

/-- The hash oracle as a term with calls, `λx. call x`; closed up, it is `hashOracle`. -/
@[expose] def callOracle {Γ : List (Kind B)} : OTerm P Γ (.arrow P.msgTy P.hTy) :=
  .node (.inl (.lam P.msgTy P.hTy)) fun _ => OTerm.call (Term.var .zero)

theorem close_callOracle {Γ : List (Kind B)} : P.close (P.callOracle (Γ := Γ)) = P.hashOracle :=
  rfl

/-- The hash oracle at `(η, ρ)` hashes its argument under the key of `ρ`. -/
theorem denote_hashOracle {M : Model D} (C : AdvClass M) {Γ : List (Kind B)}
    (env : Env (Kind.Value M) Γ) :
    (P.hashOracle (Γ := Γ)).denote (fullInterp M C) env =
      fun η ρ x => M.fn η P.hOf x (P.keyVal M η ρ.2) := by
  rw [hashOracle, FTerm.denote_lam]
  funext η ρ x
  change M.fn η P.hOf (RV.constAt η x η ρ) (P.keyVal M η ρ.2) = _
  rw [RV.constAt_apply_self]

/-- `λx. call x` is in the `⊢pptm` fragment, for Boolean or base message and hash types. -/
theorem pptm_callOracle {Γ : List (Kind B)} (hmg : P.msgTy.IsGround) (hh : P.hTy.IsGround) :
    P.Pptm (P.callOracle (Γ := Γ)) := by
  intro h hh'
  simp only [callOracle, OTerm.call, Term.heads_node, Term.heads_var, Set.iUnion_empty,
    Set.mem_insert_iff, Set.mem_iUnion, Set.mem_empty_iff_false, or_false,
    exists_const] at hh'
  rcases hh' with rfl | rfl
  · trivial
  · exact ⟨hmg, hh⟩

/-! ## An input answered by a compiled arrow -/

variable (M : Model D) (η : ℕ)

/-- Kleisli application of a compiled closed arrow: run the compiled reading of `o`
(`Interop.Squirrel.Compile`), then apply the Kleisli arrow it returns to `x`. -/
@[expose] noncomputable def kapp {a b : Ty B} (o : OTerm P [] (.arrow a b))
    (x : a.Value M.carrier η) : OracleComp (P.Iface M η) (b.Value M.carrier η) := do
  let f ← o.denoteCBV (P.cbvInterp M η) Env.empty
  M.lower η b <$> f (M.embed η a x)

/-- The input answers of a machine whose first input is the closed arrow `o` and whose other
inputs are the values `e`: a query to the first input is answered by Kleisli-applying the compiled
`o` (`kapp`), so that the hashes it computes become queries of the compiled reading's interface;
the others are answered from `e`. -/
@[expose] noncomputable def arrowIn {a b : Ty B} {Γ : List (Ty B)} (o : OTerm P [] (.arrow a b))
    (e : Vals M η Γ) : InputImpl M η (.arrow a b :: Γ) (OracleComp (P.Iface M η)) :=
  Env.cons (V := fun τ : Ty B => Vals M η τ.args →
      OracleComp (P.Iface M η) (τ.res.Value M.carrier η)) (a := Ty.arrow a b)
    (fun (q : Vals M η (a :: b.args)) =>
      (fun y => Ty.apply (τ := b) y fun _ i => q _ (.succ i)) <$> P.kapp M η o (q _ .zero))
    (InputImpl.ofVals e)

variable {P M η}

/-- Kleisli application of `λx. call x` is one query to the hash. -/
theorem kapp_callOracle (x : P.Dom M η) :
    P.kapp M η P.callOracle x =
      (fun y => M.lower (m := OracleComp (P.Iface M η)) η P.hTy (M.embed η P.hTy y)) <$>
        P.askHash M η
          (M.lower (m := OracleComp (P.Iface M η)) η P.msgTy (M.embed η P.msgTy x)) := by
  simp only [kapp, callOracle, OTerm.call, Term.denoteCBV_node, cbvInterp,
    CBVInterpretation.sum, cbvLocal, cbvCall, Term.denoteCBV_var, pure_bind,
    map_eq_bind_pure_comp, bind_assoc, Function.comp_apply]
  rfl

variable {ρ : M.Tape η} {kv : P.keyTy.Value M.carrier η}

/-- **Adequacy of Kleisli application**: run with the answers of `ρ` and `kv`, the Kleisli
application of a compiled closed arrow of order one returns the arrow's reading at the argument. -/
theorem evalWithAnswerFn_kapp {a b : Ty B} (ha : a.IsGround) (hb : b.IsGround)
    (o : OTerm P [] (.arrow a b)) (ho : P.Pptm o) (x : a.Value M.carrier η) :
    evalWithAnswerFn (P.answer M η ρ kv) (P.kapp M η o x) =
      o.denote (P.ointerp M η ρ kv) Env.empty x := by
  obtain ⟨h₁, -⟩ := denoteCBV_adequate (ρ := ρ) (kv := kv) (e := Env.empty) o ho
    (Env.liftRel_empty _) (M.embed η a x) x
    (crel_embed ((Ty.isGround_iff_order_eq_zero.1 ha).trans_le zero_le_one) x)
  rw [kapp, evalWithAnswerFn_bind, evalWithAnswerFn_map, h₁.lower_eq hb]

/-- The input answers of `arrowIn`, run with the answers of `ρ` and `kv`, answer as the arrow's
reading followed by the values. -/
theorem evalWithAnswerFn_arrowIn {a b : Ty B} {Γ : List (Ty B)} (ha : a.IsGround)
    (hb : b.IsGround) (o : OTerm P [] (.arrow a b)) (ho : P.Pptm o) (e : Vals M η Γ) :
    ∀ τ x q, evalWithAnswerFn (P.answer M η ρ kv) (P.arrowIn M η o e τ x q) =
      Ty.apply (Env.cons (V := Ty.Value M.carrier η) (a := .arrow a b)
        (o.denote (P.ointerp M η ρ kv) Env.empty) e τ x) q
  | _, .zero, q => by
    refine (evalWithAnswerFn_map _ _ _).trans ?_
    rw [evalWithAnswerFn_kapp ha hb o ho]
    rfl
  | _, .succ _, _ => rfl

/-- **Fusion with the hash** (the oracle as an input). A machine whose first input is answered by
the compiled arrow `o`, run with the answers of `ρ` and `kv`, returns its run with `o`'s reading
as its first input. -/
theorem evalWithAnswerFn_simulate_arrowIn {a b β : Ty B} {Γ : List (Ty B)} (ha : a.IsGround)
    (hb : b.IsGround) (o : OTerm P [] (.arrow a b)) (ho : P.Pptm o)
    (gF : Machine M (.arrow a b :: Γ) β) (ρa : M.TapeA η) (e : Vals M η Γ) :
    evalWithAnswerFn (P.answer M η ρ kv) (gF.simulate η ρa (P.arrowIn M η o e)) =
      gF.run η ρa (Env.cons (V := Ty.Value M.carrier η) (a := .arrow a b)
        (o.denote (P.ointerp M η ρ kv) Env.empty) e) :=
  gF.evalWithAnswerFn_simulate (evalWithAnswerFn_arrowIn ha hb o ho e)

/-- **The oracle input in the real world.** In the PRF game's real world, a machine whose first
input `o_h^k` is answered by the compiled `λx. call x`, its hashes forwarded to the PRF oracle,
runs as on the true function `h(·, k)` at the key's sample. -/
theorem simulateQ_prfRealQueryImpl_simulate_callOracle {β : Ty B} {Γ : List (Ty B)}
    (hmg : P.msgTy.IsGround) (hh : P.hTy.IsGround) (kc : M.Coin η P.keyTy)
    (gF : Machine M (.arrow P.msgTy P.hTy :: Γ) β) (ρa : M.TapeA η) (e : Vals M η Γ) :
    simulateQ ((P.scheme M η).prfRealQueryImpl kc)
        (simulateQ (P.fwd M η ρ) (gF.simulate η ρa (P.arrowIn M η P.callOracle e))) =
      pure (gF.run η ρa (Env.cons (fun x => M.fn η P.hOf x (M.sample η P.keyTy kc)) e)) := by
  rw [simulateQ_prfRealQueryImpl_fwd, evalWithAnswerFn_simulate_arrowIn hmg hh _
    (P.pptm_callOracle hmg hh)]
  rfl

/-- **The attacker's hashes are its oracle queries.** Run with any key value, a machine whose first
input is answered by the compiled `λx. call x` hashes only the arguments of its queries to that
input, on its run with the true function. -/
theorem exists_firstArgs_of_hashed {β : Ty B} {Γ : List (Ty B)} (hmg : P.msgTy.IsGround)
    (hh : P.hTy.IsGround) (gF : Machine M (.arrow P.msgTy P.hTy :: Γ) β) (ρa : M.TapeA η)
    (e : Vals M η Γ) {x : P.Dom M η}
    (hx : Sum.inr x ∈ (runLog (P.answer M η ρ kv)
      (gF.simulate η ρa (P.arrowIn M η P.callOracle e))).map (fun e => e.1)) :
    ∃ q ∈ M.firstArgs (runLog (M.answer ρa (Env.cons (fun y => M.fn η P.hOf y kv) e)) (gF η)),
      q _ .zero = x := by
  obtain ⟨ent', hmem, hent⟩ := List.mem_map.1 hx
  obtain ⟨⟨t, r⟩, he, he'⟩ := (mem_runLog_simulateQ _ _ _).1 hmem
  rw [M.evalWithAnswerFn_answerIn (evalWithAnswerFn_arrowIn hmg hh _
    (P.pptm_callOracle hmg hh) e)] at he
  rcases t with i | ⟨τ, z, q⟩
  · change _ ∈ runLog _ (pure _ : OracleComp (P.Iface M η) Bool) at he'
    simp at he'
  · cases z with
    | zero =>
      change _ ∈ runLog _ ((fun y => Ty.apply y fun _ i => q _ (.succ i)) <$>
        P.kapp M η P.callOracle (q _ .zero)) at he'
      rw [runLog_map, kapp_callOracle, runLog_map, askHash, runLog_query,
        List.mem_singleton] at he'
      subst he'
      refine ⟨q, List.mem_filterMap.2 ⟨_, he, rfl⟩, ?_⟩
      exact (M.lower_embed (m := OracleComp (P.Iface M η)) η hmg _).symm.trans
        (Sum.inr.inj hent)
    | succ z =>
      change _ ∈ runLog _ (pure _ : OracleComp (P.Iface M η) (τ.res.Value M.carrier η)) at he'
      simp at he'

/-! ## PRF.R: the reductions -/

variable {τs : List (Ty B)} {β : Ty B}

variable (P M η) in
/-- The program of PRF.R's reductions for a candidate message `t`: compile the vector `u⃗`; run
the attacker machine `gF`, its first input `o_h^k` answered by the compiled `λx. call x`
(`arrowIn`) and the others by the vector's values; then compile `t`. CCS26's `B` (App. C.3.2)
computes the message before running the attacker; here the attacker runs first, so that in the
ideal world the challenge is the last query. -/
@[expose] noncomputable def rightProg (hmg : P.msgTy.IsGround) (u : OVec P [] τs)
    (t : OTerm P [] P.msgTy) (gF : Machine M (.arrow P.msgTy P.hTy :: (τs ++ P.msgTy.args)) β)
    (ρa : M.TapeA η) : OracleComp (P.Iface M η) (β.Value M.carrier η × P.Dom M η) := do
  let e ← P.cbvVec M η u
  let y ← gF.simulate η ρa (P.arrowIn M η P.callOracle (Env.append e (Ty.groundArgs hmg)))
  let x ← t.denoteCBV (P.cbvInterp M η) Env.empty
  pure (y, M.lower η P.msgTy x)

variable (η) in
/-- **The reduction of PRF.R** for a candidate message `t` (CCS26 App. C.3.2): draw both tapes;
run `rightProg`, logging its queries, with its hashes forwarded to the PRF oracle (`fwd`); query
the oracle at `t`'s value; and return whether the attacker's output is that answer, unless `t`'s
value was hashed before. -/
@[expose] noncomputable def rightReduction (hmg : P.msgTy.IsGround) (hh : P.hTy.IsGround)
    (u : OVec P [] τs) (t : OTerm P [] P.msgTy)
    (g : AdvMachine M (τs ++ [.arrow P.msgTy P.hTy]) P.hTy) :
    PRFAdversary (P.Dom M η) (P.Rng M η) :=
  (do
    let ρ ← liftComp ($ᵗ (M.Tape η)) (PRFOracleSpec (P.Dom M η) (P.Rng M η))
    let r ← simulateQ (P.fwd M η ρ)
      (rightProg P M η hmg u t (g.withOracleFirst hh) ρ.1).withQueryLog
    let z ← functionQuery r.1.2
    pure (@decide (Ty.ofRes hh r.1.1 = z) (Classical.propDecidable _) &&
      !(@QueryLog.wasQueried _ _ (Classical.decEq _) r.2 (Sum.inr r.1.2))) :
    OracleComp (PRFOracleSpec (P.Dom M η) (P.Rng M η)) Bool)

/-- The result and the query log of PRF.R's program, run with the answers of the tapes `ρ` and
hashes keyed by `kv`. -/
@[expose] noncomputable def rightRun (hmg : P.msgTy.IsGround) (hh : P.hTy.IsGround)
    (u : OVec P [] τs) (t : OTerm P [] P.msgTy)
    (g : AdvMachine M (τs ++ [.arrow P.msgTy P.hTy]) P.hTy) (ρ : M.Tape η)
    (kv : P.keyTy.Value M.carrier η) :
    (P.hTy.res.Value M.carrier η × P.Dom M η) × QueryLog (P.Iface M η) :=
  evalWithAnswerFn (P.answer M η ρ kv)
    (rightProg P M η hmg u t (g.withOracleFirst hh) ρ.1).withQueryLog

/-- The outcome of PRF.R's reduction in the real world, at the tapes `ρ` and the key value `kv`:
the attacker's output is the hash of `t`'s value, and that value was not hashed before. -/
@[expose] noncomputable def rightOutcome (hmg : P.msgTy.IsGround) (hh : P.hTy.IsGround)
    (u : OVec P [] τs) (t : OTerm P [] P.msgTy)
    (g : AdvMachine M (τs ++ [.arrow P.msgTy P.hTy]) P.hTy) (ρ : M.Tape η)
    (kv : P.keyTy.Value M.carrier η) : Bool :=
  @decide (Ty.ofRes hh (rightRun hmg hh u t g ρ kv).1.1 =
      M.fn η P.hOf (rightRun hmg hh u t g ρ kv).1.2 kv) (Classical.propDecidable _) &&
    !(@QueryLog.wasQueried _ _ (Classical.decEq _) (rightRun hmg hh u t g ρ kv).2
      (Sum.inr (rightRun hmg hh u t g ρ kv).1.2))

variable (hmg : P.msgTy.IsGround) (hh : P.hTy.IsGround) (u : OVec P [] τs)
  (t : OTerm P [] P.msgTy) (g : AdvMachine M (τs ++ [.arrow P.msgTy P.hTy]) P.hTy)

/-- The run of PRF.R's program with the answers of `ρ` and `kv`: the attacker's run on the vector's
compiled values and the true function `h(·, kv)`, and `t`'s compiled value; its log is the logs of
the three parts. -/
theorem rightRun_eq (ρ : M.Tape η) (kv : P.keyTy.Value M.carrier η) :
    rightRun hmg hh u t g ρ kv =
      (((g.withOracleFirst hh).run η ρ.1 (Env.cons (fun x => M.fn η P.hOf x kv)
          (Env.append (evalWithAnswerFn (P.answer M η ρ kv) (P.cbvVec M η u))
            (Ty.groundArgs hmg))),
        M.lower η P.msgTy (evalWithAnswerFn (P.answer M η ρ kv)
          (t.denoteCBV (P.cbvInterp M η) Env.empty))),
        runLog (P.answer M η ρ kv) (P.cbvVec M η u) ++
          (runLog (P.answer M η ρ kv) ((g.withOracleFirst hh).simulate η ρ.1
            (P.arrowIn M η P.callOracle (Env.append
              (evalWithAnswerFn (P.answer M η ρ kv) (P.cbvVec M η u)) (Ty.groundArgs hmg)))) ++
          (runLog (P.answer M η ρ kv) (t.denoteCBV (P.cbvInterp M η) Env.empty) ++ []))) := by
  rw [rightRun, evalWithAnswerFn_withQueryLog]
  simp only [rightProg, evalWithAnswerFn_bind, evalWithAnswerFn_pure, runLog_bind, runLog_pure,
    evalWithAnswerFn_simulate_arrowIn hmg hh _ (P.pptm_callOracle hmg hh)]
  rfl

/-- **PRF.R's reduction in the real world** draws the key and both tapes and computes the
outcome with the keyed hash. -/
theorem prEvent_prfRealExperiment_rightReduction :
    Pr{let b ← (P.scheme M η).prfRealExperiment (rightReduction η hmg hh u t g)}[b = true] =
      Pr{let kc ← $ᵗ (M.Coin η P.keyTy); let ρ ← $ᵗ (M.Tape η)}[
        rightOutcome hmg hh u t g ρ (M.sample η P.keyTy kc) = true] := by
  simp only [prfRealExperiment, rightReduction, simulateQ_bind, simulateQ_map,
    simulateQ_prfRealQueryImpl_liftComp, simulateQ_prfRealQueryImpl_fwd, pure_bind, map_pure,
    simulateQ_prfRealQueryImpl_functionQuery, prEvent_norm]
  rfl

/-- **PRF.R's reduction in the ideal world.** Against a lazily sampled random function whose
values are drawn by the sampler of the hash type, the reduction succeeds with probability at most
a bound `ε` on each value of that sampler: where `t`'s value was not hashed before, the challenge
is a fresh draw (`eq_none_of_mem_support_run`), independent of the attacker's output. -/
theorem prEvent_prfIdealExperiment_rightReduction_le [DecidableEq (P.Dom M η)]
    [SampleableType (P.Rng M η)]
    (hsel : ($ᵗ (P.Rng M η)) = M.sample η P.hTy <$> ($ᵗ (M.Coin η P.hTy))) {ε : ENNReal}
    (hε : ∀ y, Pr{let r ← $ᵗ (M.Coin η P.hTy)}[M.sample η P.hTy r = y] ≤ ε) :
    Pr{let b ← prfIdealExperiment (rightReduction η hmg hh u t g)}[b = true] ≤ ε := by
  simp only [prfIdealExperiment, rightReduction, simulateQ_bind,
    simulateQ_prfIdealQueryImpl_liftComp, StateT.run'_liftM_bind]
  refine prEvent_bind_le_of_forall_le _ _ _ fun ρ => ?_
  simp only [StateT.run'_eq, StateT.run_bind, simulateQ_pure,
    simulateQ_prfIdealQueryImpl_functionQuery, Functor.map_map]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun p hp => ?_
  by_cases hb : (@QueryLog.wasQueried _ _ (Classical.decEq _) p.1.2 (Sum.inr p.1.1.2)) = true
  · simp [hb]
  · have hnone := eq_none_of_mem_support_run ρ _ ∅ p hp p.1.1.2 rfl fun h => hb (by
      rw [@QueryLog.wasQueried_eq_decide_mem_map_fst _ _ (Classical.decEq _)]
      simpa using h)
    simp only [randomOracle.run_eq, hnone, hsel, StateT.run_pure, prEvent_norm]
    refine le_trans (prEvent_mono _ _ _ fun c hc => ?_) (hε (Ty.ofRes hh p.1.1.1))
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact hc.1.symm

/-! ## The key's coordinate overwritten -/

section Update

variable [DecidableEq (M.Slot η)]

/-- With the key's coordinate overwritten, the key is read from its new coin. -/
theorem keyVal_update (ρh : M.TapeH η) (kc : M.Coin η P.keyTy) :
    P.keyVal M η (Function.update ρh (P.keySlot M η) kc) = M.sample η P.keyTy kc := by
  change M.sample η P.keyTy (Function.update ρh (P.keySlot M η) kc (P.keySlot M η)) = _
  rw [Function.update_self]

/-- A closed term with calls, without the key name, means at the tapes `ρ` with the key's
coordinate overwritten by `kc` its reading at `ρ` with the key value of `kc`. -/
theorem close_apply_update (C : AdvClass M) (env : Env (Kind.Value M) []) {τ : Ty B}
    (t : OTerm P [] τ) (hk : P.KeyFree t) (kc : M.Coin η P.keyTy) (ρ : M.Tape η) :
    (P.close t).denote (fullInterp M C) env η (ρ.1, Function.update ρ.2 (P.keySlot M η) kc) =
      t.denote (P.ointerp M η ρ (M.sample η P.keyTy kc)) Env.empty := by
  rw [denote_close_apply, keyVal_update]
  exact congrFun (ointerp_eq_of_keyFree (fun k hk => Function.update_of_ne
    (fun h => hk (congrArg Sigma.fst h)) _ _) _ t hk) _

/-- A closed vector with calls, without the key name, at the tapes `ρ` with the key's coordinate
overwritten by `kc`: the readings of its entries at `ρ` with the key value of `kc`. -/
theorem closeVec_rv_apply_update (C : AdvClass M) (env : Env (Kind.Value M) [])
    {τs : List (Ty B)} (u : OVec P [] τs) (hku : ∀ τ x, P.KeyFree (u τ x))
    (kc : M.Coin η P.keyTy) (ρ : M.Tape η) :
    (P.closeVec u).rv M C env η (ρ.1, Function.update ρ.2 (P.keySlot M η) kc) =
      fun τ x => (u τ x).denote (P.ointerp M η ρ (M.sample η P.keyTy kc)) Env.empty :=
  funext fun τ => funext fun x => close_apply_update C env (u τ x) (hku τ x) kc ρ

/-- The hash oracle at the tapes `ρ` with the key's coordinate overwritten by `kc` is the keyed
hash under the key value of `kc`. -/
theorem hashOracle_apply_update (C : AdvClass M) (env : Env (Kind.Value M) [])
    (kc : M.Coin η P.keyTy) (ρ : M.Tape η) :
    (P.hashOracle (Γ := [])).denote (fullInterp M C) env η
        (ρ.1, Function.update ρ.2 (P.keySlot M η) kc) =
      fun x => M.fn η P.hOf x (M.sample η P.keyTy kc) := by
  simp only [denote_hashOracle, keyVal_update]

end Update

/-! ## PRF.R at one security parameter -/

/-- **The attacker's win is a reduction's outcome.** At the tapes `ρ` with the key's coordinate
overwritten by `kc`: if `g` computes `h(m, k)` from `u⃗, o_h^k`, `ψ_msg(u⃗)` holds, and `g` does
not query its oracle at `m`, then for the candidate `t` of `exists_unhashed` the outcome of
`rightReduction` is `true`. -/
private theorem exists_rightOutcome [DecidableEq (M.Slot η)] (m : OTerm P [] P.msgTy)
    (hg : ∀ τ ∈ τs, τ.IsGround) (hku : ∀ τ x, P.KeyFree (u τ x)) (hkm : P.KeyFree m)
    (hpu : ∀ τ x, P.Pptm (u τ x)) (hpm : P.Pptm m) (hfu : ∀ τ x, P.FirstOrder (u τ x))
    (hfm : P.FirstOrder m) (C : AdvClass M) (env : Env (Kind.Value M) [])
    (kc : M.Coin η P.keyTy) (ρ : M.Tape η)
    (hW : Ty.appVals (g.eval η ρ.1) (VecRV.snoc ((P.closeVec u).rv M C env)
        ((P.hashOracle (Γ := [])).denote (fullInterp M C) env) η
        (ρ.1, Function.update ρ.2 (P.keySlot M η) kc)) =
      (P.hashTerm (P.close m)).denote (fullInterp M C) env η
        (ρ.1, Function.update ρ.2 (P.keySlot M η) kc))
    (hψ : (P.psiMsgVec u m).denote (fullInterp M C) env η
      (ρ.1, Function.update ρ.2 (P.keySlot M η) kc) = true)
    (hA : ∀ x ∈ M.firstArgs (runLog (M.answer ρ.1 (Env.cons
        (fun y => M.fn η P.hOf y (M.sample η P.keyTy kc)) (Env.append
          (fun τ x => (u τ x).denote (P.ointerp M η ρ (M.sample η P.keyTy kc)) Env.empty)
          (Ty.groundArgs hmg)))) ((g.withOracleFirst hh) η)),
      x _ .zero ≠ m.denote (P.ointerp M η ρ (M.sample η P.keyTy kc)) Env.empty) :
    ∃ t ∈ m :: P.calls m, rightOutcome hmg hh u t g ρ (M.sample η P.keyTy kc) = true := by
  set kv := M.sample η P.keyTy kc
  set xm := m.denote (P.ointerp M η ρ kv) Env.empty
  have hagree : ∀ k : M.Slot η, k.1 ≠ P.keyName →
      Function.update ρ.2 (P.keySlot M η) kc k = ρ.2 k :=
    fun k hk => Function.update_of_ne (fun h => hk (congrArg Sigma.fst h)) _ _
  obtain ⟨heu, -⟩ := cbvVec_spec (ρ := ρ) (kv := kv) (fun _ => True) u hg hpu
    (fun τ x => snd_denote_guardInterp_true _ _)
  obtain ⟨t, ht, htm, htlog⟩ := exists_unhashed (ρ := ρ) (kv := kv) m hpm hfm
  have hpt : P.Pptm t := by
    rcases List.mem_cons.1 ht with rfl | h
    · exact hpm
    · exact (heads_subset_of_mem_calls m t h).trans hpm
  -- Where `ψ_msg(u⃗)` holds, the vector's run does not hash `m`.
  have hq : ∀ τ x, ((u τ x).denote (P.guardInterp ρ kv fun y => y ≠ xm)
      (pairEnv Env.empty)).2 := by
    intro τ x
    rw [psiMsgVec_eq_true_iff, keyVal_update] at hψ
    rw [snd_denote_guardInterp_iff _ _ (hfu τ x)]
    intro t' ht'
    have h := hψ t' (mem_vecCalls.2 ⟨τ, x, ht'⟩)
    rwa [congrFun (ointerp_eq_of_keyFree hagree kv t'
        ((heads_subset_of_mem_calls _ t' ht').trans (hku τ x))) Env.empty,
      congrFun (ointerp_eq_of_keyFree hagree kv m hkm) Env.empty] at h
  obtain ⟨-, hok⟩ := cbvVec_spec (ρ := ρ) (kv := kv) (fun y => y ≠ xm) u hg hpu hq
  refine ⟨t, ht, ?_⟩
  rw [rightOutcome, rightRun_eq, heu, lower_evalWithAnswerFn_denoteCBV hmg t hpt, htm]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
  refine ⟨?_, ?_⟩
  · change Ty.appVals (g.eval η ρ.1) (Env.append (Vec.rv M C (P.closeVec u) env η _)
      (Env.cons ((P.hashOracle (Γ := [])).denote (fullInterp M C) env η _) Env.empty)) =
        M.fn η P.hOf ((P.close m).denote (fullInterp M C) env η _)
          (P.keyVal M η (Function.update ρ.2 (P.keySlot M η) kc)) at hW
    rwa [AdvMachine.appVals_eval_eq_withOracleFirst hmg hh, hashOracle_apply_update,
      close_apply_update C env m hkm, keyVal_update, closeVec_rv_apply_update C env u hku] at hW
  · rw [@QueryLog.wasQueried_eq_decide_mem_map_fst _ _ (Classical.decEq _),
      decide_eq_false_iff_not]
    simp only [List.map_append, List.mem_append, not_or, List.append_nil]
    refine ⟨fun hx => hok xm hx rfl, fun hx => ?_, htlog⟩
    obtain ⟨q', hq', hq'x⟩ := exists_firstArgs_of_hashed hmg hh (g.withOracleFirst hh) ρ.1 _ hx
    exact hA q' hq' hq'x

/-- **PRF.R at `η`** (CCS26 Fig. 4 and App. C.3.2). Let `g` be an attacker machine against
`u⃗, o_h^k ⊢ h(m, k)` that reads the attacker tape below `p` and makes at most `q` input queries,
with `u⃗` and `m` reading the tape below `p`. At an `η` where `⌈log₂ q(η)⌉` bits from `p(η)` fit
on the tape, and `ε` bounds each value of the sampler of the hash type, `g`'s success is at most

* the probability that `ψ_msg(u⃗)` fails (`psiMsgVec`): the vector hashes `m`;
* `2 ^ ⌈log₂ q(η)⌉` times the success of the guessing reduction `AdvMachine.rwGuess` against
  `u⃗, o_h^k ⊢ m`: `g` queries its oracle at `m`;
* for each candidate `t` among `m` and the arguments of its calls, the PRF advantage of
  `rightReduction η hmg hh u t g` plus `ε`: some candidate has `m`'s value and is not hashed by its
  own run (`exists_unhashed`), and its reduction succeeds; in the ideal world its challenge is a
  fresh draw. -/
theorem rightAdvantage_le (hU : M.UniformSampler P.hTy) (m : OTerm P [] P.msgTy)
    (hg : ∀ τ ∈ τs, τ.IsGround) (hku : ∀ τ x, P.KeyFree (u τ x)) (hkm : P.KeyFree m)
    (hpu : ∀ τ x, P.Pptm (u τ x)) (hpm : P.Pptm m) (hfu : ∀ τ x, P.FirstOrder (u τ x))
    (hfm : P.FirstOrder m) (C : AdvClass M) (env : Env (Kind.Value M) []) {p q : Polynomial ℕ}
    (hpg : Machine.ReadsBelow g fun η => p.eval η) (hqg : Machine.QueryBound g fun η => q.eval η)
    (hru : ((P.closeVec u).rv M C env).ReadsBelow fun η => p.eval η)
    (hrm : ((P.close m).denote (fullInterp M C) env).ReadsBelow fun η => p.eval η)
    (hη : p.eval η + Nat.clog 2 (q.eval η) ≤ M.lenA η) {ε : ENNReal}
    (hε : ∀ y, Pr{let r ← $ᵗ (M.Coin η P.hTy)}[M.sample η P.hTy r = y] ≤ ε) :
    deduceAdv g.eval (Vec.rv M C (Vec.snoc (P.closeVec u) P.hashOracle) env)
        ((P.hashTerm (P.close m)).denote (fullInterp M C) env) η ≤
      Pr{let ρ ← $ᵗ (M.Tape η)}[(P.psiMsgVec u m).denote (fullInterp M C) env η ρ = false] +
        2 ^ Nat.clog 2 (q.eval η) * deduceAdv (g.rwGuess p q hmg hh).eval
          (Vec.rv M C (Vec.snoc (P.closeVec u) P.hashOracle) env)
          ((P.close m).denote (fullInterp M C) env) η +
        ((m :: P.calls m).map fun t =>
          P.prfAdv M η hU (rightReduction η hmg hh u t g) + ε).sum := by
  classical
  have := D.finite_names
  have : ∀ n : (a : Ty B) × (b : Ty B) × D.Name a b, Finite (n.1.Value M.carrier η) :=
    fun n => M.finite_index η n.2.2
  set U := (P.closeVec u).rv M C env
  set O := (P.hashOracle (Γ := [])).denote (fullInterp M C) env
  set Mv := (P.close m).denote (fullInterp M C) env
  have hO : O = fun η ρ x => M.fn η P.hOf x (P.keyVal M η ρ.2) := P.denote_hashOracle C env
  rw [Vec.rv_snoc]
  let W : M.Tape η → Prop := fun ρ => Ty.appVals (g.eval η ρ.1) (VecRV.snoc U O η ρ) =
    (P.hashTerm (P.close m)).denote (fullInterp M C) env η ρ
  let BadU : M.Tape η → Prop := fun ρ => (P.psiMsgVec u m).denote (fullInterp M C) env η ρ = false
  let BadA : M.Tape η → Prop := fun ρ => ∃ x ∈ M.firstArgs (runLog (M.answer ρ.1 (Env.cons (O η ρ)
      (Env.append (U η ρ) (Ty.groundArgs hmg)))) ((g.withOracleFirst hh) η)), x _ .zero = Mv η ρ
  -- **The attacker queries `m`**: the guessing bound against the premise.
  have hA : Pr{let ρ ← $ᵗ (M.Tape η)}[BadA ρ] ≤ 2 ^ Nat.clog 2 (q.eval η) *
      deduceAdv (g.rwGuess p q hmg hh).eval (VecRV.snoc U O) Mv η :=
    prEvent_exists_firstArgs_le hmg hh g U hpg hqg O (fun η ρ x => x = Mv η ρ) hru
      (fun η ρa ρa' ρh _ => by rw [hO])
      (fun η ρa ρa' ρh x hρ hx => hx.trans (hrm η ρa ρa' ρh hρ)) hη
  -- **The remaining event**, at the reduction's tapes with the key's coordinate overwritten.
  let T : ProbComp (M.Coin η P.keyTy × M.Tape η) := do
    let kc ← $ᵗ (M.Coin η P.keyTy)
    let ρ ← $ᵗ (M.Tape η)
    pure (kc, ρ)
  have hT : ∀ r : M.Coin η P.keyTy → M.Tape η → Prop,
      Pr{let kc ← $ᵗ (M.Coin η P.keyTy); let ρ ← $ᵗ (M.Tape η)}[r kc ρ] =
        Pr{let x ← T}[r x.1 x.2] := fun r => by
    simp only [T, prEvent_norm]
  have hmain : Pr{let ρ ← $ᵗ (M.Tape η)}[W ρ ∧ ¬ BadU ρ ∧ ¬ BadA ρ] ≤
      ((m :: P.calls m).map fun t =>
        P.prfAdv M η hU (rightReduction η hmg hh u t g) + ε).sum := by
    rw [← SampleableType.prEvent_uniformSample_prod_update (β := M.TapeA η)
      (R := fun k : M.Slot η => M.Coin η k.1.2.1) (P.keySlot M η), hT]
    refine (prEvent_mono T _ (fun x => ∃ t ∈ m :: P.calls m,
      rightOutcome hmg hh u t g x.2 (M.sample η P.keyTy x.1) = true) fun x hx => ?_).trans
        ((prEvent_exists_list_le _ T _).trans ?_)
    · obtain ⟨hW, hBU, hBA⟩ := hx
      refine exists_rightOutcome hmg hh u g m hg hku hkm hpu hpm hfu hfm C env x.1 x.2 hW
        (Bool.not_eq_false _ ▸ hBU) fun y hy hyx => hBA ⟨y, ?_, ?_⟩
      · rwa [show O η _ = _ from hashOracle_apply_update C env x.1 x.2,
          show U η _ = _ from closeVec_rv_apply_update C env u hku x.1 x.2]
      · rw [show Mv η _ = _ from close_apply_update C env m hkm x.1 x.2]
        exact hyx
    refine List.sum_le_sum fun t _ => ?_
    rw [← hT fun kc ρ => rightOutcome hmg hh u t g ρ (M.sample η P.keyTy kc) = true,
      ← prEvent_prfRealExperiment_rightReduction]
    refine (ENNReal.absDiff_le_iff.1 (le_of_eq (prfAdv_eq hU _).symm)).1.trans ?_
    rw [add_comm]
    exact add_le_add le_rfl (@prEvent_prfIdealExperiment_rightReduction_le _ _ P M η _ hmg hh u t g
      (Classical.decEq _) (M.uniformSampler P.hTy hU η) rfl _ hε)
  calc Pr{let ρ ← $ᵗ (M.Tape η)}[W ρ]
      ≤ Pr{let ρ ← $ᵗ (M.Tape η)}[BadU ρ ∨ BadA ρ] +
          Pr{let ρ ← $ᵗ (M.Tape η)}[W ρ ∧ ¬ (BadU ρ ∨ BadA ρ)] :=
        prEvent_le_prEvent_add_prEvent_and_not _ _ _
    _ ≤ (Pr{let ρ ← $ᵗ (M.Tape η)}[BadU ρ] + Pr{let ρ ← $ᵗ (M.Tape η)}[BadA ρ]) +
          Pr{let ρ ← $ᵗ (M.Tape η)}[W ρ ∧ ¬ BadU ρ ∧ ¬ BadA ρ] :=
        add_le_add (prEvent_or_le _ _ _) (le_of_eq (prEvent_congr _ _ _ fun _ =>
          ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, fun h => h₂ (.inl h), fun h => h₂ (.inr h)⟩,
            fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, fun h => h.elim h₂ h₃⟩⟩))
    _ ≤ _ := add_le_add (add_le_add le_rfl hA) hmain

end PRFSymbols

/-! ## PRF.R -/

namespace Valid

variable {R : Model D → Prop} {C : ∀ M : Model D, AdvClass M} {τs : List (Ty B)}

/-- **PRF.R** (CCS26 Fig. 4 and App. C.3.2), with the hash oracle `o_h^k = λx. h(x, k)` on the
left:

```
u⃗, o_h^k ⊬ m    [ψ_key(u⃗, m)]    [ψ_msg^{m,k}(u⃗)]
---------------------------------------------------
                u⃗, o_h^k ⊬ h(m, k)
```

for a closed vector `u⃗` and message `m` given as terms with calls, closed up.

* `ψ_key` (`hku`, `hkm`), `⊢pptm` (`hpu`, `hpm`) and first order (`hfu`, `hfm`), with entries of
  Boolean or base type and Boolean or base message and hash types; the hash type is `large`.
* `[ψ_msg^{m,k}(u⃗)]` (`hmsg`, `PRFSymbols.psiMsgVec`): the calls of `u⃗` are not on `m`. As in
  CCS26, it is not asked of `m` itself, so `m` may be hashed to compute `m`, and no condition is
  checked on the oracle: it is handled by the rule.
* In every model of `R`: names of the hash type are uniform, the attacker tapes are long, and
  messages have polynomial bit blocks (the default of the guessing reduction); in every admitted
  model of `Θ` the terms read the attacker tape below a polynomial.
* `hprf` is the PRF assumption, on the named reductions `PRFSymbols.rightReduction η hmg hh u t g`
  of each admitted machine `g`, one for each candidate `t` among `m` and the arguments of its
  calls: their PRF advantages (`PRFSymbols.prfAdv`) are negligible.

At every large `η`, for `g` reading the tape below `p` and making at most `q` input queries,
`deduceAdv g (u⃗, o_h^k) (h(m, k)) η ≤ Pr[ψ_msg(u⃗) = false] +
  2 ^ ⌈log₂ q(η)⌉ · deduceAdv (rwGuess g) (u⃗, o_h^k) m η +
  Σ_t (prfAdv (rightReduction η hmg hh u t g) + 2^{-cη})`
(`PRFSymbols.rightAdvantage_le`). -/
theorem nonDed_prfR (P : PRFSymbols D) {Θ : List (Form D [])} (u : OVec P [] τs)
    (m : OTerm P [] P.msgTy) {ho : Ty.SecrecyOrder (τs ++ [.arrow P.msgTy P.hTy]) P.hTy}
    {ho' : Ty.SecrecyOrder (τs ++ [.arrow P.msgTy P.hTy]) P.msgTy} (hg : ∀ τ ∈ τs, τ.IsGround)
    (hmg : P.msgTy.IsGround) (hh : P.hTy.IsGround) (hlarge : P.hTy.HasLabel D.labels .large)
    (hku : ∀ τ x, P.KeyFree (u τ x)) (hkm : P.KeyFree m) (hpu : ∀ τ x, P.Pptm (u τ x))
    (hpm : P.Pptm m) (hfu : ∀ τ x, P.FirstOrder (u τ x)) (hfm : P.FirstOrder m)
    (hR : ∀ M, R M → M.UniformSampler P.hTy ∧ M.LongTapes ∧ M.PolyCoins P.msgTy)
    (hread : ∀ M : Model D, M.RespectsLabels → R M → ∀ env, (∀ θ ∈ Θ, θ.Holds M (C M) env) →
      Vec.ReadsPoly M (C M) (P.closeVec u) env ∧ FTerm.ReadsPoly M (C M) (P.close m) env)
    (hprf : ∀ M : Model D, M.RespectsLabels → R M → ∀ hU : M.UniformSampler P.hTy,
      ∀ g : AdvMachine M (τs ++ [.arrow P.msgTy P.hTy]) P.hTy, (C M).mem g →
        ∀ t ∈ m :: P.calls m,
          negligible (fun η => P.prfAdv M η hU (P.rightReduction η hmg hh u t g)))
    (hmsg : Valid R C Θ (.box (P.psiMsgVec u m)))
    (h : Valid R C Θ (.nonDed (Vec.snoc (P.closeVec u) P.hashOracle) (P.close m) ho')) :
    Valid R C Θ (.nonDed (Vec.snoc (P.closeVec u) P.hashOracle) (P.hashTerm (P.close m)) ho) := by
  intro M hl hRM env hΘ
  obtain ⟨hU, hlong, hc⟩ := hR M hRM
  obtain ⟨hru, pm, hpm'⟩ := hread M hl hRM env hΘ
  obtain ⟨pu, hpu'⟩ := hru.exists_readsBelow
  obtain ⟨c, hcpos, hle⟩ := M.isLarge_of_hasLabel hl hlarge
  have hbox := Form.holds_box.1 (hmsg M hl hRM env hΘ)
  have h' := Form.holds_nonDed.1 (h M hl hRM env hΘ)
  refine Form.holds_nonDed.2 fun g hgm => ?_
  obtain ⟨pg, hpg⟩ := (C M).readBound_mem hgm
  obtain ⟨qg, hqg⟩ := (C M).queryBound_mem hgm
  set p := pg + pu + pm
  have hle' : ∀ {r : Polynomial ℕ}, (r = pg ∨ r = pu ∨ r = pm) → ∀ η, r.eval η ≤ p.eval η := by
    rintro r (rfl | rfl | rfl) η <;> simp only [p, Polynomial.eval_add] <;> omega
  have hguess := h' _ ((C M).rwGuess_mem p qg hmg hh hc hgm)
  have hsum := negligible_list_sum (L := m :: P.calls m)
    (f := fun t η => P.prfAdv M η hU (P.rightReduction η hmg hh u t g) +
      (2 : ENNReal) ^ (-(c * η)))
    fun t ht => negligible_add (hprf M hl hRM hU g hgm t ht) (negligible_two_rpow_neg_mul hcpos)
  refine negligible_of_eventuallyLE ?_ (negligible_add (negligible_add hbox
    (negligible_polynomial_mul hguess (2 * qg + 1))) hsum)
  filter_upwards [hlong (p + qg)] with η hη
  have hη' : p.eval η + Nat.clog 2 (qg.eval η) ≤ M.lenA η := by
    have := Nat.clog_le_of_le_pow (b := 2) (Nat.lt_two_pow_self (n := qg.eval η)).le
    simp only [Polynomial.eval_add] at hη
    omega
  have hfac : (2 : ENNReal) ^ Nat.clog 2 (qg.eval η) ≤ ((2 * qg + 1).eval η : ℕ) := by
    have := Nat.pow_clog_le_mul_add_one 2 (qg.eval η)
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
      Polynomial.eval_ofNat]
    exact_mod_cast this
  refine (P.rightAdvantage_le hmg hh u g hU m hg hku hkm hpu hpm hfu hfm (C M) env
    (hpg.mono (hle' (.inl rfl))) hqg (fun τ x => (hpu' τ x).mono (hle' (.inr (.inl rfl))))
    (hpm'.mono (hle' (.inr (.inr rfl)))) hη' (hle η)).trans ?_
  exact add_le_add (add_le_add le_rfl (mul_le_mul' hfac le_rfl)) le_rfl

end Valid

/-! ## Instances, for derivations -/

/-- An instance of PRF.R: the keyed hash, a closed vector and a message with calls, with Boolean
or base message and hash types, which the reductions use, and the order bounds of the premise and
the conclusion. -/
structure PRFRInstance (D : Decl B) where
  /-- The keyed hash. -/
  P : PRFSymbols D
  /-- The types of the vector. -/
  τs : List (Ty B)
  /-- The vector, with calls. -/
  u : OVec P [] τs
  /-- The message, with calls. -/
  m : OTerm P [] P.msgTy
  /-- Messages are Boolean or base. -/
  hmg : P.msgTy.IsGround
  /-- Hashes are Boolean or base. -/
  hh : P.hTy.IsGround
  /-- The conclusion has order at most one. -/
  order : Ty.SecrecyOrder (τs ++ [.arrow P.msgTy P.hTy]) P.hTy
  /-- The premise has order at most one. -/
  orderM : Ty.SecrecyOrder (τs ++ [.arrow P.msgTy P.hTy]) P.msgTy

namespace PRFRInstance

variable (e : PRFRInstance D)

/-- The syntactic side conditions of PRF.R: entries of Boolean or base type, a `large` hash type,
`ψ_key`, `⊢pptm` and first order. -/
@[expose] def Syntactic : Prop :=
  (∀ τ ∈ e.τs, τ.IsGround) ∧ e.P.hTy.HasLabel D.labels .large ∧
    (∀ τ x, e.P.KeyFree (e.u τ x)) ∧ e.P.KeyFree e.m ∧ (∀ τ x, e.P.Pptm (e.u τ x)) ∧
    e.P.Pptm e.m ∧ (∀ τ x, e.P.FirstOrder (e.u τ x)) ∧ e.P.FirstOrder e.m

/-- The PRF assumption of PRF.R: in every model of `R`, the named reductions
`PRFSymbols.rightReduction` of every admitted machine, one for each candidate, have negligible PRF
advantage. -/
@[expose] def Holds (R : Model D → Prop) (C : ∀ M : Model D, AdvClass M) : Prop :=
  ∀ M : Model D, M.RespectsLabels → R M → ∀ hU : M.UniformSampler e.P.hTy,
    ∀ g : AdvMachine M (e.τs ++ [.arrow e.P.msgTy e.P.hTy]) e.P.hTy, (C M).mem g →
      ∀ t ∈ e.m :: e.P.calls e.m,
        negligible (fun η => e.P.prfAdv M η hU (e.P.rightReduction η e.hmg e.hh e.u t g))

/-- The left side of PRF.R, `u⃗, o_h^k`. -/
@[expose] def lhs : Vec D [] (e.τs ++ [.arrow e.P.msgTy e.P.hTy]) :=
  Vec.snoc (e.P.closeVec e.u) e.P.hashOracle

/-- PRF.R at an instance. -/
theorem valid {R : Model D → Prop} {C : ∀ M : Model D, AdvClass M} {Θ : List (Form D [])}
    (hs : e.Syntactic) (hh : e.Holds R C)
    (hR : ∀ M, R M → M.UniformSampler e.P.hTy ∧ M.LongTapes ∧ M.PolyCoins e.P.msgTy)
    (hread : ∀ M : Model D, M.RespectsLabels → R M → ∀ env, (∀ θ ∈ Θ, θ.Holds M (C M) env) →
      Vec.ReadsPoly M (C M) (e.P.closeVec e.u) env ∧ FTerm.ReadsPoly M (C M) (e.P.close e.m) env)
    (hmsg : Valid R C Θ (.box (e.P.psiMsgVec e.u e.m)))
    (h : Valid R C Θ (.nonDed e.lhs (e.P.close e.m) e.orderM)) :
    Valid R C Θ (.nonDed e.lhs (e.P.hashTerm (e.P.close e.m)) e.order) :=
  let ⟨hg, hlarge, hku, hkm, hpu, hpm, hfu, hfm⟩ := hs
  Valid.nonDed_prfR e.P e.u e.m hg e.hmg e.hh hlarge hku hkm hpu hpm hfu hfm hR hread hh hmsg h

end PRFRInstance

end Interop.Squirrel
