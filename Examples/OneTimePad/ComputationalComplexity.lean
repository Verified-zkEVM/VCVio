/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.OneTimePad.Basic
public import VCVio.CryptoFoundations.Asymptotics.PathSemantics
public import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# A fair-coin implementation of the one-time pad

This file gives the one-time pad an explicit random-bit implementation. `coinVector n` is
syntactic `OracleComp coinSpec` code containing one fair-coin query for each of its `n` output
coordinates. Mapping the resulting Boolean function through `bitVecOfFnLE` gives the key
generator `coinBitVec`.

The syntactic and probabilistic claims are kept separate. The query-bound theorem characterizes
the exact number of visible coin queries without interpreting them. The distribution theorems
then show that interpreting those queries as independent fair bits produces exactly the same
uniform `BitVec` law used by `oneTimePad`. The resulting scheme is complete and perfectly secret.

`CoinBitVecFamily.IsPPTByUnder` names the remaining backend-relative uniform-PPT obligation. It is
an instance of VCVio's packed security-family predicate, rather than a pointwise family of
unrelated machines. Constructing it requires executable bounded-iteration machinery from the
chosen quantitative backend; the semantic and exact-query results in this file do not assume such
a machine for free.
-/

@[expose] public section

open OracleSpec OracleComp
open scoped ENNReal
open PFunctor.DynSystem.DynComputation

namespace oneTimePad

/-! ## Explicit fair-bit sampling -/

/-- Sample an `n`-coordinate Boolean function using one explicit `coinSpec` query per coordinate.

The little-endian interpretation is chosen only when this function is mapped to a `BitVec`; the
interaction syntax itself is simply an ordered sequence of independent Boolean queries. -/
def coinVector : (n : ℕ) → OracleComp coinSpec (Fin n → Bool)
  | 0 => pure Fin.elim0
  | n + 1 => do
      let bit ← coin
      let tail ← coinVector n
      pure (Fin.cons bit tail)

/-- Interpret Boolean coordinates as a little-endian fixed-width bit vector. -/
def bitVecOfFnLE {n : ℕ} (bits : Fin n → Bool) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn bits)).cast List.length_ofFn

/-- Reading a coordinate after constructing a little-endian bit vector recovers that coordinate. -/
@[simp]
theorem bitVecOfFnLE_getLsb {n : ℕ} (bits : Fin n → Bool) (index : Fin n) :
    (bitVecOfFnLE bits).getLsb index = bits index := by
  unfold bitVecOfFnLE
  change
    (BitVec.cast List.length_ofFn (BitVec.ofBoolListLE (List.ofFn bits))).getLsbD
      index.val = bits index
  rw [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  simp [List.getD_eq_getElem?_getD, index.isLt]

/-- Interpret an explicitly sampled Boolean vector as a little-endian `BitVec`. -/
def coinBitVec (n : ℕ) : OracleComp coinSpec (BitVec n) :=
  bitVecOfFnLE <$> coinVector n

/-- `bitVecOfFnLE` is injective because every input coordinate can be read back. -/
private theorem bitVecOfFnLE_injective (n : ℕ) :
    Function.Injective (bitVecOfFnLE : (Fin n → Bool) → BitVec n) := by
  intro lhs rhs heq
  funext index
  have hbit := congrArg (fun value : BitVec n ↦ value.getLsb index) heq
  simpa only [bitVecOfFnLE_getLsb] using hbit

/-- `bitVecOfFnLE` is a bijection between Boolean coordinates and fixed-width bit vectors. -/
private theorem bitVecOfFnLE_bijective (n : ℕ) :
    Function.Bijective (bitVecOfFnLE : (Fin n → Bool) → BitVec n) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  exact ⟨bitVecOfFnLE_injective n, by simp⟩

/-! ## Exact syntactic query accounting -/

attribute [local implicit_reducible] PFunctor.FreeM.bind PFunctor.FreeM.map
attribute [local implicit_reducible] PFunctor.FreeM.Path.trace

/-- Relabelling the leaves of a free interaction tree preserves the complete event trace.

`Path.pullMap` supplies the path through the original tree corresponding to a path through its
leaf relabelling. This local bridge lets the exact path argument below look through the maps used
to assemble Boolean vectors and `BitVec`s. -/
private theorem trace_pullMap {P : PFunctor} {α β : Type} (f : α → β) :
    (program : PFunctor.FreeM P α) →
    (path : PFunctor.FreeM.Path (f <$> program)) →
      PFunctor.FreeM.Path.trace (f <$> program) path =
        PFunctor.FreeM.Path.trace program
          (PFunctor.FreeM.Path.pullMap f program path)
  | .pure _, _ => rfl
  | .liftBind position next, ⟨answer, tail⟩ => by
      change
        ⟨position, answer⟩ :: PFunctor.FreeM.Path.trace (f <$> next answer) tail =
          ⟨position, answer⟩ :: PFunctor.FreeM.Path.trace (next answer)
            (PFunctor.FreeM.Path.pullMap f (next answer) tail)
      rw [trace_pullMap f (next answer) tail]

/-- Transporting a typed path along equality of its free interaction trees preserves its erased
event trace. -/
private theorem trace_transport {P : PFunctor} {α : Type}
    {source target : PFunctor.FreeM P α} (h : source = target)
    (path : PFunctor.FreeM.Path source) :
    PFunctor.FreeM.Path.trace source path =
      PFunctor.FreeM.Path.trace target (h ▸ path) := by
  subst target
  rfl

/-- A budget accepts `coinVector n` exactly when it contains at least `n` coin queries.

This is an exact statement about the free interaction syntax. In particular, it is stronger than
merely exhibiting `n` as an upper bound. -/
theorem coinVector_isTotalQueryBound_iff (n budget : ℕ) :
    IsTotalQueryBound (coinVector n) budget ↔ n ≤ budget := by
  induction n generalizing budget with
  | zero =>
      constructor
      · intro _
        exact Nat.zero_le budget
      · intro _
        trivial
  | succ n ih =>
      change (0 < budget ∧ ∀ bit : Bool,
        IsTotalQueryBound
          (coinVector n >>= fun tail ↦
            pure (@Fin.cons n (fun _ ↦ Bool) bit tail))
          (budget - 1)) ↔ n + 1 ≤ budget
      constructor
      · rintro ⟨hbudget, htail⟩
        have hbound : IsTotalQueryBound (coinVector n) (budget - 1) := by
          have hbit := htail false
          rw [bind_pure_comp] at hbit
          exact (isQueryBound_map_iff (coinVector n)
            (@Fin.cons n (fun _ ↦ Bool) false) (budget - 1) _ _).1 hbit
        have := (ih (budget - 1)).1 hbound
        omega
      · intro hbound
        refine ⟨by omega, fun bit ↦ ?_⟩
        have htail : IsTotalQueryBound (coinVector n) (budget - 1) :=
          (ih (budget - 1)).2 (by omega)
        rw [bind_pure_comp]
        exact (isQueryBound_map_iff (coinVector n)
          (@Fin.cons n (fun _ ↦ Bool) bit) (budget - 1) _ _).2 htail

/-- The explicit Boolean-vector sampler has exact total query bound `n`. -/
theorem coinVector_isTotalQueryBound (n : ℕ) :
    IsTotalQueryBound (coinVector n) n :=
  (coinVector_isTotalQueryBound_iff n n).2 le_rfl

/-- Mapping the sampled coordinates to a `BitVec` neither adds nor removes oracle queries. -/
theorem coinBitVec_isTotalQueryBound_iff (n budget : ℕ) :
    IsTotalQueryBound (coinBitVec n) budget ↔ n ≤ budget := by
  unfold coinBitVec IsTotalQueryBound
  rw [isQueryBound_map_iff]
  exact coinVector_isTotalQueryBound_iff n budget

/-- The explicit `BitVec` key generator has exact total query bound `n`. -/
theorem coinBitVec_isTotalQueryBound (n : ℕ) :
    IsTotalQueryBound (coinBitVec n) n :=
  (coinBitVec_isTotalQueryBound_iff n n).2 le_rfl

/-- Every complete typed path through `coinVector n` contains exactly `n` coin queries.

Unlike the total-query-bound theorem, this is a pointwise equality for every possible sequence of
Boolean replies, so it rules out both shorter and longer branches. -/
theorem coinVector_path_trace_length : (n : ℕ) →
    (path : PFunctor.FreeM.Path (coinVector n).toFreeM) →
    (PFunctor.FreeM.Path.trace (coinVector n).toFreeM path).length = n
  | 0, path => by
      have hprogram : (coinVector 0).toFreeM =
          (pure Fin.elim0 : PFunctor.FreeM coinSpec.toPFunctor (Fin 0 → Bool)) := by
        rw [coinVector.eq_def]
      let path' := hprogram ▸ path
      calc
        (PFunctor.FreeM.Path.trace (coinVector 0).toFreeM path).length =
            (PFunctor.FreeM.Path.trace (pure Fin.elim0) path').length := by
          exact congrArg List.length (trace_transport hprogram path)
        _ = 0 := by
          rcases path' with ⟨⟩
          rfl
  | n + 1, path => by
      let explicit : PFunctor.FreeM coinSpec.toPFunctor (Fin (n + 1) → Bool) := do
        let bit ← coin
        let tail ← (coinVector n).toFreeM
        pure (Fin.cons bit tail)
      let branch (bit : Bool) :
          PFunctor.FreeM coinSpec.toPFunctor (Fin (n + 1) → Bool) :=
        (coinVector n).toFreeM >>= fun tail => pure (Fin.cons bit tail)
      let normalized : PFunctor.FreeM coinSpec.toPFunctor (Fin (n + 1) → Bool) :=
        PFunctor.FreeM.liftBind (P := coinSpec.toPFunctor) () fun bit : Bool =>
          PFunctor.FreeM.bind
            (PFunctor.FreeM.map id (PFunctor.FreeM.pure bit)) branch
      have hprogram : (coinVector (n + 1)).toFreeM = explicit := by
        simpa only [explicit] using coinVector.eq_def (n + 1)
      let path' := hprogram ▸ path
      have hnormalized : explicit = normalized := by
        rfl
      let path'' := hnormalized ▸ path'
      calc
        (PFunctor.FreeM.Path.trace (coinVector (n + 1)).toFreeM path).length =
            (PFunctor.FreeM.Path.trace explicit path').length := by
          exact congrArg List.length (trace_transport hprogram path)
        _ = (PFunctor.FreeM.Path.trace normalized path'').length := by
          exact congrArg List.length (trace_transport hnormalized path')
        _ = n + 1 := by
          dsimp only [normalized] at path'' ⊢
          rcases path'' with ⟨bit, tail⟩
          change Bool at bit
          change PFunctor.FreeM.Path
            (PFunctor.FreeM.bind
              (PFunctor.FreeM.map id (PFunctor.FreeM.pure bit)) branch) at tail
          have hchild :
              PFunctor.FreeM.bind
                  (PFunctor.FreeM.map id (PFunctor.FreeM.pure bit)) branch =
                branch bit := by
            rw [PFunctor.FreeM.map_pure]
            rfl
          let branchPath := hchild ▸ tail
          let consBit : (Fin n → Bool) → (Fin (n + 1) → Bool) :=
            @Fin.cons n (fun _ => Bool) bit
          have hbranch : branch bit = consBit <$> (coinVector n).toFreeM := by
            dsimp only [branch]
            rw [PFunctor.FreeM.monad_bind_def]
            change PFunctor.FreeM.bind (coinVector n).toFreeM (pure ∘ consBit) =
              PFunctor.FreeM.map consBit (coinVector n).toFreeM
            exact PFunctor.FreeM.bind_pure_comp consBit (coinVector n).toFreeM
          let mappedPath := hbranch ▸ branchPath
          change
            (PFunctor.FreeM.Path.trace
              (PFunctor.FreeM.bind
                (PFunctor.FreeM.map id (PFunctor.FreeM.pure bit)) branch)
              tail).length + 1 = n + 1
          have hchildTrace :
              (PFunctor.FreeM.Path.trace
                (PFunctor.FreeM.bind
                  (PFunctor.FreeM.map id (PFunctor.FreeM.pure bit)) branch)
                tail).length =
                (PFunctor.FreeM.Path.trace (branch bit) branchPath).length := by
            exact congrArg List.length (trace_transport hchild tail)
          have htrace :
              (PFunctor.FreeM.Path.trace (branch bit) branchPath).length =
                (PFunctor.FreeM.Path.trace
                  (consBit <$> (coinVector n).toFreeM) mappedPath).length := by
            exact congrArg List.length (trace_transport hbranch branchPath)
          rw [hchildTrace, htrace,
            trace_pullMap consBit (coinVector n).toFreeM mappedPath,
            coinVector_path_trace_length n]

/-- Every complete typed path through `coinBitVec n` contains exactly `n` coin queries.

Converting the sampled Boolean coordinates to a `BitVec` only relabels leaves, so its trace is the
trace of the underlying `coinVector`. -/
theorem coinBitVec_path_trace_length (n : ℕ)
    (path : PFunctor.FreeM.Path (coinBitVec n).toFreeM) :
    (PFunctor.FreeM.Path.trace (coinBitVec n).toFreeM path).length = n := by
  let convert : (Fin n → Bool) → BitVec n := bitVecOfFnLE
  let mapped := convert <$> (coinVector n).toFreeM
  have hprogram : (coinBitVec n).toFreeM = mapped := by
    rfl
  let mappedPath := hprogram ▸ path
  calc
    (PFunctor.FreeM.Path.trace (coinBitVec n).toFreeM path).length =
        (PFunctor.FreeM.Path.trace mapped mappedPath).length := by
      exact congrArg List.length (trace_transport hprogram path)
    _ = (PFunctor.FreeM.Path.trace (coinVector n).toFreeM
          (PFunctor.FreeM.Path.pullMap convert (coinVector n).toFreeM mappedPath)).length := by
      exact congrArg List.length
        (trace_pullMap convert (coinVector n).toFreeM mappedPath)
    _ = n := coinVector_path_trace_length n _

/-- The expected length of the typed path sampled from `coinBitVec n` is exactly `n`.

The expectation is therefore a probabilistic corollary of a stronger syntactic fact: its random
variable is pointwise constant on every typed path. -/
theorem expectedQueryCount_coinBitVec_eq (n : ℕ) :
    PFunctor.FreeM.expectedQueryCount (coinBitVec n).toFreeM = (n : ℝ≥0∞) := by
  unfold PFunctor.FreeM.expectedQueryCount
  have hconstant :
      (fun path : PFunctor.FreeM.Path (coinBitVec n).toFreeM =>
          ((PFunctor.FreeM.Path.trace (coinBitVec n).toFreeM path).length : ℝ≥0∞)) =
        fun _ => (n : ℝ≥0∞) := by
    funext path
    exact_mod_cast coinBitVec_path_trace_length n path
  rw [hconstant]
  exact OracleComp.EvalDist.expectedValue_const
    (probFailure_eq_zero (mx := PFunctor.FreeM.withPath (coinBitVec n).toFreeM))
    (n : ℝ≥0∞)

/-- The expected length of the typed path sampled from `coinBitVec n` is at most `n`.

This convenient inequality is the reflexive consequence of the exact expectation theorem. -/
theorem expectedQueryCount_coinBitVec_le (n : ℕ) :
    PFunctor.FreeM.expectedQueryCount (coinBitVec n).toFreeM ≤ (n : ℝ≥0∞) :=
  (expectedQueryCount_coinBitVec_eq n).le

/-! ## Uniform distribution and semantic closing -/

/-- Every Boolean vector has probability `2⁻ⁿ` under the explicit coin sampler. -/
theorem probOutput_coinVector (n : ℕ) (value : Fin n → Bool) :
    Pr[= value | coinVector n] = (2 : ℝ≥0∞)⁻¹ ^ n := by
  induction n with
  | zero =>
      have hvalue : value = Fin.elim0 := funext fun index ↦ index.elim0
      simp [coinVector, hvalue]
  | succ n ih =>
      have hcons : ∀ (bit : Bool) (tail : Fin n → Bool),
          value = Fin.cons bit tail ↔ tail = Fin.tail value ∧ bit = value 0 := by
        intro bit tail
        constructor
        · rintro rfl
          simp
        · rintro ⟨rfl, rfl⟩
          exact (Fin.cons_self_tail value).symm
      rw [coinVector]
      simp only [probOutput_bind_eq_tsum, probOutput_pure, ih, probOutput_coin,
        hcons, ite_and, mul_ite, mul_one, mul_zero, tsum_ite_eq]
      rw [pow_succ']

/-- Explicit independent coin sampling has the canonical uniform Boolean-vector distribution. -/
theorem evalDist_coinVector_eq_uniform (n : ℕ) :
    𝒟[coinVector n] = 𝒟[($ᵗ (Fin n → Bool) : ProbComp (Fin n → Bool))] := by
  apply evalDist_ext
  intro value
  rw [probOutput_coinVector, probOutput_uniformSample]
  simp [ENNReal.inv_pow]

/-- The explicit `n`-coin key generator agrees with canonical uniform `BitVec n` sampling. -/
theorem evalDist_coinBitVec_eq_uniform (n : ℕ) :
    𝒟[coinBitVec n] = 𝒟[($ᵗ BitVec n : ProbComp (BitVec n))] := by
  calc
    𝒟[coinBitVec n] =
        𝒟[bitVecOfFnLE <$> ($ᵗ (Fin n → Bool) : ProbComp (Fin n → Bool))] := by
      rw [coinBitVec, evalDist_map, evalDist_coinVector_eq_uniform, ← evalDist_map]
    _ = 𝒟[($ᵗ BitVec n : ProbComp (BitVec n))] :=
      evalDist_map_bijective_uniform_cross (α := Fin n → Bool) (β := BitVec n)
        bitVecOfFnLE (bitVecOfFnLE_bijective n)

/-- Every key has the canonical uniform probability under explicit coin sampling. -/
theorem probOutput_coinBitVec (n : ℕ) (value : BitVec n) :
    Pr[= value | coinBitVec n] = (Fintype.card (BitVec n) : ℝ≥0∞)⁻¹ := by
  rw [probOutput_def, evalDist_coinBitVec_eq_uniform, ← probOutput_def]
  exact probOutput_uniformSample (BitVec n) value

/-- Every fixed-width key occurs in the support of the explicit coin sampler. -/
@[simp]
theorem support_coinBitVec (n : ℕ) : support (coinBitVec n) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro value
  exact (mem_support_iff_of_evalDist_eq (evalDist_coinBitVec_eq_uniform n) value).2 (by simp)

/-- The concrete semantic handler that answers each `coinSpec` query with a uniform Boolean. -/
def fairCoinImpl : QueryImpl coinSpec ProbComp :=
  uniformSampleImpl

/-- Closing any fair-coin syntax with `fairCoinImpl` preserves its evaluation distribution. -/
@[simp]
theorem evalDist_simulateQ_fairCoinImpl {α : Type} (computation : OracleComp coinSpec α) :
    𝒟[simulateQ fairCoinImpl computation] = 𝒟[computation] := by
  unfold fairCoinImpl
  exact uniformSampleImpl.evalDist_simulateQ (spec := coinSpec) computation

/-- Closing the explicit key generator recovers canonical uniform `BitVec` sampling. -/
theorem evalDist_close_coinBitVec_eq_uniform (n : ℕ) :
    𝒟[simulateQ fairCoinImpl (coinBitVec n)] =
      𝒟[($ᵗ BitVec n : ProbComp (BitVec n))] := by
  rw [evalDist_simulateQ_fairCoinImpl, evalDist_coinBitVec_eq_uniform]

/-! ## One-time pad over the explicit sampler -/

/-- The one-time pad whose key generator uses exactly one explicit fair-coin query per key bit. -/
def coinOneTimePad (sp : ℕ) :
    SymmEncAlg (OracleComp coinSpec) (BitVec sp) (BitVec sp) (BitVec sp) where
  keygen := coinBitVec sp
  encrypt key message := pure (key ^^^ message)
  decrypt key ciphertext := pure (some (key ^^^ ciphertext))

/-- Encryption followed by decryption recovers every message with probability one. -/
theorem coinOneTimePad_complete (sp : ℕ) : (coinOneTimePad sp).Complete := by
  intro message
  have hsimp : (coinOneTimePad sp).CompleteExp message =
      (fun _ : BitVec sp ↦ (some message : Option (BitVec sp))) <$> coinBitVec sp := by
    simp [SymmEncAlg.CompleteExp, coinOneTimePad, monad_norm]
  rw [hsimp]
  simp [probFailure_of_liftM_PMF]

/-- For a fixed message, the explicit-coin and canonical OTP ciphertext laws agree. -/
theorem evalDist_coinOneTimePad_cipherGivenMsg_eq (sp : ℕ) (message : BitVec sp) :
    𝒟[(coinOneTimePad sp).PerfectSecrecyCipherGivenMsgExp message] =
      𝒟[(oneTimePad sp).PerfectSecrecyCipherGivenMsgExp message] := by
  simp only [SymmEncAlg.PerfectSecrecyCipherGivenMsgExp, coinOneTimePad, oneTimePad,
    bind_pure_comp]
  rw [evalDist_map, evalDist_coinBitVec_eq_uniform, ← evalDist_map]

/-- Closing the explicit-coin ciphertext experiment agrees with the canonical OTP experiment. -/
theorem evalDist_close_coinOneTimePad_cipherGivenMsg_eq (sp : ℕ) (message : BitVec sp) :
    𝒟[simulateQ fairCoinImpl
        ((coinOneTimePad sp).PerfectSecrecyCipherGivenMsgExp message)] =
      𝒟[(oneTimePad sp).PerfectSecrecyCipherGivenMsgExp message] := by
  rw [evalDist_simulateQ_fairCoinImpl, evalDist_coinOneTimePad_cipherGivenMsg_eq]

/-- The explicit-coin one-time pad is perfectly secret. -/
theorem coinOneTimePad_perfectSecrecyAt (sp : ℕ) :
    (coinOneTimePad sp).perfectSecrecyAt := by
  apply (coinOneTimePad sp).perfectSecrecyAt_of_uniformKey_of_uniqueKey
    (fun key message ↦ ⟨key ^^^ message, by simp [coinOneTimePad]⟩)
  refine ⟨probOutput_coinBitVec sp, ?_⟩
  intro message ciphertext
  refine ⟨ciphertext ^^^ message, ?_, ?_⟩
  · simp [coinOneTimePad, BitVec.xor_assoc]
  · intro key hkey
    simp only [coinOneTimePad, support_pure, Set.mem_singleton_iff] at hkey
    apply (BitVec.xor_left_inj message).mp
    rw [← hkey.2]
    simp [BitVec.xor_assoc]

/-! ## Uniform strict-PPT boundary -/

/-- The packed security family of explicit-coin OTP key generators. -/
def coinBitVecFamily (n : ℕ) (_ : Unit) : OracleComp coinSpec (BitVec n) :=
  coinBitVec n

namespace CoinBitVecFamily

/-- The exact backend-relative uniform-PPT proposition for `coinBitVecFamily`.

An inhabitant must provide one realization of the packed family and one polynomial bounding all
security parameters and Boolean response paths. Pointwise witnesses do not inhabit this
proposition. -/
def IsPPTByUnder
    {C : PFunctor.StepClass} [C.HasProd] [C.HasSum] [C.HasOption]
    [DecidableEq
      (OracleComp.SecurityFamily.Spec (fun _ : ℕ ↦ coinSpec)).Domain]
    (Q : PFunctor.QuantitativeStepClass C)
    (bd : Boundary C
      (OracleComp.SecurityFamily.Spec (fun _ : ℕ ↦ coinSpec)).toPFunctor
      (OracleComp.SecurityFamily.Input (fun _ : ℕ ↦ Unit))
      (OracleComp.SecurityFamily.Output (fun n : ℕ ↦ BitVec n)))
    {label : Type}
    (contract : OracleComp.Complexity.OracleContract Q bd.interface label) : Prop :=
  OracleComp.Complexity.SecurityFamily.IsCoinPPTByUnder
    Q bd contract coinBitVecFamily

end CoinBitVecFamily

end oneTimePad
