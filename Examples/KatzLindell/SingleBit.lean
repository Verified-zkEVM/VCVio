/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Examples.KatzLindell.PrivKEav
import ToMathlib.Data.BitVec
import VCVio.OracleComp.Coinductive.PolyTimeClosure

/-!
# Katz–Lindell Claim 3.11: Single-Bit Unpredictability

If a private-key scheme has indistinguishable encryptions in the presence of an
eavesdropper, then no probabilistic polynomial-time adversary can predict the `i`-th bit
of a uniformly random plaintext from its encryption with probability non-negligibly
better than `1/2` (Katz and Lindell, *Introduction to Modern Cryptography*, Claim 3.11).

The proof follows the book's reduction, with the probability core sharpened to an exact
equality of experiments:

* `predictExp` is the bit-prediction experiment; out-of-range bit indices read as `0`
  via `BitVec.getLsbD`, matching the book's convention.
* `reduceAdv` is the reduction adversary `A′`: its choose phase (`chooseProg`) samples
  two uniform messages with bit `i` overwritten by `0` resp. `1`, coin by coin; its
  distinguish phase forwards the given predictor's output bit.
* `probOutput_uniformSample_bitVec_bind_getLsbD` is the uniform-split identity: reading
  bit `i` of a uniform bitvector is the same as sampling the bit separately and
  overwriting (the change of variables `BitVec.involutive_overwriteBit_pair`).
* `probOutput_predictExp_eq_eavExp_reduceAdvIdeal` is the master identity
  `Pr[A predicts bit i] = Pr[PrivK^eav with A′] `, exactly (the book's
  `1/2 + ε` bookkeeping follows by taking biases).
* `secureAgainst_predictBitGame_of_eavSecure` assembles **Claim 3.11** through
  `SecurityGame.secureAgainst_of_close_reduction`: the reduction is exact for `i < n`
  and the finitely many parameters `n ≤ i` are absorbed into the negligible slack; the
  "`A′` is PPT since `A` is" step is `OracleComp.IsPolyTime.precomp` for the
  distinguish phase and the sampler machine for the choose phase.

Two supporting facts are deferred with `sorry`, each isolated and consumed only through
its statement:

* `evalDist_simulateQ_chooseProg`: the coin-by-coin sampler computes the specification
  sampler `chooseIdeal` (proof plan: induction on the coin-fill recursion showing the
  accumulator's filled bits are uniform, then the `BitVec.extractLsb'` pairing bijection
  `BitVec (2*n) ≃ BitVec n × BitVec n` via `probOutput_map_bijective_uniform_cross`).
* `isPolyTime_chooseProg`: the sampler is polynomial time (proof plan: an
  `Examples.DynamicalSystems.XorFlips`-style machine with state
  `Fin (2*n+1) × BitVec (2*n)`, round bound `2*n`, the *binary* state encoding
  `Computability.finEncodingBitVec` — the unary `FinEnum` encoding would be exponential
  — and per-step witnesses from `Computability.EncPolyTime.ofFintype`).
-/

open ENNReal OracleComp OracleSpec SymmEncAlg Computability

namespace KatzLindell

variable {K C : ℕ → Type}

/-! ## The bit-prediction experiment -/

/-- The bit-prediction experiment of Katz–Lindell Claim 3.11: encrypt a uniformly random
message and let the adversary guess its `i`-th bit from the ciphertext
(`BitVec.getLsbD`, so out-of-range indices read as `0`, as in the book). -/
noncomputable def predictExp (π : (n : ℕ) → SymmEncAlg ProbComp (BitVec n) (K n) (C n))
    (A : (n : ℕ) → C n → OracleComp coinSpec Bool) (i : ℕ) (n : ℕ) : ProbComp Bool := do
  let m ← $ᵗ BitVec n
  let k ← (π n).keygen
  let c ← (π n).encrypt k m
  let g ← simulateQ uniformSampleImpl (A n c)
  pure (g == m.getLsbD i)

/-! ## The reduction adversary -/

/-- Sample `r` fresh coins into bits `r-1, …, 0` of the accumulator. -/
def fillBits {w : ℕ} : ℕ → BitVec w → OracleComp coinSpec (BitVec w)
  | 0, acc => pure acc
  | r + 1, acc => OracleComp.queryBind () fun b => fillBits r (acc.overwriteBit r b)

/-- `fillBits r acc` makes at most `r` queries. -/
theorem isTotalQueryBound_fillBits {w : ℕ} (r : ℕ) (acc : BitVec w) :
    IsTotalQueryBound (fillBits r acc) r := by
  induction r generalizing acc with
  | zero => trivial
  | succ r ih => exact ⟨Nat.succ_pos r, fun b => ih (acc.overwriteBit r b)⟩

/-- The choose phase of the Katz–Lindell Claim 3.11 reduction: fill `2 * n` uniform
coins, split them into two `n`-bit messages, and force bit `i` to `0` in the first and
`1` in the second. -/
def chooseProg (i n : ℕ) : OracleComp coinSpec (BitVec n × BitVec n × Unit) := do
  let w ← fillBits (2 * n) (0 : BitVec (2 * n))
  pure ((w.extractLsb' 0 n).overwriteBit i false, (w.extractLsb' n n).overwriteBit i true, ())

/-- The Katz–Lindell Claim 3.11 reduction adversary `A′`: choose two uniform messages
differing in the forced bit `i`, and forward the predictor's bit as the guess. It keeps
no cross-phase state. -/
def reduceAdv (A : (n : ℕ) → C n → OracleComp coinSpec Bool) (i : ℕ) :
    PPTEavAdversary (fun n => BitVec n) C where
  State _ := Unit
  choose n := chooseProg i n
  distinguish n p := A n p.2

/-- The specification sampler for the reduction's choose phase, at the `ProbComp`
level: two independent uniform messages with bit `i` overwritten. -/
noncomputable def chooseIdeal (i n : ℕ) : ProbComp (BitVec n × BitVec n × Unit) := do
  let x ← $ᵗ BitVec n
  let y ← $ᵗ BitVec n
  pure (x.overwriteBit i false, y.overwriteBit i true, ())

/-- The reduction with the specification sampler in place of the coin-by-coin
program, as a single-scheme `SymmEncAlg.EavAdversary`. -/
noncomputable def reduceAdvIdeal (A : (n : ℕ) → C n → OracleComp coinSpec Bool)
    (i n : ℕ) : EavAdversary ProbComp (BitVec n) (C n) where
  State := Unit
  chooseMessages := chooseIdeal i n
  distinguish _ c := simulateQ uniformSampleImpl (A n c)

/-- **(Deferred)** The coin-by-coin sampler computes the specification sampler.
Proof plan: induction on `fillBits` showing the filled low bits are uniform and
independent, then the pairing bijection `w ↦ (extractLsb' 0 n w, extractLsb' n n w)`
via `probOutput_map_bijective_uniform_cross` and
`probOutput_uniformSample_bind_uniformSample`. -/
theorem evalDist_simulateQ_chooseProg (i n : ℕ) :
    𝒟[simulateQ uniformSampleImpl (chooseProg i n)] = 𝒟[chooseIdeal i n] := by
  sorry

/-- **(Deferred)** The choose phase is polynomial time. Proof plan: the machine with
state `Fin (2*n+1) × BitVec (2*n)` (counter of remaining coins, accumulator), round
bound `steps := .C 2 * .X`, simulation relation tying the state to the residual
`fillBits` program (the `Examples.DynamicalSystems.XorFlips` recipe), the binary state
encoding `finEncodingPair (finEncodingOfFinEnum _) (finEncodingBitVec _)` — linear where
the unary `FinEnum` encoding would be exponential — and all four step witnesses from
`Computability.EncPolyTime.ofFintype` with time bounds from
`EncPolyTime.time_ofFintype_eval_le`. -/
theorem isPolyTime_chooseProg (i : ℕ) :
    OracleComp.IsPolyTime fun n (_ : Unit) => chooseProg i n := by
  sorry

/-! ## The probability core -/

/-- **Uniform-split identity**: consuming a uniform bitvector together with its `i`-th
bit is the same as consuming a uniform bit and a uniform bitvector with bit `i`
overwritten by it. The change of variables is the involution
`BitVec.involutive_overwriteBit_pair`. -/
theorem probOutput_uniformSample_bitVec_bind_getLsbD {n : ℕ} {γ : Type} {i : ℕ}
    (hi : i < n) (body : BitVec n → Bool → ProbComp γ) (z : γ) :
    Pr[= z | do let m ← $ᵗ BitVec n; body m (m.getLsbD i)] =
      Pr[= z | do let b ← $ᵗ Bool; let m ← $ᵗ BitVec n; body (m.overwriteBit i b) b] := by
  have hτ : Function.Bijective fun p : BitVec n × Bool =>
      (BitVec.overwriteBit i p.2 p.1, p.1.getLsbD i) :=
    (BitVec.involutive_overwriteBit_pair hi).bijective
  calc Pr[= z | do let m ← $ᵗ BitVec n; body m (m.getLsbD i)]
      = Pr[= z | do let m ← $ᵗ BitVec n; let _ ← $ᵗ Bool; body m (m.getLsbD i)] := by
        refine (probOutput_bind_congr' _ z fun m => ?_).symm
        simp
    _ = Pr[= z | ($ᵗ (BitVec n × Bool)) >>= fun p => body p.1 (p.1.getLsbD i)] :=
        probOutput_uniformSample_bind_uniformSample (BitVec n)
          (fun p => body p.1 (p.1.getLsbD i)) z
    _ = Pr[= z | ($ᵗ (BitVec n × Bool)) >>=
          fun p => body (p.1.overwriteBit i p.2) p.2] := by
        refine Eq.trans (probOutput_bind_congr' _ z fun p => ?_)
          (probOutput_bind_bijective_uniform_cross (BitVec n × Bool)
            (fun p : BitVec n × Bool => (BitVec.overwriteBit i p.2 p.1, p.1.getLsbD i))
            hτ (fun p => body (p.1.overwriteBit i p.2) p.2) z)
        simp
    _ = Pr[= z | do
          let m ← $ᵗ BitVec n
          let b ← $ᵗ Bool
          body (m.overwriteBit i b) b] :=
        (probOutput_uniformSample_bind_uniformSample (BitVec n)
          (fun p => body (p.1.overwriteBit i p.2) p.2) z).symm
    _ = Pr[= z | do
          let b ← $ᵗ Bool
          let m ← $ᵗ BitVec n
          body (m.overwriteBit i b) b] :=
        probOutput_bind_bind_swap _ _ _ z

section MasterIdentity

variable (π : (n : ℕ) → SymmEncAlg ProbComp (BitVec n) (K n) (C n))
  (A : (n : ℕ) → C n → OracleComp coinSpec Bool)

/-- The fixed-bit branch shared by both experiments: encrypt a uniform message with bit
`i` overwritten by `b`, and compare the predictor's output to `b`. -/
private noncomputable def branchExp (i n : ℕ) (b : Bool) : ProbComp Bool := do
  let m ← $ᵗ BitVec n
  let k ← (π n).keygen
  let c ← (π n).encrypt k (m.overwriteBit i b)
  let g ← simulateQ uniformSampleImpl (A n c)
  pure (g == b)

private lemma probOutput_predictExp_eq_avg {i n : ℕ} (hi : i < n) :
    Pr[= true | predictExp π A i n] =
      (Pr[= true | branchExp π A i n true] + Pr[= true | branchExp π A i n false]) / 2 := by
  have hsplit := probOutput_uniformSample_bitVec_bind_getLsbD hi
    (fun m bit => do
      let k ← (π n).keygen
      let c ← (π n).encrypt k m
      let g ← simulateQ uniformSampleImpl (A n c)
      pure (g == bit)) true
  exact hsplit.trans (probOutput_bind_uniformBool _ true)

private lemma probOutput_eavExp_reduceAdvIdeal_eq_avg (i n : ℕ) :
    Pr[= true | EavExp (π n) (reduceAdvIdeal A i n)] =
      (Pr[= true | branchExp π A i n true] + Pr[= true | branchExp π A i n false]) / 2 := by
  -- Push the challenge bit to the front of the experiment.
  have hswap : Pr[= true | EavExp (π n) (reduceAdvIdeal A i n)] =
      Pr[= true | do
        let b ← ($ᵗ Bool)
        let msc ← chooseIdeal i n
        let k ← (π n).keygen
        let c ← (π n).encrypt k (if b then msc.2.1 else msc.1)
        let b' ← simulateQ uniformSampleImpl (A n c)
        pure (b == b')] := by
    rw [EavExp]
    refine Eq.trans (probOutput_bind_congr' _ true fun msc => ?_)
      (probOutput_bind_bind_swap _ _ _ true)
    obtain ⟨m₀, m₁, s⟩ := msc
    exact probOutput_bind_bind_swap _ _ _ true
  rw [hswap, probOutput_bind_uniformBool]
  -- Per branch, drop the unused sample and normalize the Boolean comparison.
  have hbranch : ∀ b, Pr[= true | do
      let msc ← chooseIdeal i n
      let k ← (π n).keygen
      let c ← (π n).encrypt k (if b then msc.2.1 else msc.1)
      let b' ← simulateQ uniformSampleImpl (A n c)
      pure (b == b')] = Pr[= true | branchExp π A i n b] := by
    intro b
    have hinline : Pr[= true | do
        let msc ← chooseIdeal i n
        let k ← (π n).keygen
        let c ← (π n).encrypt k (if b then msc.2.1 else msc.1)
        let b' ← simulateQ uniformSampleImpl (A n c)
        pure (b == b')] =
      Pr[= true | do
        let x ← $ᵗ BitVec n
        let y ← $ᵗ BitVec n
        let k ← (π n).keygen
        let c ← (π n).encrypt k
          (if b then y.overwriteBit i true else x.overwriteBit i false)
        let b' ← simulateQ uniformSampleImpl (A n c)
        pure (b == b')] := by
      refine probOutput_congr rfl ?_
      simp [chooseIdeal, monad_norm]
    rw [hinline]
    unfold branchExp
    cases b
    · -- `b = false`: the second sample `y` is unused.
      refine probOutput_bind_congr' _ true fun x => ?_
      simp
    · -- `b = true`: the first sample `x` is unused.
      refine Eq.trans (probOutput_bind_bind_swap _ _ _ true) ?_
      refine probOutput_bind_congr' _ true fun y => ?_
      simp
  rw [hbranch true, hbranch false]

/-- **Master identity** (the probability core of Katz–Lindell Claim 3.11, sharpened to
an exact equality): the predictor's success probability equals the reduction's success
probability in the eavesdropping experiment, for meaningful bit positions `i < n`. -/
theorem probOutput_predictExp_eq_eavExp_reduceAdvIdeal {i n : ℕ} (hi : i < n) :
    Pr[= true | predictExp π A i n] =
      Pr[= true | EavExp (π n) (reduceAdvIdeal A i n)] :=
  (probOutput_predictExp_eq_avg π A hi).trans
    (probOutput_eavExp_reduceAdvIdeal_eq_avg π A i n).symm

/-- The machine-level reduction agrees with its specification: `privKEav` with
`reduceAdv` computes the same success probability as the ideal-sampler experiment,
through the (deferred) sampler-semantics bridge `evalDist_simulateQ_chooseProg`. -/
theorem probOutput_privKEav_reduceAdv_eq_eavExp_reduceAdvIdeal (i n : ℕ) :
    Pr[= true | privKEav π (reduceAdv A i) n] =
      Pr[= true | EavExp (π n) (reduceAdvIdeal A i n)] := by
  refine probOutput_congr rfl ?_
  simp only [privKEav, EavExp, PPTEavAdversary.toEavAdversary, reduceAdv, reduceAdvIdeal]
  rw [evalDist_bind, evalDist_bind, evalDist_simulateQ_chooseProg]

end MasterIdentity

/-! ## Polynomial time of the reduction -/

/-- **`A′` is PPT since `A` is**: the reduction adversary is probabilistic polynomial
time whenever the predictor is. The choose phase is the (deferred) sampler machine; the
distinguish phase reuses the predictor's machine through the input-precomposition
closure `OracleComp.IsPolyTime.precomp`. Ciphertexts are required to be (per-parameter)
finite encodable types, as bitstring types are. -/
theorem isPPT_reduceAdv [∀ n, Finite (C n)] (encC : (n : ℕ) → FinEncoding (C n))
    {A : (n : ℕ) → C n → OracleComp coinSpec Bool}
    (hA : OracleComp.IsPolyTime A) (i : ℕ) :
    (reduceAdv (C := C) A i).IsPPT :=
  ⟨isPolyTime_chooseProg i,
    hA.precomp (fun n (p : Unit × C n) => p.2)
      (fun n => finEncodingPair (finEncodingOfFinEnum Unit) (encC n))
      (fun _ => OracleHandler.ofFn fun _ => true)⟩

/-! ## Claim 3.11 -/

variable (π : (n : ℕ) → SymmEncAlg ProbComp (BitVec n) (K n) (C n))

/-- The bit-prediction game of Claim 3.11 as a `SecurityGame`: the advantage of a
predictor at bit `i` is the bias of `predictExp` away from `1/2`. -/
noncomputable def predictBitGame (i : ℕ) :
    SecurityGame ((n : ℕ) → C n → OracleComp coinSpec Bool) where
  advantage A n := ENNReal.ofReal (predictExp π A i n).boolBiasAdvantage

/-- **Katz–Lindell Claim 3.11**: if `π` has indistinguishable encryptions in the
presence of an eavesdropper, then for every bit position `i`, no polynomial-time
adversary predicts bit `i` of a uniform plaintext from its encryption with
non-negligible bias. The reduction is advantage-exact for `i < n`; the finitely many
parameters `n ≤ i` are absorbed as negligible slack. -/
theorem secureAgainst_predictBitGame_of_eavSecure [∀ n, Finite (C n)]
    (encC : (n : ℕ) → FinEncoding (C n)) (hπ : EavSecure π) (i : ℕ) :
    (predictBitGame π i).secureAgainst OracleComp.IsPolyTime := by
  refine SecurityGame.secureAgainst_of_close_reduction
    (g₂ := eavGuessGame π) (reduce := fun A => reduceAdv A i)
    (ε := fun n => if n ≤ i then 1 else 0)
    (negligible_of_eventually_zero ?_)
    (fun A hA => isPPT_reduceAdv encC hA i) ?_ hπ
  · filter_upwards [Filter.eventually_gt_atTop i] with n hn
    simp [Nat.not_le.mpr hn]
  · intro A _ n
    rcases Nat.lt_or_ge i n with hn | hn
    swap
    · -- Degenerate band `n ≤ i`: the advantage is at most one, absorbed by the slack.
      simp only [if_pos hn]
      exact (ENNReal.ofReal_le_one.mpr (ProbComp.boolBiasAdvantage_le_one _)).trans
        le_add_self
    · -- Meaningful band `i < n`: the reduction is advantage-exact.
      simp only [if_neg (Nat.not_le.mpr hn), add_zero]
      have hPr : Pr[= true | predictExp π A i n] =
          Pr[= true | privKEav π (reduceAdv A i) n] :=
        (probOutput_predictExp_eq_eavExp_reduceAdvIdeal π A hn).trans
          (probOutput_privKEav_reduceAdv_eq_eavExp_reduceAdvIdeal π A i n).symm
      refine le_of_eq (congrArg ENNReal.ofReal ?_)
      rw [ProbComp.boolBiasAdvantage_eq_two_mul_abs_sub_half,
        ProbComp.boolBiasAdvantage_eq_two_mul_abs_sub_half, hPr]

/-- The literal reading of **Katz–Lindell Claim 3.11**: for an eavesdropping-secure
scheme, every polynomial-time predictor guesses bit `i` of a uniform plaintext with
probability at most `1/2 + negl n`. -/
theorem exists_negligible_probOutput_predictExp_le [∀ n, Finite (C n)]
    (encC : (n : ℕ) → FinEncoding (C n)) (hπ : EavSecure π)
    (A : (n : ℕ) → C n → OracleComp coinSpec Bool)
    (hA : OracleComp.IsPolyTime A) (i : ℕ) :
    ∃ f : ℕ → ℝ≥0∞, negligible f ∧
      ∀ n, Pr[= true | predictExp π A i n] ≤ 1 / 2 + f n :=
  ⟨(predictBitGame π i).advantage A,
    secureAgainst_predictBitGame_of_eavSecure π encC hπ i A hA, fun n =>
    ProbComp.probOutput_true_le_half_add_ofReal_boolBiasAdvantage (predictExp π A i n)⟩

end KatzLindell
