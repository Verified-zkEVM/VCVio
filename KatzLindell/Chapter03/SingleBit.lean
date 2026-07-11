/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import KatzLindell.Chapter03.PrivKEav
import KatzLindell.Chapter03.SamplerMachine
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
  "`A′` is PPT since `A` is" step (`hred`) is an explicit honest-fallback hypothesis —
  a coarser residue than the single pure-glue witness `eavSecure_prgEnc` is left with —
  see `isPPT_reduceAdv` for its decomposition into the choose-phase machine witnesses
  and the ciphertext-projection precomposition, both awaiting the base-machine library.

The distribution of the coin-by-coin sampler is pinned down by `evalDist_fillBits` (the
coin loop is uniform) and the half-splitting bijection `splitPair`, giving the exact
sampler semantics `evalDist_simulateQ_chooseProg`. The sampler's polynomial-time story,
`isPolyTime_chooseProg` (hypothesis form), lives in
`KatzLindell.Chapter03.SamplerMachine`.
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

/-! ## Distribution of the coin-fill sampler

The choose-phase sampler `fillBits` / `chooseProg` and its polynomial-time witness
`isPolyTime_chooseProg` live in `KatzLindell.Chapter03.SamplerMachine`; here its output
distribution is pinned down. -/

/-- Binding a fair coin query averages the two branch probabilities, since a `coinSpec`
query returns a uniform boolean. -/
theorem probOutput_queryBind_coin_split {α : Type} (g : Bool → OracleComp coinSpec α) (v : α) :
    Pr[= v | OracleComp.queryBind (spec := coinSpec) () g] =
      (Pr[= v | g true] + Pr[= v | g false]) / 2 := by
  rw [show OracleComp.queryBind (spec := coinSpec) () g
        = (liftM (OracleSpec.query (spec := coinSpec) ()) : OracleComp coinSpec Bool) >>= g
      from rfl, probOutput_bind_eq_tsum]
  simp only [tsum_fintype (L := .unconditional _), Fintype.sum_bool, probOutput_query,
    Fintype.card_bool, Nat.cast_ofNat]
  rw [← mul_add, ENNReal.div_eq_inv_mul]

open Classical in
/-- Output distribution of the coin-fill loop: `fillBits r acc` overwrites the low `r`
bits of `acc` with independent fair coins, so a target `v` is produced exactly when it
agrees with `acc` on the untouched high bits (`r ≤ j`), each such `v` with mass `2⁻ʳ`. -/
theorem probOutput_fillBits {w : ℕ} (r : ℕ) (hr : r ≤ w) (acc v : BitVec w) :
    Pr[= v | fillBits r acc] =
      if ∀ j, r ≤ j → acc.getLsbD j = v.getLsbD j then (2 ^ r : ℝ≥0∞)⁻¹ else 0 := by
  induction r generalizing acc with
  | zero =>
    simp only [fillBits, probOutput_pure]
    refine if_congr ?_ (by norm_num) rfl
    refine ⟨fun h => h ▸ fun j _ => rfl, fun h => ?_⟩
    exact ((BitVec.eq_of_getLsbD_eq_iff).mpr fun j _ => h j (Nat.zero_le j)).symm
  | succ r ih =>
    have hrw : r < w := hr
    have harith : ((2 : ℝ≥0∞) ^ r)⁻¹ / 2 = (2 ^ (r + 1))⁻¹ := by
      rw [pow_succ, ENNReal.mul_inv (by simp) (by simp), div_eq_mul_inv]
    rw [show fillBits (r + 1) acc = OracleComp.queryBind (spec := coinSpec) () fun b =>
          fillBits r (acc.overwriteBit r b) from rfl, probOutput_queryBind_coin_split,
      ih (Nat.le_of_succ_le hr) _, ih (Nat.le_of_succ_le hr) _]
    have hcond : ∀ b : Bool,
        (∀ j, r ≤ j → (acc.overwriteBit r b).getLsbD j = v.getLsbD j) ↔
          (b = v.getLsbD r ∧ ∀ j, r + 1 ≤ j → acc.getLsbD j = v.getLsbD j) := by
      intro b
      refine ⟨fun h => ⟨?_, fun j hj => ?_⟩, ?_⟩
      · have := h r (le_refl r); rwa [BitVec.getLsbD_overwriteBit_self hrw] at this
      · have hjr : r < j := Nat.lt_of_succ_le hj
        have := h j (Nat.le_of_succ_le hj)
        rwa [BitVec.getLsbD_overwriteBit_of_ne hjr.ne'] at this
      · rintro ⟨hb, hD⟩ j hj
        rcases eq_or_lt_of_le hj with rfl | hlt
        · rw [BitVec.getLsbD_overwriteBit_self hrw]; exact hb
        · rw [BitVec.getLsbD_overwriteBit_of_ne hlt.ne']; exact hD j hlt
    simp only [hcond]
    by_cases hD : (∀ j, r + 1 ≤ j → acc.getLsbD j = v.getLsbD j)
    · simp only [eq_true hD, and_true, if_true]
      rw [show (if true = v.getLsbD r then ((2 : ℝ≥0∞) ^ r)⁻¹ else 0)
            + (if false = v.getLsbD r then ((2 : ℝ≥0∞) ^ r)⁻¹ else 0) = (2 ^ r)⁻¹ from by
          cases v.getLsbD r <;> simp, harith]
    · simp only [eq_false hD, and_false, if_false, add_zero]
      simp

/-- Filling all `w` bits with fair coins yields the uniform distribution on `BitVec w`,
regardless of the starting accumulator. -/
theorem evalDist_fillBits {w : ℕ} (acc : BitVec w) :
    𝒟[fillBits w acc] = 𝒟[($ᵗ BitVec w)] := by
  refine evalDist_ext fun v => ?_
  rw [probOutput_fillBits w le_rfl acc v, probOutput_uniformSample,
    if_pos fun j hj => by rw [BitVec.getLsbD_of_ge acc j hj, BitVec.getLsbD_of_ge v j hj],
    card_bitVec, Nat.cast_pow, Nat.cast_ofNat]

/-! ## The reduction adversary -/

/-- The Katz–Lindell Claim 3.11 reduction adversary `A′`: choose two uniform messages
differing in the forced bit `i`, and forward the predictor's bit as the guess. It keeps
no cross-phase state. -/
noncomputable def reduceAdv (A : (n : ℕ) → C n → OracleComp coinSpec Bool) (i : ℕ) :
    PPTEavAdversary (fun n => BitVec n) C where
  State _ := Unit
  encState := BitEncFam.unit
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

/-- Splitting a `2 * n`-bit vector into its low and high `n`-bit halves. -/
def splitPair (n : ℕ) (w : BitVec (2 * n)) : BitVec n × BitVec n :=
  (w.extractLsb' 0 n, w.extractLsb' n n)

/-- The half-splitting map is a bijection `BitVec (2 * n) ≃ BitVec n × BitVec n`: distinct
vectors differ in some bit, which lands in exactly one half, and the two spaces have equal
cardinality `2 ^ (2 * n) = 2 ^ n * 2 ^ n`. -/
theorem bijective_splitPair (n : ℕ) : Function.Bijective (splitPair n) := by
  classical
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun w1 w2 h => ?_, ?_⟩
  · simp only [splitPair, Prod.mk.injEq] at h
    obtain ⟨h0, hn⟩ := h
    refine BitVec.eq_of_getLsbD_eq_iff.mpr fun j hj => ?_
    rcases lt_or_ge j n with hjn | hjn
    · have hcongr := congrArg (·.getLsbD j) h0
      simpa [BitVec.getLsbD_extractLsb', hjn, Nat.zero_add] using hcongr
    · have hi : j - n < n := by omega
      have hcongr := congrArg (·.getLsbD (j - n)) hn
      simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and] at hcongr
      rwa [show n + (j - n) = j from by omega] at hcongr
  · rw [card_bitVec, Fintype.card_prod, card_bitVec, ← pow_add, two_mul]

/-- The coin-by-coin sampler computes the specification sampler: filling `2 * n` coins and
splitting them into the two forced messages has the same distribution as sampling two
independent uniform messages and forcing bit `i`. The coin loop is uniform
(`evalDist_fillBits`) and the half-splitting `splitPair` is a bijection turning one uniform
`2 * n`-bit sample into two independent uniform `n`-bit samples. -/
theorem evalDist_simulateQ_chooseProg (i n : ℕ) :
    𝒟[simulateQ uniformSampleImpl (chooseProg i n)] = 𝒟[chooseIdeal i n] := by
  rw [uniformSampleImpl.evalDist_simulateQ]
  have hstep : 𝒟[chooseProg i n] =
      𝒟[($ᵗ BitVec (2 * n)) >>= fun w : BitVec (2 * n) =>
        pure (BitVec.overwriteBit i false (splitPair n w).1,
              BitVec.overwriteBit i true (splitPair n w).2, ())] := by
    rw [show chooseProg i n = fillBits (2 * n) (0 : BitVec (2 * n)) >>= fun w : BitVec (2 * n) =>
          pure (BitVec.overwriteBit i false (splitPair n w).1,
                BitVec.overwriteBit i true (splitPair n w).2, ()) from rfl,
      evalDist_bind, evalDist_bind]
    congr 1
    exact evalDist_fillBits _
  rw [hstep]
  refine evalDist_ext fun z => ?_
  refine Eq.trans (probOutput_bind_bijective_uniform_cross (BitVec (2 * n)) (splitPair n)
      (bijective_splitPair n)
      (fun p : BitVec n × BitVec n =>
        pure (BitVec.overwriteBit i false p.1, BitVec.overwriteBit i true p.2, ())) z) ?_
  exact (probOutput_uniformSample_bind_uniformSample (BitVec n)
      (fun p : BitVec n × BitVec n =>
        pure (BitVec.overwriteBit i false p.1, BitVec.overwriteBit i true p.2, ())) z).symm

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

/-- **`A′` is PPT since `A` is — the honest hypothesis form.** Both halves of the
reduction adversary's polynomial time are taken as hypotheses (now at pinned canonical
boundaries), for two distinct reasons rooted in the advice bound of the machine model:

* the choose phase is a coin fold into a `BitVec (2 * n)` accumulator, whose machine
  families await the base-machine library (`isPolyTime_chooseProg` states exactly the
  needed families);
* the distinguish phase precomposes the predictor with a projection on the ciphertext
  type, which is superpolynomially large for bitstring ciphertexts, so the table-based
  closure `OracleComp.IsPolyTime.precomp` cannot certify it within any polynomial
  advice bound — a real projection machine is needed.

Once discharged, the conclusion is definitional. -/
theorem isPPT_reduceAdv {A : (n : ℕ) → C n → OracleComp coinSpec Bool}
    (eC : Computability.BitEncFam C) (i : ℕ)
    (hchoose : OracleComp.IsPolyTime (BoundaryData.coin BitEncFam.unit
      (BitEncFam.bitVecX.pair (BitEncFam.bitVecX.pair BitEncFam.unit)))
      fun n (_ : Unit) => chooseProg i n)
    (hdist : OracleComp.IsPolyTime
      (BoundaryData.coin (BitEncFam.unit.pair eC) BitEncFam.bool)
      fun n (p : Unit × C n) => A n p.2) :
    (reduceAdv (C := C) A i).IsPPT BitEncFam.bitVecX eC :=
  ⟨hchoose, hdist⟩

/-! ## Claim 3.11 -/

variable (π : (n : ℕ) → SymmEncAlg ProbComp (BitVec n) (K n) (C n))

/-- The bit-prediction game of Claim 3.11 as a `SecurityGame`: the advantage of a
predictor at bit `i` is the bias of `predictExp` away from `1/2`. -/
noncomputable def predictBitGame (i : ℕ) :
    SecurityGame ((n : ℕ) → C n → OracleComp coinSpec Bool) :=
  SecurityGame.ofBoolGuessGame (fun A n => predictExp π A i n)

/-- **Katz–Lindell Claim 3.11**: if `π` has indistinguishable encryptions in the
presence of an eavesdropper, then for every bit position `i`, no polynomial-time
adversary predicts bit `i` of a uniform plaintext from its encryption with
non-negligible bias. The reduction is advantage-exact for `i < n`; the finitely many
parameters `n ≤ i` are absorbed as negligible slack.

The polynomial time of the reduction adversary is an explicit hypothesis (`hred`) — an
honest fallback, coarser than the single pure-glue witness `eavSecure_prgEnc` is left
with: discharging it awaits the base-machine library (see `isPPT_reduceAdv` for the
exact decomposition into choose- and distinguish-phase witnesses). -/
theorem secureAgainst_predictBitGame_of_eavSecure (eC : Computability.BitEncFam C)
    (hπ : EavSecure π BitEncFam.bitVecX eC) (i : ℕ)
    (hred : ∀ A : (n : ℕ) → C n → OracleComp coinSpec Bool,
      OracleComp.IsPolyTime (BoundaryData.coin eC BitEncFam.bool) A →
        (reduceAdv A i).IsPPT BitEncFam.bitVecX eC) :
    (predictBitGame π i).secureAgainst
      (OracleComp.IsPolyTime (BoundaryData.coin eC BitEncFam.bool)) := by
  refine SecurityGame.secureAgainst_of_close_reduction
    (g₂ := eavGuessGame π) (reduce := fun A => reduceAdv A i)
    (ε := fun n => if n ≤ i then 1 else 0)
    (negligible_of_eventually_zero ?_)
    (fun A hA => hred A hA) ?_ hπ
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
probability at most `1/2 + negl n`. The reduction's polynomial time is the same
explicit hypothesis as in `secureAgainst_predictBitGame_of_eavSecure`. -/
theorem exists_negligible_probOutput_predictExp_le (eC : Computability.BitEncFam C)
    (hπ : EavSecure π BitEncFam.bitVecX eC)
    (A : (n : ℕ) → C n → OracleComp coinSpec Bool)
    (hA : OracleComp.IsPolyTime (BoundaryData.coin eC BitEncFam.bool) A) (i : ℕ)
    (hred : ∀ A : (n : ℕ) → C n → OracleComp coinSpec Bool,
      OracleComp.IsPolyTime (BoundaryData.coin eC BitEncFam.bool) A →
        (reduceAdv A i).IsPPT BitEncFam.bitVecX eC) :
    ∃ f : ℕ → ℝ≥0∞, negligible f ∧
      ∀ n, Pr[= true | predictExp π A i n] ≤ 1 / 2 + f n :=
  ⟨(predictBitGame π i).advantage A,
    secureAgainst_predictBitGame_of_eavSecure π eC hπ i hred A hA, fun n =>
    ProbComp.probOutput_true_le_half_add_ofReal_boolBiasAdvantage (predictExp π A i n)⟩

end KatzLindell
