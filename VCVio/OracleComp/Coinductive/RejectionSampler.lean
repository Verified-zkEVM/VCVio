/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathlib.Data.Nat.Size
import VCVio.OracleComp.Coinductive.RunLimit
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Rejection Sampling on Coins: Exact Limit, Truncated Distance

The coin-driven rejection sampler for the uniform distribution on `Fin (t + 1)`:
repeatedly flip `rejWidth t = Nat.size t` fair coins into an accumulator and accept the
result if it is at most `t`, restarting otherwise (`rejectionMachine`). Against the
fair-coin oracle `coinSpec.probHandler`:

* **Exact limit uniformity** (`runLimit_rejectionMachine`): the limit run *equals* the
  uniform distribution `𝒟[$ᵗ Fin (t + 1)]`. In particular the machine terminates
  almost surely (`rejectionMachine_asTerminates`). This answers the "limit of the
  distribution" question exactly — but it is a statement about the semantic limit
  object `OracleMachine.runLimit` only.
* **Geometric truncation bound** (`gap_runKT_rejectionMachine_le`,
  `etvDist_runKT_rejectionMachine_le`): the *truncated* run at fuel
  `(rejWidth t + 1) * (k + 1)` — a strict fuel budget covering `k + 1` attempt blocks —
  is within `2⁻⁽ᵏ⁺¹⁾` of exact uniform in extended total-variation distance. Each
  rejected block wastes one restart flip, keeping blocks uniform at `rejWidth t + 1`
  steps; acceptance probability per block is `(t + 1) / 2 ^ rejWidth t ≥ 1/2` by
  minimality of `Nat.size`.

## Not polynomial time — and deliberately so

The unbounded sampler is **not** a polynomial-time machine, and no such claim is made
here: `OracleComp.IsPolyTime` requires a fuelled `Implements` witness, and no finite
fuel implements exact uniform sampling on a non-power-of-two range with coins (the
machine has positive rejection probability at every fuel). What enters PPT statements
is strictly the truncated machine at fuel `(rejWidth t + 1) * (k + 1)` together with
the explicit statistical budget `2⁻⁽ᵏ⁺¹⁾`, in the `OracleMachine.ImplementsWithin`
discipline of `VCVio.OracleComp.Coinductive.RunLimit`. Taking `k = poly(n)` makes the
budget negligible while the fuel stays polynomial — the textbook (Katz–Lindell)
strict-PPT treatment of sampling from non-power-of-two ranges. Expected-time
("Las Vegas") analysis is deliberately not formalized.
-/

open ENNReal OmegaCompletePartialOrder OracleSpec OracleMachine

namespace OracleComp

/-! ## The fair coin, pointwise -/

/-- The canonical coin handler answers each side with probability `2⁻¹`. -/
@[simp] lemma probHandler_coin_apply (b : Bool) :
    (coinSpec.probHandler () : SPMF Bool) b = 2⁻¹ := by
  have h : (coinSpec.probHandler () : SPMF Bool) = 𝒟[coin] := by
    rw [← OracleSpec.simulateQ_probHandler coin]
    simp [OracleComp.coin]
  rw [h, ← probOutput_def, probOutput_coin]

/-- The canonical coin handler loses no mass. -/
@[simp] lemma gap_probHandler_coin : (coinSpec.probHandler () : SPMF Bool).gap = 0 := by
  rw [SPMF.gap_eq_one_sub_tsum, tsum_bool, probHandler_coin_apply, probHandler_coin_apply,
    ENNReal.inv_two_add_inv_two, tsub_self]

/-- Binding the fair coin into a constant continuation is that constant: the wasted
restart flip of a rejected attempt does not change the distribution. -/
lemma probHandler_coin_bind_const {α : Type} (p : SPMF α) :
    (coinSpec.probHandler () >>= fun _ => p) = p :=
  SPMF.bind_const_of_gap_eq_zero gap_probHandler_coin p

private lemma map_bind_eq {α β γ : Type} (p : SPMF α) (f : α → β) (g : β → SPMF γ) :
    (f <$> p) >>= g = p >>= fun a => g (f a) := by
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]

private lemma map_apply_eq_of_eq {α β : Type} [DecidableEq β] {f : α → β}
    {p : SPMF α} (x : α) {y : β} (h : f x = y)
    (hinj : ∀ a, p a ≠ 0 → f a = y → a = x) : (f <$> p) y = p x := by
  rw [map_eq_bind_pure_comp, SPMF.bind_apply_eq_tsum]
  refine (tsum_eq_single x fun v hv => ?_).trans ?_
  · rcases eq_or_ne (p v) 0 with hp | hp
    · rw [hp, zero_mul]
    · rw [Function.comp_apply,
        (SPMF.pure_apply_eq_zero_iff _ _).mpr fun hy => hv (hinj v hp hy.symm), mul_zero]
  · rw [Function.comp_apply, h, SPMF.pure_apply_self, mul_one]

private lemma map_apply_eq_zero {α β : Type} {f : α → β} (p : SPMF α) {y : β}
    (h : ∀ a, f a ≠ y) : (f <$> p) y = 0 := by
  rw [map_eq_bind_pure_comp, SPMF.bind_apply_eq_tsum]
  refine ENNReal.tsum_eq_zero.mpr fun v => ?_
  rw [Function.comp_apply,
    (SPMF.pure_apply_eq_zero_iff _ _).mpr fun hy => h v hy.symm, mul_zero]

/-! ## Uniform bit blocks from fair coins -/

private lemma bit_append_lt {j u : ℕ} (b : Bool) (hu : u < 2 ^ j) :
    b.toNat * 2 ^ j + u < 2 ^ (j + 1) := by
  have h2 : 2 ^ (j + 1) = 2 ^ j + 2 ^ j := by rw [pow_succ]; ring
  cases b with
  | false => simpa using hu.trans_le (by omega)
  | true => simpa [h2] using Nat.add_lt_add_left hu (2 ^ j)

/-- The distribution of `j` fair coin flips folded most-significant-bit first into
`Fin (2 ^ j)`: the value distribution of one build phase of the rejection sampler. -/
noncomputable def coinFlips : (j : ℕ) → SPMF (Fin (2 ^ j))
  | 0 => pure ⟨0, Nat.two_pow_pos 0⟩
  | j + 1 => coinSpec.probHandler () >>= fun b =>
      (fun u : Fin (2 ^ j) => (⟨b.toNat * 2 ^ j + u, bit_append_lt b u.isLt⟩ :
        Fin (2 ^ (j + 1)))) <$> coinFlips j

@[simp] lemma coinFlips_zero : coinFlips 0 = pure ⟨0, Nat.two_pow_pos 0⟩ := rfl

lemma coinFlips_succ (j : ℕ) :
    coinFlips (j + 1) = coinSpec.probHandler () >>= fun b =>
      (fun u : Fin (2 ^ j) => (⟨b.toNat * 2 ^ j + u, bit_append_lt b u.isLt⟩ :
        Fin (2 ^ (j + 1)))) <$> coinFlips j := rfl

/-- The coin-flip block is uniform: every `j`-bit value has probability `2⁻ʲ`. -/
lemma coinFlips_apply (j : ℕ) : ∀ u : Fin (2 ^ j), coinFlips j u = ((2 : ℝ≥0∞) ^ j)⁻¹ := by
  induction j with
  | zero =>
    intro u
    have hu : u = ⟨0, Nat.two_pow_pos 0⟩ := Fin.ext (by have := u.isLt; omega)
    simp [hu]
  | succ j ih =>
    intro u
    have hmap : ∀ b : Bool,
        ((fun v : Fin (2 ^ j) => (⟨b.toNat * 2 ^ j + v, bit_append_lt b v.isLt⟩ :
          Fin (2 ^ (j + 1)))) <$> coinFlips j) u =
          if b = decide ((u : ℕ) < 2 ^ j) then 0 else ((2 : ℝ≥0∞) ^ j)⁻¹ := by
      intro b
      rcases Nat.lt_or_ge (u : ℕ) (2 ^ j) with hu | hu
      · cases b with
        | false =>
          rw [if_neg (by simp [decide_eq_true hu])]
          refine (map_apply_eq_of_eq (⟨(u : ℕ), hu⟩ : Fin (2 ^ j))
            (Fin.ext (by simp)) fun a _ ha => Fin.ext ?_).trans (ih _)
          simpa using congrArg Fin.val ha
        | true =>
          rw [if_pos (by simp [decide_eq_true hu])]
          refine map_apply_eq_zero _ fun a ha => ?_
          have := congrArg Fin.val ha
          simp only [Bool.toNat_true, one_mul] at this
          omega
      · cases b with
        | false =>
          rw [if_pos (by simp [decide_eq_false (Nat.not_lt.mpr hu)])]
          refine map_apply_eq_zero _ fun a ha => ?_
          have h1 := a.isLt
          have := congrArg Fin.val ha
          simp only [Bool.toNat_false, zero_mul, zero_add] at this
          omega
        | true =>
          rw [if_neg (by simp [decide_eq_false (Nat.not_lt.mpr hu)])]
          have hu2 : (u : ℕ) - 2 ^ j < 2 ^ j := by
            have h2 : (u : ℕ) < 2 ^ (j + 1) := u.isLt
            have h3 : 2 ^ (j + 1) = 2 ^ j + 2 ^ j := by rw [pow_succ]; ring
            omega
          refine (map_apply_eq_of_eq (⟨(u : ℕ) - 2 ^ j, hu2⟩ : Fin (2 ^ j))
            (Fin.ext ?_) fun a _ ha => Fin.ext ?_).trans (ih _)
          · simp only [Bool.toNat_true, one_mul]
            show 2 ^ j + ((u : ℕ) - 2 ^ j) = u
            omega
          · have := congrArg Fin.val ha
            simp only [Bool.toNat_true, one_mul] at this
            show (a : ℕ) = (u : ℕ) - 2 ^ j
            omega
    have hpow : ((2 : ℝ≥0∞) ^ (j + 1))⁻¹ = 2⁻¹ * ((2 : ℝ≥0∞) ^ j)⁻¹ := by
      rw [pow_succ', ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ofNat_ne_top)]
    rw [coinFlips_succ, SPMF.bind_apply_eq_tsum, tsum_bool, hmap false, hmap true,
      probHandler_coin_apply, probHandler_coin_apply]
    rcases Nat.lt_or_ge (u : ℕ) (2 ^ j) with hu | hu
    · rw [if_neg (by simp [decide_eq_true hu]), if_pos (by simp [decide_eq_true hu]),
        mul_zero, add_zero, hpow]
    · rw [if_pos (by simp [decide_eq_false (Nat.not_lt.mpr hu)]),
        if_neg (by simp [decide_eq_false (Nat.not_lt.mpr hu)]),
        mul_zero, zero_add, hpow]

/-- The coin-flip block loses no mass. -/
@[simp] lemma gap_coinFlips (j : ℕ) : (coinFlips j).gap = 0 := by
  rw [SPMF.gap_eq_one_sub_tsum, tsum_fintype,
    Finset.sum_congr rfl fun u _ => coinFlips_apply j u, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    show ((2 ^ j : ℕ) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ j by push_cast; ring,
    ENNReal.mul_inv_cancel (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top ofNat_ne_top),
    tsub_self]

/-! ## The rejection-sampler machine -/

/-- Bit width of one rejection-sampling attempt for target `Fin (t + 1)`: the number
of bits of `t`, so that `t < 2 ^ rejWidth t ≤ 2 * (t + 1)` and each attempt accepts
with probability at least `1/2`. -/
def rejWidth (t : ℕ) : ℕ := Nat.size t

lemma lt_two_pow_rejWidth (t : ℕ) : t < 2 ^ rejWidth t := Nat.lt_size_self t

lemma two_pow_rejWidth_le (t : ℕ) : 2 ^ rejWidth t ≤ 2 * (t + 1) := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [rejWidth, Nat.size_zero]
  · have h1 : 0 < Nat.size t := Nat.size_pos.mpr ht
    have h2 : 2 ^ (Nat.size t - 1) ≤ t := Nat.lt_size.mp (by omega)
    have h3 : 2 ^ rejWidth t = 2 * 2 ^ (Nat.size t - 1) := by
      rw [rejWidth, ← pow_succ']
      congr 1
      omega
    omega

/-- The rejection-sampler machine for `Fin (t + 1)`: state `(counter, accumulator)`.
While the counter is below `rejWidth t`, each coin answer is shifted into the
accumulator; at a full counter the readout accepts an accumulator value `≤ t`, and a
rejected value spends one further (wasted) coin flip restarting at `(0, 0)`, keeping
attempt blocks uniform at `rejWidth t + 1` steps. -/
def rejectionMachine (t : ℕ) : OracleMachine coinSpec Unit (Fin (t + 1)) where
  State := Fin (rejWidth t + 1) × Fin (2 ^ rejWidth t)
  expose _ := ()
  update s b :=
    if h : (s.1 : ℕ) < rejWidth t then
      (⟨(s.1 : ℕ) + 1, Nat.succ_lt_succ h⟩,
        ⟨(2 * (s.2 : ℕ) + b.toNat) % 2 ^ rejWidth t, Nat.mod_lt _ (Nat.two_pow_pos _)⟩)
    else (0, ⟨0, Nat.two_pow_pos _⟩)
  init _ := (0, ⟨0, Nat.two_pow_pos _⟩)
  output s :=
    if (s.1 : ℕ) = rejWidth t then
      if h : (s.2 : ℕ) ≤ t then some ⟨s.2, Nat.lt_succ_of_le h⟩ else none
    else none

/-- One attempt's continuation: accept a sampled value `≤ t`, otherwise fall through
to `X` (the rest of the run). -/
noncomputable def acceptOr (t : ℕ) (X : SPMF (Fin (t + 1)))
    (u : Fin (2 ^ rejWidth t)) : SPMF (Fin (t + 1)) :=
  if h : (u : ℕ) ≤ t then pure ⟨u, Nat.lt_succ_of_le h⟩ else X

/-! ## Block analysis of the fuelled run -/

private lemma output_eq_none_of_lt (t : ℕ) {c : Fin (rejWidth t + 1)}
    (hc : (c : ℕ) < rejWidth t) (acc : Fin (2 ^ rejWidth t)) :
    (rejectionMachine t).output (c, acc) = none := by
  simp only [rejectionMachine]
  rw [if_neg (by omega)]

/-- The build phase: from a state with `j` bits missing, the run is a uniform `j`-bit
draw shifted into the accumulator, followed by the run from the full counter. -/
private lemma runKT_build (t : ℕ) (j : ℕ) :
    ∀ (c : Fin (rejWidth t + 1)), (c : ℕ) + j = rejWidth t →
      ∀ (acc : Fin (2 ^ rejWidth t)) (m : ℕ),
      (rejectionMachine t).runKT coinSpec.probHandler (j + m) (c, acc) =
        coinFlips j >>= fun u => (rejectionMachine t).runKT coinSpec.probHandler m
          (Fin.last _, ⟨((acc : ℕ) * 2 ^ j + (u : ℕ)) % 2 ^ rejWidth t,
            Nat.mod_lt _ (Nat.two_pow_pos _)⟩) := by
  induction j with
  | zero =>
    intro c hc acc m
    have hcl : c = Fin.last (rejWidth t) := Fin.ext (by simpa using hc)
    subst hcl
    rw [Nat.zero_add, coinFlips_zero, pure_bind]
    refine congrArg ((rejectionMachine t).runKT coinSpec.probHandler m)
      (Prod.ext rfl (Fin.ext ?_))
    simp [Nat.mod_eq_of_lt acc.isLt]
  | succ j ih =>
    intro c hc acc m
    have hlt : (c : ℕ) < rejWidth t := by omega
    have hfuel : j + 1 + m = (j + m) + 1 := by omega
    rw [hfuel, (rejectionMachine t).runKT_succ_of_output_eq_none _
      (output_eq_none_of_lt t hlt acc) (j + m)]
    have hstep : OracleStrategy.kleisliStep coinSpec.probHandler
        (rejectionMachine t).toStrategy (c, acc) =
        (fun b => (rejectionMachine t).update (c, acc) b) <$>
          coinSpec.probHandler () := rfl
    have hupd : ∀ b : Bool, (rejectionMachine t).update (c, acc) b =
        (⟨(c : ℕ) + 1, Nat.succ_lt_succ hlt⟩,
          ⟨(2 * (acc : ℕ) + b.toNat) % 2 ^ rejWidth t,
            Nat.mod_lt _ (Nat.two_pow_pos _)⟩) := fun b => by
      simp only [rejectionMachine]
      rw [dif_pos hlt]
    rw [hstep, map_bind_eq, coinFlips_succ, bind_assoc]
    refine congrArg (coinSpec.probHandler () >>= ·) (funext fun b => ?_)
    rw [hupd b, ih ⟨(c : ℕ) + 1, Nat.succ_lt_succ hlt⟩
      (by show (c : ℕ) + 1 + j = rejWidth t; omega) _ m, map_bind_eq]
    refine congrArg (coinFlips j >>= ·) (funext fun u => ?_)
    dsimp only
    refine congrArg ((rejectionMachine t).runKT coinSpec.probHandler m)
      (Prod.ext rfl (Fin.ext ?_))
    show ((2 * (acc : ℕ) + b.toNat) % 2 ^ rejWidth t * 2 ^ j + (u : ℕ)) % 2 ^ rejWidth t
      = ((acc : ℕ) * 2 ^ (j + 1) + (b.toNat * 2 ^ j + (u : ℕ))) % 2 ^ rejWidth t
    have h1 : ((2 * (acc : ℕ) + b.toNat) % 2 ^ rejWidth t * 2 ^ j + (u : ℕ))
        ≡ (2 * (acc : ℕ) + b.toNat) * 2 ^ j + (u : ℕ) [MOD 2 ^ rejWidth t] :=
      ((Nat.mod_modEq _ _).mul_right _).add_right _
    have h2 : (2 * (acc : ℕ) + b.toNat) * 2 ^ j + (u : ℕ)
        = (acc : ℕ) * 2 ^ (j + 1) + (b.toNat * 2 ^ j + (u : ℕ)) := by
      rw [pow_succ]
      ring
    calc ((2 * (acc : ℕ) + b.toNat) % 2 ^ rejWidth t * 2 ^ j + (u : ℕ)) % 2 ^ rejWidth t
        = ((2 * (acc : ℕ) + b.toNat) * 2 ^ j + (u : ℕ)) % 2 ^ rejWidth t := h1
      _ = _ := by rw [h2]

/-- The build phase from the initial state, with the accumulator cleaned up. -/
private lemma runKT_init_build (t m : ℕ) :
    (rejectionMachine t).runKT coinSpec.probHandler (rejWidth t + m)
      ((rejectionMachine t).init ()) =
      coinFlips (rejWidth t) >>= fun u =>
        (rejectionMachine t).runKT coinSpec.probHandler m (Fin.last _, u) := by
  rw [show (rejectionMachine t).init () =
    ((0 : Fin (rejWidth t + 1)), ⟨0, Nat.two_pow_pos _⟩) from rfl,
    runKT_build t (rejWidth t) 0 (by simp) _ m]
  refine congrArg (coinFlips (rejWidth t) >>= ·) (funext fun u => ?_)
  dsimp only
  refine congrArg ((rejectionMachine t).runKT coinSpec.probHandler m)
    (Prod.ext rfl (Fin.ext ?_))
  show ((0 : ℕ) * 2 ^ rejWidth t + (u : ℕ)) % 2 ^ rejWidth t = (u : ℕ)
  simp [Nat.mod_eq_of_lt u.isLt]

/-- An accepted full-counter state reads out its value at any fuel. -/
private lemma runKT_accept (t : ℕ) {u : Fin (2 ^ rejWidth t)} (hu : (u : ℕ) ≤ t)
    (m : ℕ) : (rejectionMachine t).runKT coinSpec.probHandler m (Fin.last _, u) =
      pure ⟨u, Nat.lt_succ_of_le hu⟩ := by
  refine (rejectionMachine t).runKT_of_output_eq_some _ ?_ m
  simp only [rejectionMachine]
  rw [if_pos (by simp), dif_pos hu]

private lemma output_reject (t : ℕ) {u : Fin (2 ^ rejWidth t)} (hu : t < (u : ℕ)) :
    (rejectionMachine t).output (Fin.last _, u) = none := by
  simp only [rejectionMachine]
  rw [if_pos (by simp), dif_neg (by omega)]

private lemma kleisliStep_reject (t : ℕ) (u : Fin (2 ^ rejWidth t)) (m : ℕ) :
    OracleStrategy.kleisliStep coinSpec.probHandler (rejectionMachine t).toStrategy
        (Fin.last _, u) >>=
        (rejectionMachine t).runKT coinSpec.probHandler m =
      (rejectionMachine t).runKT coinSpec.probHandler m
        ((rejectionMachine t).init ()) := by
  have hstep : OracleStrategy.kleisliStep coinSpec.probHandler
      (rejectionMachine t).toStrategy (Fin.last _, u) =
      (fun b => (rejectionMachine t).update (Fin.last _, u) b) <$>
        coinSpec.probHandler () := rfl
  have hupd : ∀ b : Bool, (rejectionMachine t).update (Fin.last _, u) b =
      ((0 : Fin (rejWidth t + 1)), ⟨0, Nat.two_pow_pos _⟩) := fun b => by
    simp only [rejectionMachine]
    rw [dif_neg (by simp)]
  rw [hstep, map_bind_eq]
  simp only [hupd]
  exact probHandler_coin_bind_const _

/-- A rejected full-counter state spends one flip restarting. -/
private lemma runKT_reject_succ (t : ℕ) {u : Fin (2 ^ rejWidth t)}
    (hu : t < (u : ℕ)) (m : ℕ) :
    (rejectionMachine t).runKT coinSpec.probHandler (m + 1) (Fin.last _, u) =
      (rejectionMachine t).runKT coinSpec.probHandler m
        ((rejectionMachine t).init ()) := by
  rw [(rejectionMachine t).runKT_succ_of_output_eq_none _ (output_reject t hu) m,
    kleisliStep_reject t u m]

/-- The attempt-block recurrence for the fuelled run: one block peels off as a
uniform draw followed by accept-or-recurse. -/
private lemma runKT_attempt_succ (t k : ℕ) :
    (rejectionMachine t).runKT coinSpec.probHandler
        ((k + 1) * (rejWidth t + 1) + rejWidth t) ((rejectionMachine t).init ()) =
      coinFlips (rejWidth t) >>= acceptOr t
        ((rejectionMachine t).runKT coinSpec.probHandler
          (k * (rejWidth t + 1) + rejWidth t) ((rejectionMachine t).init ())) := by
  have hfuel : (k + 1) * (rejWidth t + 1) + rejWidth t =
      rejWidth t + ((k * (rejWidth t + 1) + rejWidth t) + 1) := by ring
  rw [hfuel, runKT_init_build t _]
  refine congrArg (coinFlips (rejWidth t) >>= ·) (funext fun u => ?_)
  rw [acceptOr]
  rcases Nat.lt_or_ge t (u : ℕ) with hu | hu
  · rw [dif_neg (by omega), runKT_reject_succ t hu]
  · rw [dif_pos hu, runKT_accept t hu]

private lemma runKT_attempt_zero (t : ℕ) :
    (rejectionMachine t).runKT coinSpec.probHandler (0 * (rejWidth t + 1) + rejWidth t)
        ((rejectionMachine t).init ()) =
      coinFlips (rejWidth t) >>= acceptOr t failure := by
  rw [show 0 * (rejWidth t + 1) + rejWidth t = rejWidth t + 0 by ring,
    runKT_init_build t 0]
  refine congrArg (coinFlips (rejWidth t) >>= ·) (funext fun u => ?_)
  rw [acceptOr]
  rcases Nat.lt_or_ge t (u : ℕ) with hu | hu
  · rw [dif_neg (by omega), OracleMachine.runKT_zero, output_reject t hu]
    rfl
  · rw [dif_pos hu, runKT_accept t hu]

/-! ## The rejection rate -/

/-- The per-attempt rejection probability `(2 ^ w - (t + 1)) / 2 ^ w`. -/
noncomputable def rejQ (t : ℕ) : ℝ≥0∞ :=
  ((2 ^ rejWidth t - (t + 1) : ℕ) : ℝ≥0∞) * (((2 ^ rejWidth t : ℕ) : ℝ≥0∞))⁻¹

/-- Minimality of `Nat.size`: each attempt rejects with probability at most `1/2`. -/
lemma rejQ_le_half (t : ℕ) : rejQ t ≤ 2⁻¹ := by
  have hN := two_pow_rejWidth_le t
  have ht1 := lt_two_pow_rejWidth t
  have h2r : 2 * (2 ^ rejWidth t - (t + 1)) ≤ 2 ^ rejWidth t := by omega
  have hcast : (2 : ℝ≥0∞) * ((2 ^ rejWidth t - (t + 1) : ℕ) : ℝ≥0∞) ≤
      ((2 ^ rejWidth t : ℕ) : ℝ≥0∞) := by
    calc (2 : ℝ≥0∞) * ((2 ^ rejWidth t - (t + 1) : ℕ) : ℝ≥0∞)
        = ((2 * (2 ^ rejWidth t - (t + 1)) : ℕ) : ℝ≥0∞) := by push_cast; ring
      _ ≤ _ := Nat.cast_le.mpr h2r
  have key : ((2 ^ rejWidth t - (t + 1) : ℕ) : ℝ≥0∞) ≤
      2⁻¹ * ((2 ^ rejWidth t : ℕ) : ℝ≥0∞) := by
    calc ((2 ^ rejWidth t - (t + 1) : ℕ) : ℝ≥0∞)
        = 2⁻¹ * ((2 : ℝ≥0∞) * ((2 ^ rejWidth t - (t + 1) : ℕ) : ℝ≥0∞)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ofNat_ne_top, one_mul]
      _ ≤ 2⁻¹ * ((2 ^ rejWidth t : ℕ) : ℝ≥0∞) := mul_le_mul' le_rfl hcast
  calc rejQ t ≤ (2⁻¹ * ((2 ^ rejWidth t : ℕ) : ℝ≥0∞)) *
        (((2 ^ rejWidth t : ℕ) : ℝ≥0∞))⁻¹ := mul_le_mul' key le_rfl
    _ = 2⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel
          (Nat.cast_ne_zero.mpr (Nat.two_pow_pos _).ne') (ENNReal.natCast_ne_top _),
          mul_one]

private lemma card_filter_not_le (t : ℕ) :
    (Finset.univ.filter fun u : Fin (2 ^ rejWidth t) => ¬(u : ℕ) ≤ t).card =
      2 ^ rejWidth t - (t + 1) := by
  have hle : (Finset.univ.filter fun u : Fin (2 ^ rejWidth t) => (u : ℕ) ≤ t).card
      = t + 1 := by
    have hset : (Finset.univ.filter fun u : Fin (2 ^ rejWidth t) => (u : ℕ) ≤ t)
        = Finset.Iic ⟨t, lt_two_pow_rejWidth t⟩ := by
      ext u
      simp [Fin.le_def]
    rw [hset, Fin.card_Iic]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (2 ^ rejWidth t))))
    (p := fun u => (u : ℕ) ≤ t)
  rw [Finset.card_univ, Fintype.card_fin] at hsplit
  omega

/-- The missing mass of one attempt block: the rejection rate times the missing mass
of the continuation. -/
private lemma gap_bind_acceptOr (t : ℕ) (X : SPMF (Fin (t + 1))) :
    (coinFlips (rejWidth t) >>= acceptOr t X).gap = rejQ t * X.gap := by
  rw [SPMF.gap_bind, gap_coinFlips, zero_add, tsum_fintype]
  have hterm : ∀ u : Fin (2 ^ rejWidth t),
      coinFlips (rejWidth t) u * (acceptOr t X u).gap =
        ((2 : ℝ≥0∞) ^ rejWidth t)⁻¹ *
          (if (u : ℕ) ≤ t then 0 else X.gap) := fun u => by
    rw [coinFlips_apply, acceptOr]
    rcases Nat.lt_or_ge t (u : ℕ) with hu | hu
    · rw [dif_neg (by omega), if_neg (by omega)]
    · rw [dif_pos hu, if_pos hu, SPMF.gap_pure]
  rw [Finset.sum_congr rfl fun u _ => hterm u, ← Finset.mul_sum, Finset.sum_ite,
    Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul,
    card_filter_not_le t, rejQ,
    show (((2 ^ rejWidth t : ℕ) : ℝ≥0∞))⁻¹ = ((2 : ℝ≥0∞) ^ rejWidth t)⁻¹ by
      congr 1; push_cast; ring]
  ring

/-- Geometric decay of the missing mass along attempt blocks. -/
private lemma gap_runKT_attempts_le (t : ℕ) : ∀ k : ℕ,
    ((rejectionMachine t).runKT coinSpec.probHandler (k * (rejWidth t + 1) + rejWidth t)
      ((rejectionMachine t).init ())).gap ≤ 2⁻¹ ^ (k + 1)
  | 0 => by
    rw [runKT_attempt_zero t, gap_bind_acceptOr]
    calc rejQ t * (failure : SPMF (Fin (t + 1))).gap ≤ 2⁻¹ * 1 :=
        mul_le_mul' (rejQ_le_half t)
          (by rw [SPMF.gap_eq_one_sub_tsum]; exact tsub_le_self)
      _ = 2⁻¹ ^ (0 + 1) := by simp
  | k + 1 => by
    rw [runKT_attempt_succ t k, gap_bind_acceptOr]
    calc rejQ t * _ ≤ 2⁻¹ * 2⁻¹ ^ (k + 1) :=
        mul_le_mul' (rejQ_le_half t) (gap_runKT_attempts_le t k)
      _ = 2⁻¹ ^ (k + 1 + 1) := by rw [← pow_succ']

/-! ## Exact limit uniformity -/

/-- A rejected full-counter state restarts, in the limit. -/
private lemma runLimit_reject (t : ℕ) {u : Fin (2 ^ rejWidth t)} (hu : t < (u : ℕ)) :
    (rejectionMachine t).runLimit coinSpec.probHandler (Fin.last _, u) =
      (rejectionMachine t).runLimit coinSpec.probHandler
        ((rejectionMachine t).init ()) := by
  refine SPMF.ext fun b => ?_
  rw [OracleMachine.runLimit_apply, OracleMachine.runLimit_apply]
  refine le_antisymm (iSup_le fun m => ?_) (iSup_le fun m => ?_)
  · rcases m with _ | m
    · rw [OracleMachine.runKT_zero, output_reject t hu]
      simp
    · rw [runKT_reject_succ t hu m]
      exact le_iSup (fun m => ((rejectionMachine t).runKT coinSpec.probHandler m
        ((rejectionMachine t).init ())) b) m
  · rw [← runKT_reject_succ t hu m]
    exact le_iSup (fun m => ((rejectionMachine t).runKT coinSpec.probHandler m
      (Fin.last _, u)) b) (m + 1)

/-- The limit run satisfies the attempt-block fixpoint equation: one uniform draw,
accept or restart. -/
private lemma runLimit_init_eq (t : ℕ) :
    (rejectionMachine t).runLimit coinSpec.probHandler ((rejectionMachine t).init ()) =
      coinFlips (rejWidth t) >>= acceptOr t
        ((rejectionMachine t).runLimit coinSpec.probHandler
          ((rejectionMachine t).init ())) := by
  refine le_antisymm ?_ ?_
  · refine ωSup_le _ _ fun m => ?_
    calc (rejectionMachine t).runChain coinSpec.probHandler
          ((rejectionMachine t).init ()) m
        ≤ (rejectionMachine t).runKT coinSpec.probHandler (rejWidth t + m)
            ((rejectionMachine t).init ()) :=
          (rejectionMachine t).runKT_monotone _ _ (by omega)
      _ = coinFlips (rejWidth t) >>= fun u =>
            (rejectionMachine t).runKT coinSpec.probHandler m (Fin.last _, u) :=
          runKT_init_build t m
      _ ≤ coinFlips (rejWidth t) >>= acceptOr t
            ((rejectionMachine t).runLimit coinSpec.probHandler
              ((rejectionMachine t).init ())) := by
          refine SPMF.bind_le_bind le_rfl fun u => ?_
          rw [acceptOr]
          rcases Nat.lt_or_ge t (u : ℕ) with hu | hu
          · rw [dif_neg (by omega)]
            calc (rejectionMachine t).runKT coinSpec.probHandler m (Fin.last _, u)
                ≤ (rejectionMachine t).runLimit coinSpec.probHandler (Fin.last _, u) :=
                  (rejectionMachine t).runKT_le_runLimit _ m _
              _ = _ := runLimit_reject t hu
          · rw [dif_pos hu, runKT_accept t hu]
  · have hpt : acceptOr t ((rejectionMachine t).runLimit coinSpec.probHandler
        ((rejectionMachine t).init ())) = fun u =>
        (rejectionMachine t).runLimit coinSpec.probHandler (Fin.last _, u) := by
      funext u
      rw [acceptOr]
      rcases Nat.lt_or_ge t (u : ℕ) with hu | hu
      · rw [dif_neg (by omega), runLimit_reject t hu]
      · rw [dif_pos hu, (rejectionMachine t).runLimit_of_output_eq_some _ (show
          (rejectionMachine t).output (Fin.last _, u) = some ⟨u, Nat.lt_succ_of_le hu⟩ by
            simp only [rejectionMachine]
            rw [if_pos (by simp), dif_pos hu])]
    rw [hpt, show (coinFlips (rejWidth t) >>= fun u =>
        (rejectionMachine t).runLimit coinSpec.probHandler (Fin.last _, u)) =
        ωSup ⟨fun m => coinFlips (rejWidth t) >>= fun u =>
            (rejectionMachine t).runKT coinSpec.probHandler m (Fin.last _, u),
          fun _ _ h => SPMF.bind_le_bind le_rfl fun u =>
            (rejectionMachine t).runKT_monotone _ _ h⟩ from
      SPMF.bind_ωSup _ fun u =>
        (rejectionMachine t).runChain coinSpec.probHandler (Fin.last _, u)]
    refine ωSup_le _ _ fun m => ?_
    calc (coinFlips (rejWidth t) >>= fun u =>
          (rejectionMachine t).runKT coinSpec.probHandler m (Fin.last _, u))
        = (rejectionMachine t).runKT coinSpec.probHandler (rejWidth t + m)
            ((rejectionMachine t).init ()) := (runKT_init_build t m).symm
      _ ≤ _ := (rejectionMachine t).runKT_le_runLimit _ _ _

/-- Pointwise value of the limit run: solving the fixpoint equation gives exact
uniformity. -/
private lemma runLimit_init_apply (t : ℕ) (b : Fin (t + 1)) :
    (rejectionMachine t).runLimit coinSpec.probHandler ((rejectionMachine t).init ()) b
      = ((t + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
  set μ := (rejectionMachine t).runLimit coinSpec.probHandler
    ((rejectionMachine t).init ()) with hμ
  have hsum : ∑ u : Fin (2 ^ rejWidth t), acceptOr t μ u b
      = 1 + ((2 ^ rejWidth t - (t + 1) : ℕ) : ℝ≥0∞) * μ b := by
    have happ : ∀ u : Fin (2 ^ rejWidth t), acceptOr t μ u b =
        if (u : ℕ) ≤ t then (if (u : ℕ) = (b : ℕ) then 1 else 0) else μ b := fun u => by
      rw [acceptOr]
      rcases Nat.lt_or_ge t (u : ℕ) with hu | hu
      · rw [dif_neg (by omega), if_neg (by omega)]
      · rw [dif_pos hu, if_pos hu, SPMF.pure_apply]
        exact if_congr ⟨fun h => by rw [h], fun h => Fin.ext (by simpa using h.symm)⟩
          rfl rfl
    have hone : ∑ u ∈ Finset.univ.filter
        (fun u : Fin (2 ^ rejWidth t) => (u : ℕ) ≤ t),
        (if (u : ℕ) = (b : ℕ) then (1 : ℝ≥0∞) else 0) = 1 := by
      have hb : (b : ℕ) < 2 ^ rejWidth t := by
        have h1 := b.isLt
        have h2 := lt_two_pow_rejWidth t
        omega
      rw [Finset.sum_eq_single (⟨(b : ℕ), hb⟩ : Fin (2 ^ rejWidth t))]
      · simp
      · intro u _ hu
        rw [if_neg fun h => hu (Fin.ext (by simpa using h))]
      · intro h
        exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          simpa using Nat.lt_succ_iff.mp b.isLt⟩) h
    rw [Finset.sum_congr rfl fun u _ => happ u, Finset.sum_ite, hone,
      Finset.sum_const, nsmul_eq_mul, card_filter_not_le t]
  have hterm : ∀ u : Fin (2 ^ rejWidth t),
      coinFlips (rejWidth t) u * acceptOr t μ u b =
        ((2 : ℝ≥0∞) ^ rejWidth t)⁻¹ * acceptOr t μ u b := fun u => by
    rw [coinFlips_apply]
  have hpoint : μ b = ((2 : ℝ≥0∞) ^ rejWidth t)⁻¹ *
      (1 + ((2 ^ rejWidth t - (t + 1) : ℕ) : ℝ≥0∞) * μ b) := by
    conv_lhs => rw [hμ, runLimit_init_eq t, ← hμ]
    rw [SPMF.bind_apply_eq_tsum, tsum_congr hterm, ENNReal.tsum_mul_left,
      tsum_fintype, hsum]
  have hμb_ne_top : μ b ≠ ⊤ := by
    rw [SPMF.apply_eq_toPMF_some]
    exact PMF.apply_ne_top _ _
  have hkey : (2 : ℝ≥0∞) ^ rejWidth t * μ b =
      1 + ((2 ^ rejWidth t - (t + 1) : ℕ) : ℝ≥0∞) * μ b := by
    conv_lhs => rw [hpoint]
    rw [← mul_assoc,
      ENNReal.mul_inv_cancel (pow_ne_zero _ two_ne_zero)
        (ENNReal.pow_ne_top ofNat_ne_top), one_mul]
  have hfin : ((2 ^ rejWidth t - (t + 1) : ℕ) : ℝ≥0∞) * μ b ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hμb_ne_top
  have hcast : ((2 ^ rejWidth t : ℕ) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ rejWidth t := by
    push_cast
    ring
  have hmain : ((t + 1 : ℕ) : ℝ≥0∞) * μ b = 1 := by
    have hle := lt_two_pow_rejWidth t
    have hsub : ((t + 1 : ℕ) : ℝ≥0∞) =
        ((2 ^ rejWidth t : ℕ) : ℝ≥0∞) - ((2 ^ rejWidth t - (t + 1) : ℕ) : ℝ≥0∞) := by
      rw [← ENNReal.natCast_sub]
      congr 1
      omega
    rw [hsub, ENNReal.sub_mul fun _ _ => hμb_ne_top, hcast, hkey,
      ENNReal.add_sub_cancel_right hfin]
  calc μ b = ((t + 1 : ℕ) : ℝ≥0∞)⁻¹ * (((t + 1 : ℕ) : ℝ≥0∞) * μ b) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel
          (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero t)) (ENNReal.natCast_ne_top _),
          one_mul]
    _ = ((t + 1 : ℕ) : ℝ≥0∞)⁻¹ := by rw [hmain, mul_one]

/-- **Exact limit uniformity**: the limit run of the rejection sampler against the
fair coin is exactly the uniform distribution on `Fin (t + 1)`. The "limit of the
distribution" of the potentially non-terminating sampler exists and is the intended
one — as a statement about the semantic limit `OracleMachine.runLimit`, with no
polynomial-time claim attached (see the module docstring). -/
theorem runLimit_rejectionMachine (t : ℕ) :
    (rejectionMachine t).runLimit coinSpec.probHandler ((rejectionMachine t).init ()) =
      𝒟[($ᵗ Fin (t + 1) : ProbComp _)] := by
  refine SPMF.ext fun b => ?_
  rw [runLimit_init_apply t b, evalDist_uniformSample, SPMF.liftM_apply,
    PMF.uniformOfFintype_apply, Fintype.card_fin]

/-- The rejection sampler terminates almost surely against the fair coin. -/
theorem rejectionMachine_asTerminates (t : ℕ) :
    (rejectionMachine t).ASTerminates coinSpec.probHandler
      ((rejectionMachine t).init ()) := by
  rw [OracleMachine.ASTerminates, runLimit_rejectionMachine t, evalDist_uniformSample,
    SPMF.gap_liftM]

/-! ## Distance of the truncated run -/

/-- **Geometric truncation bound**: the strictly fuelled run covering `k + 1` attempt
blocks is missing at most `2⁻⁽ᵏ⁺¹⁾` of its mass. -/
theorem gap_runKT_rejectionMachine_le (t k : ℕ) :
    ((rejectionMachine t).runKT coinSpec.probHandler ((rejWidth t + 1) * (k + 1))
      ((rejectionMachine t).init ())).gap ≤ ((2 : ℝ≥0∞) ^ (k + 1))⁻¹ := by
  have hfuel : k * (rejWidth t + 1) + rejWidth t ≤ (rejWidth t + 1) * (k + 1) := by
    have h : (rejWidth t + 1) * (k + 1) = k * (rejWidth t + 1) + rejWidth t + 1 := by
      ring
    omega
  calc ((rejectionMachine t).runKT coinSpec.probHandler ((rejWidth t + 1) * (k + 1))
        ((rejectionMachine t).init ())).gap
      ≤ ((rejectionMachine t).runKT coinSpec.probHandler
          (k * (rejWidth t + 1) + rejWidth t) ((rejectionMachine t).init ())).gap :=
        SPMF.gap_antitone ((rejectionMachine t).runKT_monotone _ _ hfuel)
    _ ≤ 2⁻¹ ^ (k + 1) := gap_runKT_attempts_le t k
    _ = ((2 : ℝ≥0∞) ^ (k + 1))⁻¹ := (ENNReal.inv_pow).symm

/-- **Truncated rejection sampling is statistically close to uniform**: the strictly
fuelled run at fuel `(rejWidth t + 1) * (k + 1)` is within `2⁻⁽ᵏ⁺¹⁾` of the exact
uniform distribution in extended total-variation distance. This is the form that
enters polynomial-time statements: strict fuel plus an explicit statistical budget
(`OracleMachine.ImplementsWithin`), never an expected-time claim. -/
theorem etvDist_runKT_rejectionMachine_le (t k : ℕ) :
    ((rejectionMachine t).runKT coinSpec.probHandler ((rejWidth t + 1) * (k + 1))
        ((rejectionMachine t).init ())).etvDist 𝒟[($ᵗ Fin (t + 1) : ProbComp _)]
      ≤ ((2 : ℝ≥0∞) ^ (k + 1))⁻¹ := by
  have hle : (rejectionMachine t).runKT coinSpec.probHandler
      ((rejWidth t + 1) * (k + 1)) ((rejectionMachine t).init ()) ≤
      𝒟[($ᵗ Fin (t + 1) : ProbComp _)] := by
    rw [← runLimit_rejectionMachine t]
    exact (rejectionMachine t).runKT_le_runLimit _ _ _
  rw [SPMF.etvDist_eq_gap_sub_of_le hle]
  exact le_trans tsub_le_self (gap_runKT_rejectionMachine_le t k)

end OracleComp
