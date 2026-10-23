/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.TapeFactor
public import HashSig.SLHDSA.SHAKE128s.Proof.Averaging

/-!
# A block of answers, read as a tape of parsed views

`TapeFactor` hands the coverage charge blocks of `List HashOutput`, drawn by `DigestTape.padding`,
and takes the hit relation as a parameter. The FORS machinery states everything about
`ForsDisclosureTape.Tape n = Fin n → View` instead. This file is the one conversion between the
two, and the hit relation `BlockHit` the game needs: a fresh answer whose fourteen FORS leaves are
all disclosed by the block.

`DigestTape.viewTape_uniform` already says a uniform *word* parses to a uniform tape. What is
missing is that `padding` draws a uniform word at all (it draws one answer at a time), and that is
`evalDist_padding_eq_ofFn`, by splitting a uniform function type at its first coordinate.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.BlockViews

open DigestTape TapeFactor

/-! ## A block is a uniform word -/

/-- Uniform sampling of a pair is two independent draws. -/
theorem uniformSample_prod_eq_bind {α β : Type} [SampleableType α] [SampleableType β] :
    ($ᵗ (α × β) : ProbComp (α × β)) =
      (do let left ← $ᵗ α; let right ← $ᵗ β; pure (left, right)) := by
  rw [uniformSample]
  change ((·, ·) <$> ($ᵗ α) <*> ($ᵗ β)) = _
  simp only [seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]

/-- Consing one answer onto a word is a bijection from the pair. -/
theorem cons_bijective (length : Nat) :
    Function.Bijective (fun pair : HashOutput × (Fin length → HashOutput) =>
      Fin.cons pair.1 pair.2 : HashOutput × (Fin length → HashOutput) →
        Fin (length + 1) → HashOutput) := by
  constructor
  · intro left right hsame
    have hhead := congrFun hsame 0
    have htail : ∀ index : Fin length, left.2 index = right.2 index := fun index => by
      have := congrFun hsame index.succ
      simpa using this
    exact Prod.ext (by simpa using hhead) (funext htail)
  · intro word
    exact ⟨(word 0, Fin.tail word), Fin.cons_self_tail word⟩

/-- **A block of independent draws is a uniform word.** `padding` draws one answer at a time;
the FORS machinery wants a function off `Fin length`. They agree. -/
theorem evalDist_padding_eq_ofFn (length : Nat) :
    𝒟[padding length] =
      𝒟[List.ofFn <$> ($ᵗ (Fin length → HashOutput) :
        ProbComp (Fin length → HashOutput))] := by
  induction length with
  | zero =>
    rw [padding, show (List.ofFn : (Fin 0 → HashOutput) → List HashOutput) =
        fun _ => ([] : List HashOutput) from by funext word; simp, map_eq_bind_pure_comp]
    exact (OracleComp.DeferredSampling.evalDist_bind_const_neverFails _ (by simp) _).symm
  | succ remaining ih =>
    have hbijection : 𝒟[(fun pair : HashOutput × (Fin remaining → HashOutput) =>
          Fin.cons pair.1 pair.2) <$>
        ($ᵗ (HashOutput × (Fin remaining → HashOutput)) : ProbComp _)] =
        𝒟[($ᵗ (Fin (remaining + 1) → HashOutput) : ProbComp _)] :=
      evalDist_map_bijective_uniform_cross
        (α := HashOutput × (Fin remaining → HashOutput))
        (β := Fin (remaining + 1) → HashOutput) _ (cons_bijective remaining)
    calc 𝒟[padding (remaining + 1)]
        = 𝒟[($ᵗ HashOutput : ProbComp HashOutput) >>= fun value =>
            padding remaining >>= fun rest => (pure (value :: rest) : ProbComp _)] := rfl
      _ = 𝒟[($ᵗ HashOutput : ProbComp HashOutput) >>= fun value =>
            (List.ofFn <$> ($ᵗ (Fin remaining → HashOutput) : ProbComp _)) >>= fun rest =>
              (pure (value :: rest) : ProbComp _)] := by
          refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun value => ?_
          rw [evalDist_bind, evalDist_bind, ih]
      _ = 𝒟[(fun pair : HashOutput × (Fin remaining → HashOutput) =>
              pair.1 :: List.ofFn pair.2) <$>
            ($ᵗ (HashOutput × (Fin remaining → HashOutput)) : ProbComp _)] := by
          rw [uniformSample_prod_eq_bind]
          simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
      _ = 𝒟[List.ofFn <$> ($ᵗ (Fin (remaining + 1) → HashOutput) : ProbComp _)] := by
          have hmap : 𝒟[List.ofFn <$>
                ((fun pair : HashOutput × (Fin remaining → HashOutput) =>
                  Fin.cons pair.1 pair.2) <$>
                    ($ᵗ (HashOutput × (Fin remaining → HashOutput)) : ProbComp _))] =
              𝒟[List.ofFn <$> ($ᵗ (Fin (remaining + 1) → HashOutput) : ProbComp _)] := by
            rw [evalDist_map, hbijection, evalDist_map]
          refine Eq.trans ?_ hmap
          rw [Functor.map_map]
          refine congrArg evalDist (congrArg (fun step =>
            step <$> ($ᵗ (HashOutput × (Fin remaining → HashOutput)) : ProbComp _)) ?_)
          funext pair
          simp [List.ofFn_succ]

/-! ## The block as a tape -/

/-- **A fresh answer parses to a uniform view.** -/
theorem evalDist_parse_uniform :
    𝒟[MessageDigest.parse <$> ($ᵗ HashOutput : ProbComp HashOutput)] =
      𝒟[($ᵗ MessageDigest.View : ProbComp MessageDigest.View)] := by
  have hsplit : 𝒟[MessageDigest.split <$> ($ᵗ HashOutput : ProbComp HashOutput)] =
      𝒟[($ᵗ (MessageDigest.View × (BitVec 2 × BitVec 7)) : ProbComp _)] :=
    evalDist_map_bijective_uniform_cross (α := HashOutput)
      (β := MessageDigest.View × (BitVec 2 × BitVec 7))
      MessageDigest.split MessageDigest.split_bijective
  calc 𝒟[MessageDigest.parse <$> ($ᵗ HashOutput : ProbComp HashOutput)]
      = 𝒟[Prod.fst <$> (MessageDigest.split <$> ($ᵗ HashOutput : ProbComp HashOutput))] := by
        rw [Functor.map_map]
        rfl
    _ = 𝒟[Prod.fst <$> ($ᵗ (MessageDigest.View × (BitVec 2 × BitVec 7)) : ProbComp _)] := by
        rw [evalDist_map, hsplit, ← evalDist_map]
    _ = _ := evalDist_map_fst_uniformSample_prod

/-- A block of answers, read as a tape of parsed FORS views. Cells past the block's end read as
a default, which never happens where the charge looks: it reads cell `index` only when the run
recorded an answer there. -/
def blockTape (length : Nat) (block : List HashOutput) : ForsDisclosureTape.Tape length :=
  fun index => MessageDigest.parse (block.getD index.val default)

/-- **A drawn block is a uniform tape.** -/
theorem evalDist_blockTape (length : Nat) :
    𝒟[blockTape length <$> padding length] =
      𝒟[($ᵗ (ForsDisclosureTape.Tape length) :
        ProbComp (ForsDisclosureTape.Tape length))] := by
  calc 𝒟[blockTape length <$> padding length]
      = 𝒟[blockTape length <$>
          (List.ofFn <$> ($ᵗ (Fin length → HashOutput) : ProbComp _))] := by
        rw [evalDist_map, evalDist_padding_eq_ofFn length, ← evalDist_map]
    _ = 𝒟[(fun word index => MessageDigest.parse (word index)) <$>
          ($ᵗ (Fin length → HashOutput) : ProbComp _)] := by
        rw [Functor.map_map]
        refine congrArg evalDist (congrArg (fun step =>
          step <$> ($ᵗ (Fin length → HashOutput) : ProbComp _)) ?_)
        funext word
        funext index
        simp [blockTape, List.getD_eq_getElem?_getD]
    _ = _ := viewTape_uniform length

/-! ## The hit relation the game needs -/

/-- An answer whose fourteen FORS leaves are all disclosed by the block. -/
def BlockHit (length : Nat) (block : List HashOutput) (value : HashOutput) : Prop :=
  ForsCoverage.Covered (ForsDisclosureTape.disclosures (blockTape length block))
    (MessageDigest.parse value)

variable {σ : Type} [RecorderView.CacheView σ]

open scoped Classical in
/-- Expectations move through a reshaping of the outcome. -/
theorem tsum_probOutput_map {β γ : Type} [DecidableEq γ] (run : ProbComp β) (reshape : β → γ)
    (weight : γ → ℝ≥0∞) :
    ∑' value, Pr{let x ← reshape <$> run}[x = value] * weight value =
      ∑' value, Pr{let x ← run}[x = value] * weight (reshape value) := by
  classical
  calc ∑' value, Pr{let x ← reshape <$> run}[x = value] * weight value
      = ∑' value, (∑' source, if value = reshape source then Pr{let x ← run}[x = source] else 0) *
          weight value :=
        tsum_congr fun value => by rw [probOutput_map_eq_tsum_ite]
    _ = ∑' value, ∑' source,
          (if value = reshape source then Pr{let x ← run}[x = source] else 0) * weight value :=
        tsum_congr fun value => ENNReal.tsum_mul_right.symm
    _ = ∑' source, ∑' value,
          (if value = reshape source then Pr{let x ← run}[x = source] else 0) * weight value :=
        ENNReal.tsum_comm
    _ = ∑' source, Pr{let x ← run}[x = source] * weight (reshape source) :=
        tsum_congr fun source => by
          rw [tsum_eq_single (reshape source)
            (fun other hother => by rw [if_neg hother, zero_mul]), if_pos rfl]

end SlhDsaSecurity.BlockViews
