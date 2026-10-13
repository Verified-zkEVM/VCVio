/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.ReductionGames.SplicedChain
import all HashSig.GXMSS.Security.ReductionGames.SourceGames
import all HashSig.GXMSS.Security.ReductionGames.GuessingGames
import all HashSig.GXMSS.Security.ReductionGames.CollisionReductions
import all HashSig.GXMSS.Security.ReductionGames.SplicedChain

/-!
# Chain hybrid measure bridges

Coordinate resampling and finite telescoping compare returned winning measures across
the chain hybrid. The undetectability reductions sample their challenge before seed reveal.
-/

public section

namespace GXMSS.ReductionGames

open Encoding ENNReal OracleComp OracleSpec Security TweakableHash

variable {PP T X H M R E S : Type} {h w v n radix : ℕ}

/-- The nested finite start sampler has the uniform product measure on complete arrays. -/
private theorem sampleStarts_uniform_measure [SampleableType H]
    [MeasurableSpace H] [MeasurableSingletonClass H] :
    𝒟[GXMSS.sampleStarts H h v] = ProbabilityTheory.uniformOn Set.univ := by
  classical
  unfold GXMSS.sampleStarts
  exact evalDist_mOfFn_const_uniform (2 ^ h)
    (Fin.mOfFn v (fun _ => ($ᵗ H : ProbComp H)))
    (evalDist_mOfFn_const_uniform v ($ᵗ H)
      SampleableType.evalDist_uniformSample)

/-- Refreshing one independent start coordinate preserves the complete start-array measure. -/
private theorem sampleStarts_coordinate_resampling [SampleableType H]
    (ep : Epoch h) (i : Fin v) :
    let : MeasurableSpace H := ⊤
    𝒟[do
      let x ← ($ᵗ H : ProbComp H)
      let starts ← GXMSS.sampleStarts H h v
      return Function.update starts ep (Function.update (starts ep) i x)] =
      𝒟[GXMSS.sampleStarts H h v] := by
  classical
  let : MeasurableSpace H := ⊤
  let Flat := Epoch h × Fin v → H
  let Nested := Epoch h → Fin v → H
  let e : Flat ≃ Nested := Equiv.curry (Epoch h) (Fin v) H
  have hvalue : 𝒟[($ᵗ H : ProbComp H)] = ProbabilityTheory.uniformOn Set.univ :=
    SampleableType.evalDist_uniformSample
  have hflat : 𝒟[($ᵗ Flat : ProbComp Flat)] =
      ProbabilityTheory.uniformOn Set.univ :=
    SampleableType.evalDist_uniformSample
  have hnested : 𝒟[GXMSS.sampleStarts H h v] =
      ProbabilityTheory.uniformOn Set.univ := sampleStarts_uniform_measure
  have hmap : 𝒟[e <$> ($ᵗ Flat : ProbComp Flat)] =
      𝒟[GXMSS.sampleStarts H h v] := by
    rw [evalDist_map_of_discrete, hflat,
      ProbabilityTheory.uniformOn_univ_map_equiv e, hnested]
  have hupdate : ∀ (g : Flat) (x : H),
      e (Function.update g (ep, i) x) =
        Function.update (e g) ep (Function.update (e g ep) i x) := by
    intro g x
    funext ep' i'
    change Function.update g (ep, i) x (ep', i') =
      Function.update (e g) ep (Function.update (e g ep) i x) ep' i'
    by_cases hep : ep' = ep
    · subst ep'
      by_cases hi : i' = i
      · subst i'; simp [Function.update]
      · simp [Function.update, hi]
        rfl
    · simp [Function.update, hep]
      rfl
  have hflatUpdate := evalDist_bind_bind_update
    ($ᵗ H : ProbComp H) ($ᵗ Flat : ProbComp Flat)
    hvalue hflat (ep, i) (fun g => pure (e g))
  have hinner (x : H) :
      𝒟[GXMSS.sampleStarts H h v >>= fun starts =>
        pure (Function.update starts ep (Function.update (starts ep) i x))] =
      𝒟[($ᵗ Flat : ProbComp Flat) >>= fun g =>
        pure (e (Function.update g (ep, i) x))] := by
    have hcross := evalDist_bind_bijective_uniform_cross
      ($ᵗ Flat : ProbComp Flat) (GXMSS.sampleStarts H h v)
      hflat hnested e e.bijective
      (fun starts => pure
        (Function.update starts ep (Function.update (starts ep) i x)))
    simp_rw [← hupdate] at hcross
    exact hcross.symm
  calc
    𝒟[do
      let x ← ($ᵗ H : ProbComp H)
      let starts ← GXMSS.sampleStarts H h v
      return Function.update starts ep (Function.update (starts ep) i x)]
        = 𝒟[do
          let x ← ($ᵗ H : ProbComp H)
          let g ← ($ᵗ Flat : ProbComp Flat)
          return e (Function.update g (ep, i) x)] := by
            rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]
            simp_rw [hinner]
    _ = 𝒟[($ᵗ Flat : ProbComp Flat) >>= fun g => pure (e g)] := hflatUpdate
    _ = 𝒟[GXMSS.sampleStarts H h v] := by
      rw [map_eq_bind_pure_comp] at hmap
      exact hmap

/-- The refreshed start law remains equal under any returned continuation, including loss. -/
private theorem sampleStarts_coordinate_resampling_bind [SampleableType H]
    {α : Type} [MeasurableSpace α]
    (ep : Epoch h) (i : Fin v)
    (f : (Epoch h → Fin v → H) → ProbComp α) :
    let : MeasurableSpace H := ⊤
    𝒟[do
      let x ← ($ᵗ H : ProbComp H)
      let starts ← GXMSS.sampleStarts H h v
      f (Function.update starts ep (Function.update (starts ep) i x))] =
    𝒟[GXMSS.sampleStarts H h v >>= f] := by
  classical
  let : MeasurableSpace H := ⊤
  have hrefresh := sampleStarts_coordinate_resampling (H := H) ep i
  have hprogram :
      (do
        let x ← ($ᵗ H : ProbComp H)
        let starts ← GXMSS.sampleStarts H h v
        f (Function.update starts ep (Function.update (starts ep) i x))) =
      (do
        let x ← ($ᵗ H : ProbComp H)
        let starts ← GXMSS.sampleStarts H h v
        pure (Function.update starts ep (Function.update (starts ep) i x))) >>= f := by
    simp only [bind_assoc, pure_bind]
  rw [hprogram, evalDist_bind_of_discrete, hrefresh,
    ← evalDist_bind_of_discrete]

/-- Pointwise equality of returned event masses integrates over a common discrete draw. -/
private theorem evalDist_bind_event_eq_of_discrete
    {α β : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    [MeasurableSpace β]
    (mx : ProbComp α) (f g : α → ProbComp β)
    (event : Set β) (hevent : MeasurableSet event)
    (hfg : ∀ a, 𝒟[f a] event = 𝒟[g a] event) :
    𝒟[mx >>= f] event = 𝒟[mx >>= g] event := by
  apply le_antisymm
  · exact evalDist_bind_apply_mono_of_discrete mx f g hevent
      (fun a => (hfg a).le)
  · exact evalDist_bind_apply_mono_of_discrete mx g f hevent
      (fun a => (hfg a).ge)

/-- A position-zero splice never reads its old selected start at any positive chain position. -/
private theorem splicedChainValue_zero_start_update
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (guess : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H) (x : H)
    (ep : Epoch h) (i : Fin v) (position : ℕ)
    (hzero : (guessedPosition guess).val = 0) (hpos : 0 < position) :
    splicedChainValue hash pp guess answer
      (Function.update starts (guessedEpoch guess)
        (Function.update (starts (guessedEpoch guess)) (guessedChain guess) x))
      ep i position =
    splicedChainValue hash pp guess answer starts ep i position := by
  unfold splicedChainValue
  by_cases htarget : ep = guessedEpoch guess ∧ i = guessedChain guess
  · have hnot : ¬position < (guessedPosition guess).val + 1 := by omega
    simp [htarget, hnot]
  · have hstart :
        Function.update starts (guessedEpoch guess)
          (Function.update (starts (guessedEpoch guess)) (guessedChain guess) x)
          ep i = starts ep i := by
      by_cases he : ep = guessedEpoch guess
      · subst ep
        have hi : i ≠ guessedChain guess := by
          intro hi; exact htarget ⟨rfl, hi⟩
        simp [Function.update, hi]
      · simp [Function.update, he]
    simp [htarget, hstart]

/-- Updating the old selected start leaves the endpoint array of a zero splice fixed. -/
private theorem splicedEndpoints_zero_start_update
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (guess : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H) (x : H)
    (hzero : (guessedPosition guess).val = 0) (hn : 0 < 2 ^ w - 1) :
    splicedEndpoints hash pp guess answer
      (Function.update starts (guessedEpoch guess)
        (Function.update (starts (guessedEpoch guess)) (guessedChain guess) x)) =
      splicedEndpoints hash pp guess answer starts := by
  funext ep i
  exact splicedChainValue_zero_start_update hash pp guess answer starts x ep i
    (2 ^ w - 1) hzero hn

/-- Every surviving selected-epoch signature at a zero splice has a positive selected digit. -/
private theorem splicedSignatureOfWord_zero_start_update
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (guess : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H) (x : H)
    (ep : Epoch h) (wr : Codeword v (2 ^ w) × R)
    (hzero : (guessedPosition guess).val = 0) (hn : 0 < 2 ^ w - 1)
    (hword : ep = guessedEpoch guess →
      0 < (wr.1 (guessedChain guess)).val) :
    splicedSignatureOfWord hash pp guess answer
      (Function.update starts (guessedEpoch guess)
        (Function.update (starts (guessedEpoch guess)) (guessedChain guess) x))
      (splicedEndpoints hash pp guess answer
        (Function.update starts (guessedEpoch guess)
          (Function.update (starts (guessedEpoch guess)) (guessedChain guess) x))) ep wr =
    splicedSignatureOfWord hash pp guess answer starts
      (splicedEndpoints hash pp guess answer starts) ep wr := by
  rw [splicedEndpoints_zero_start_update hash pp guess answer starts x hzero hn]
  have hots : (fun i => splicedChainValue hash pp guess answer
      (Function.update starts (guessedEpoch guess)
        (Function.update (starts (guessedEpoch guess)) (guessedChain guess) x))
      ep i (wr.1 i)) =
      (fun i => splicedChainValue hash pp guess answer starts ep i (wr.1 i)) := by
    funext i
    by_cases ht : ep = guessedEpoch guess ∧ i = guessedChain guess
    · exact splicedChainValue_zero_start_update hash pp guess answer starts x ep i
        (wr.1 i) hzero (by simpa only [ht.2] using hword ht.1)
    · unfold splicedChainValue
      have hstart :
          Function.update starts (guessedEpoch guess)
            (Function.update (starts (guessedEpoch guess)) (guessedChain guess) x)
            ep i = starts ep i := by
        by_cases he : ep = guessedEpoch guess
        · subst ep
          have hi : i ≠ guessedChain guess := by
            intro hi; exact ht ⟨rfl, hi⟩
          simp [Function.update, hi]
        · simp [Function.update, he]
      simp [ht, hstart]
  simp only [splicedSignatureOfWord, hots]

/-- At a zero splice the filtered signing handler is independent of the old selected start. -/
private theorem filteredSplicedSigningOracle_zero_start_update
    [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (pp : PP) (selector guess : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H) (x : H)
    (hzero : (guessedPosition guess).val = 0) (hn : 0 < 2 ^ w - 1)
    (hepoch : guessedEpoch selector = guessedEpoch guess)
    (hchain : guessedChain selector = guessedChain guess) :
    filteredSplicedSigningOracle hash enc K pp selector guess answer
      (Function.update starts (guessedEpoch guess)
        (Function.update (starts (guessedEpoch guess)) (guessedChain guess) x))
      (splicedEndpoints hash pp guess answer
        (Function.update starts (guessedEpoch guess)
          (Function.update (starts (guessedEpoch guess)) (guessedChain guess) x))) =
    filteredSplicedSigningOracle hash enc K pp selector guess answer starts
      (splicedEndpoints hash pp guess answer starts) := by
  rw [splicedEndpoints_zero_start_update hash pp guess answer starts x hzero hn]
  funext q state
  cases state with
  | none => rfl
  | some history =>
    rcases q with ⟨ep, msg⟩
    by_cases hused : history ep = none
    · simp only [filteredSplicedSigningOracle, hused]
      apply bind_congr
      intro wr
      cases wr with
      | none => rfl
      | some value =>
        by_cases hbad : ep = guessedEpoch selector ∧
            (value.1 (guessedChain selector)).val < (guessedPosition selector).val + 1
        · simp [hbad]
        · have hword : ep = guessedEpoch guess →
              0 < (value.1 (guessedChain guess)).val := by
            intro hep
            have hnot : ¬(value.1 (guessedChain selector)).val <
                (guessedPosition selector).val + 1 := by
              intro hlt; exact hbad ⟨by simpa only [hepoch] using hep, hlt⟩
            rw [hchain] at hnot
            omega
          have hsig := splicedSignatureOfWord_zero_start_update hash pp guess answer
            starts x ep value hzero hn hword
          rw [splicedEndpoints_zero_start_update hash pp guess answer starts x
            hzero hn] at hsig
          simp only [hsig]
    · cases hrecord : history ep with
      | none => exact False.elim (hused hrecord)
      | some record => simp [filteredSplicedSigningOracle, hrecord]

/-- The zero-cut filtered winning mass is independent of the old selected start. -/
private theorem runFilteredSpliced_zero_start_update_mass
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) (pp : PP)
    (selector guess : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H) (x : H)
    (hzero : (guessedPosition guess).val = 0) (hn : 0 < 2 ^ w - 1)
    (hepoch : guessedEpoch selector = guessedEpoch guess)
    (hchain : guessedChain selector = guessedChain guess) :
    𝒟[(fun out => out.elim false
      (fun result => jointChainObservation hash enc K (selector, result))) <$>
      runFilteredSpliced hash enc K adv pp selector guess answer
        (Function.update starts (guessedEpoch guess)
          (Function.update (starts (guessedEpoch guess)) (guessedChain guess) x))]
      {true} =
    𝒟[(fun out => out.elim false
      (fun result => jointChainObservation hash enc K (selector, result))) <$>
      runFilteredSpliced hash enc K adv pp selector guess answer starts] {true} := by
  have hend := splicedEndpoints_zero_start_update hash pp guess answer starts x hzero hn
  have hhandler := filteredSplicedSigningOracle_zero_start_update
    hash enc K pp selector guess answer starts x hzero hn hepoch hchain
  rw [hend] at hhandler
  apply congrArg (fun mx : ProbComp Bool => 𝒟[mx] {true})
  unfold runFilteredSpliced
  dsimp only
  rw [hend, hhandler]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc]
  apply bind_congr
  intro z
  cases z with
  | mk forgery state =>
    cases state <;> rfl

/-- At a fixed seed and selector, a real first-step challenge can be sampled independently of
the otherwise unused old selected start, without changing returned selected winning mass. -/
private theorem filteredZero_real_source_mass
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) (pp : PP)
    (selector splice : Guess h w v)
    (hzero : (guessedPosition splice).val = 0) (hn : 0 < 2 ^ w - 1)
    (hepoch : guessedEpoch selector = guessedEpoch splice)
    (hchain : guessedChain selector = guessedChain splice) :
    𝒟[do
      let starts ← GXMSS.sampleStarts H h v
      let answer := hash.chain pp (guessedEpoch splice) (guessedChain splice)
        0 1 (starts (guessedEpoch splice) (guessedChain splice))
      let out ← runFilteredSpliced hash enc K adv pp selector splice answer starts
      return out.elim false
        (fun result => jointChainObservation hash enc K (selector, result))] {true} =
    𝒟[do
      let x ← ($ᵗ H : ProbComp H)
      let starts ← GXMSS.sampleStarts H h v
      let answer := hash.chain pp (guessedEpoch splice) (guessedChain splice) 0 1 x
      let out ← runFilteredSpliced hash enc K adv pp selector splice answer starts
      return out.elim false
        (fun result => jointChainObservation hash enc K (selector, result))] {true} := by
  classical
  let : MeasurableSpace H := ⊤
  let F : H → (Epoch h → Fin v → H) → ProbComp Bool := fun answer starts =>
    (fun out => out.elim false
      (fun result => jointChainObservation hash enc K (selector, result))) <$>
      runFilteredSpliced hash enc K adv pp selector splice answer starts
  have hpoint (x : H) (starts : Epoch h → Fin v → H) :
      𝒟[F (hash.chain pp (guessedEpoch splice) (guessedChain splice) 0 1
        ((Function.update starts (guessedEpoch splice)
          (Function.update (starts (guessedEpoch splice)) (guessedChain splice) x))
          (guessedEpoch splice) (guessedChain splice)))
        (Function.update starts (guessedEpoch splice)
          (Function.update (starts (guessedEpoch splice)) (guessedChain splice) x))]
        {true} =
      𝒟[F (hash.chain pp (guessedEpoch splice) (guessedChain splice) 0 1 x) starts]
        {true} := by
    simp only [Function.update_self]
    exact runFilteredSpliced_zero_start_update_mass hash enc K adv pp selector splice
      (hash.chain pp (guessedEpoch splice) (guessedChain splice) 0 1 x)
      starts x hzero hn hepoch hchain
  have hresample := sampleStarts_coordinate_resampling_bind
    (H := H) (α := Bool) (guessedEpoch splice) (guessedChain splice)
    (fun starts => F (hash.chain pp (guessedEpoch splice) (guessedChain splice) 0 1
      (starts (guessedEpoch splice) (guessedChain splice))) starts)
  change 𝒟[($ᵗ H : ProbComp H) >>= fun x =>
    GXMSS.sampleStarts H h v >>= fun starts =>
      F (hash.chain pp (guessedEpoch splice) (guessedChain splice) 0 1
        ((Function.update starts (guessedEpoch splice)
          (Function.update (starts (guessedEpoch splice)) (guessedChain splice) x))
          (guessedEpoch splice) (guessedChain splice)))
        (Function.update starts (guessedEpoch splice)
          (Function.update (starts (guessedEpoch splice)) (guessedChain splice) x))] =
    𝒟[GXMSS.sampleStarts H h v >>= fun starts =>
      F (hash.chain pp (guessedEpoch splice) (guessedChain splice) 0 1
        (starts (guessedEpoch splice) (guessedChain splice))) starts] at hresample
  have hcouple : 𝒟[GXMSS.sampleStarts H h v >>= fun starts =>
      F (hash.chain pp (guessedEpoch splice) (guessedChain splice) 0 1
        (starts (guessedEpoch splice) (guessedChain splice))) starts] {true} =
    𝒟[($ᵗ H : ProbComp H) >>= fun x =>
      GXMSS.sampleStarts H h v >>= fun starts =>
        F (hash.chain pp (guessedEpoch splice) (guessedChain splice) 0 1 x) starts]
      {true} := by
   calc
    _ = 𝒟[($ᵗ H : ProbComp H) >>= fun x =>
      GXMSS.sampleStarts H h v >>= fun starts =>
        F (hash.chain pp (guessedEpoch splice) (guessedChain splice) 0 1
          ((Function.update starts (guessedEpoch splice)
            (Function.update (starts (guessedEpoch splice)) (guessedChain splice) x))
            (guessedEpoch splice) (guessedChain splice)))
          (Function.update starts (guessedEpoch splice)
            (Function.update (starts (guessedEpoch splice)) (guessedChain splice) x))]
        {true} := congrArg (· {true}) hresample.symm
    _ = 𝒟[($ᵗ H : ProbComp H) >>= fun x =>
      GXMSS.sampleStarts H h v >>= fun starts =>
        F (hash.chain pp (guessedEpoch splice) (guessedChain splice) 0 1 x) starts]
        {true} := by
      apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
      intro x
      apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
      intro starts
      exact hpoint x starts
  simpa only [F, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    using hcouple

/-- Advancing the filtered honest response from the first positive step to the selected cut
preserves the full adaptive filtered computation, including its absorbing abort state. -/
private theorem runFilteredSpliced_honest_from_zero
    [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) (pp : PP)
    (selector : Guess h w v) (starts : Epoch h → Fin v → H)
    (hn : 0 < 2 ^ w - 1) :
    runFilteredSpliced hash enc K adv pp selector
      (guessedEpoch selector, guessedChain selector, ⟨0, hn⟩)
      (hash.chain pp (guessedEpoch selector) (guessedChain selector) 0 1
        (starts (guessedEpoch selector) (guessedChain selector))) starts =
    runFilteredSpliced hash enc K adv pp selector selector
      (hash.chain pp (guessedEpoch selector) (guessedChain selector) 0
        ((guessedPosition selector).val + 1)
        (starts (guessedEpoch selector) (guessedChain selector))) starts := by
  let g := (guessedPosition selector).val
  let ep := guessedEpoch selector
  let i := guessedChain selector
  let start := starts ep i
  let splice (j : ℕ) (hj : j ≤ g) : Guess h w v :=
    (ep, i, ⟨j, lt_of_le_of_lt hj (guessedPosition selector).isLt⟩)
  have hiter : ∀ j (hj : j ≤ g),
      runFilteredSpliced hash enc K adv pp selector (splice 0 (by omega))
        (hash.chain pp ep i 0 1 start) starts =
      runFilteredSpliced hash enc K adv pp selector (splice j hj)
        (hash.chain pp ep i 0 (j + 1) start) starts := by
    intro j
    induction j with
    | zero =>
      intro hj
      rfl
    | succ j ih =>
      intro hj
      have hjprev : j ≤ g := by omega
      have hnext := runFilteredSpliced_advance hash enc K adv pp selector
        (splice j hjprev) (splice (j + 1) hj)
        (hash.chain pp ep i 0 (j + 1) start) starts
        (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
        (by change (⟨j + 1, _⟩ : Fin (2 ^ w - 1)) ≤ guessedPosition selector
            exact Fin.le_iff_val_le_val.mpr hj)
      have hchain : hash.chain pp ep i (j + 1) 1
          (hash.chain pp ep i 0 (j + 1) start) =
          hash.chain pp ep i 0 (j + 1 + 1) start := by
        simpa only [Nat.zero_add] using
          (hash.chain_add pp ep i 0 (j + 1) 1 start).symm
      simp only [splice, guessedEpoch, guessedChain, guessedPosition] at hnext
      rw [hchain] at hnext
      simpa only [Nat.succ_eq_add_one] using (ih hjprev).trans hnext
  have hzero : splice 0 (by omega) =
      (ep, i, (⟨0, hn⟩ : Fin (2 ^ w - 1))) := by
    apply Prod.ext
    · rfl
    · apply Prod.ext <;> rfl
  have hfinal : splice g (Nat.le_refl g) = selector := by
    rcases selector with ⟨⟨ep', i'⟩, pos⟩
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Fin.ext
        rfl
  simpa only [hzero, hfinal, ep, i, g, start] using hiter g (Nat.le_refl g)

/-- At an honest cut response, the full adaptive spliced interaction is the source interaction
with the same fixed keys and exactly the same optional signing law. -/
private theorem runSpliced_honest
    [SampleableType H] [SampleableType R] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) (pp : PP)
    (guess : Guess h w v) (starts : Epoch h → Fin v → H) :
    runSpliced hash enc K adv pp guess
      (hash.chain pp (guessedEpoch guess) (guessedChain guess) 0
        ((guessedPosition guess).val + 1)
        (starts (guessedEpoch guess) (guessedChain guess))) starts =
      runWithKeys hash enc K adv
        (GXMSS.keys hash pp starts).1 (GXMSS.keys hash pp starts).2 := by
  unfold runSpliced runWithKeys
  rw [show splicedEndpoints hash pp guess
      (hash.chain pp (guessedEpoch guess) (guessedChain guess) 0
        ((guessedPosition guess).val + 1)
        (starts (guessedEpoch guess) (guessedChain guess))) starts =
      GXMSS.endpoints hash pp starts from
        splicedEndpoints_honest hash pp guess starts]
  simp only [GXMSS.keys]
  rw [splicedSigningOracle_honest hash enc K pp guess starts]

/-- The source experiment written with an honest positive-position splice. The seed, starts,
retry law and adaptive signing calls are exactly those of the original Game 5 run. -/
private def jointHonestSpliceProgram
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq R] [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) : ProbComp Bool := do
  let guess ← $ᵗ (Guess h w v)
  let pp ← hash.thf.seedGen
  let starts ← GXMSS.sampleStarts H h v
  let answer := hash.chain pp (guessedEpoch guess) (guessedChain guess) 0
    ((guessedPosition guess).val + 1)
    (starts (guessedEpoch guess) (guessedChain guess))
  let out ← runSpliced hash enc K adv pp guess answer starts
  return jointChainObservation hash enc K (guess, out)

private theorem jointHonestSpliceProgram_eq_source
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq R] [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SchemeAdversary PP H M R h v) :
    jointHonestSpliceProgram hash enc K adv =
      jointChainObservation hash enc K <$> gameFive hash enc K hv hw adv := by
  unfold jointHonestSpliceProgram gameFive sourceProgram GXMSS.keygen
  simp only [bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp_def]
  apply bind_congr
  intro guess
  apply bind_congr
  intro pp
  apply bind_congr
  intro starts
  rw [runSpliced_honest hash enc K adv pp guess starts]

private def jointFilteredHonestProgram
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq R] [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) : ProbComp Bool := do
  let guess ← $ᵗ (Guess h w v)
  let pp ← hash.thf.seedGen
  let starts ← GXMSS.sampleStarts H h v
  let answer := hash.chain pp (guessedEpoch guess) (guessedChain guess) 0
    ((guessedPosition guess).val + 1)
    (starts (guessedEpoch guess) (guessedChain guess))
  let out ← runFilteredSpliced hash enc K adv pp guess guess answer starts
  return out.elim false
    (fun result => jointChainObservation hash enc K (guess, result))

private def jointZeroRealProgram
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq R] [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) : ProbComp Bool := do
  let guess ← $ᵗ (Guess h w v)
  let pp ← hash.thf.seedGen
  let x ← ($ᵗ H : ProbComp H)
  let starts ← GXMSS.sampleStarts H h v
  let zero : Guess h w v :=
    (guessedEpoch guess, guessedChain guess,
      ⟨0, Nat.pos_of_ne_zero (NeZero.ne (2 ^ w - 1))⟩)
  let answer := hash.chain pp (guessedEpoch guess) (guessedChain guess) 0 1 x
  let out ← runFilteredSpliced hash enc K adv pp guess zero answer starts
  return out.elim false
    (fun result => jointChainObservation hash enc K (guess, result))

private def jointZeroRealNormalized
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq R] [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) : ProbComp Bool := do
  let pp ← hash.thf.seedGen
  let guess ← $ᵗ (Guess h w v)
  let starts ← GXMSS.sampleStarts H h v
  let x ← ($ᵗ H : ProbComp H)
  let zero : Guess h w v :=
    (guessedEpoch guess, guessedChain guess,
      ⟨0, Nat.pos_of_ne_zero (NeZero.ne (2 ^ w - 1))⟩)
  let answer := hash.chain pp (guessedEpoch guess) (guessedChain guess) 0 1 x
  let out ← runFilteredSpliced hash enc K adv pp guess zero answer starts
  return out.elim false
    (fun result => jointChainObservation hash enc K (guess, result))

private theorem jointZeroRealProgram_eq_normalized
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq R] [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) :
    𝒟[jointZeroRealProgram hash enc K adv] =
      𝒟[jointZeroRealNormalized hash enc K adv] := by
  unfold jointZeroRealProgram jointZeroRealNormalized
  rw [OracleComp.evalDist_bind_bind_swap
    ($ᵗ (Guess h w v) : ProbComp (Guess h w v)) hash.thf.seedGen]
  apply evalDist_bind_congr
  intro pp
  apply evalDist_bind_congr
  intro guess
  exact OracleComp.evalDist_bind_bind_swap ($ᵗ H : ProbComp H)
    (GXMSS.sampleStarts H h v) _

/-- Filtering preserves the unconditioned selected source mass after all outer draws. -/
private theorem jointHonestSplice_mass_eq_filtered
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq R] [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) :
    𝒟[jointHonestSpliceProgram hash enc K adv] {true} =
      𝒟[jointFilteredHonestProgram hash enc K adv] {true} := by
  let : MeasurableSpace PP := ⊤
  let : MeasurableSpace (Epoch h → Fin v → H) := ⊤
  unfold jointHonestSpliceProgram jointFilteredHonestProgram
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro guess
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro pp
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro starts
  simpa only [map_eq_bind_pure_comp, Function.comp_def] using
    runSpliced_selectedMass_eq_filtered hash enc K adv pp guess guess
      (hash.chain pp (guessedEpoch guess) (guessedChain guess) 0
        ((guessedPosition guess).val + 1)
        (starts (guessedEpoch guess) (guessedChain guess))) starts

/-- The filtered source mass equals the independently sampled real zero-cut hybrid. -/
private theorem jointFilteredHonest_mass_eq_zeroReal
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq R] [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) :
    𝒟[jointFilteredHonestProgram hash enc K adv] {true} =
      𝒟[jointZeroRealProgram hash enc K adv] {true} := by
  let : MeasurableSpace PP := ⊤
  let : MeasurableSpace H := ⊤
  let : MeasurableSpace (Epoch h → Fin v → H) := ⊤
  have hn : 0 < 2 ^ w - 1 := Nat.pos_of_ne_zero (NeZero.ne (2 ^ w - 1))
  unfold jointFilteredHonestProgram jointZeroRealProgram
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro guess
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro pp
  let zero : Guess h w v :=
    (guessedEpoch guess, guessedChain guess, ⟨0, hn⟩)
  have hcut : 𝒟[do
      let starts ← GXMSS.sampleStarts H h v
      let answer := hash.chain pp (guessedEpoch guess) (guessedChain guess) 0
        ((guessedPosition guess).val + 1)
        (starts (guessedEpoch guess) (guessedChain guess))
      let out ← runFilteredSpliced hash enc K adv pp guess guess answer starts
      return out.elim false
        (fun result => jointChainObservation hash enc K (guess, result))] {true} =
    𝒟[do
      let starts ← GXMSS.sampleStarts H h v
      let answer := hash.chain pp (guessedEpoch guess) (guessedChain guess) 0 1
        (starts (guessedEpoch guess) (guessedChain guess))
      let out ← runFilteredSpliced hash enc K adv pp guess zero answer starts
      return out.elim false
        (fun result => jointChainObservation hash enc K (guess, result))] {true} := by
    apply congrArg (fun mx : ProbComp Bool => 𝒟[mx] {true})
    apply bind_congr
    intro starts
    dsimp only
    rw [← runFilteredSpliced_honest_from_zero hash enc K adv pp guess starts hn]
  rw [hcut]
  simpa only [zero, guessedEpoch, guessedChain] using
    filteredZero_real_source_mass hash enc K adv pp guess zero rfl hn rfl rfl

/-- The exact source selected mass is the returned true mass of the real zero-cut hybrid. -/
private theorem jointChainAdvantage_eq_zeroReal
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SchemeAdversary PP H M R h v) :
    jointChainAdvantage hash enc K hv hw adv =
      𝒟[jointZeroRealProgram hash enc K adv] {true} := by
  unfold jointChainAdvantage jointChainOutputMeasure
  rw [ProbCompRuntime.probComp_evalDist,
    ← jointHonestSpliceProgram_eq_source hash enc K hv hw adv]
  exact (jointHonestSplice_mass_eq_filtered hash enc K adv).trans
    (jointFilteredHonest_mass_eq_zeroReal hash enc K adv)

/-- A cancellation-free finite telescope suitable for subprobability event masses. -/
private theorem finite_chain_hybrid_telescope (f : ℕ → ℝ≥0∞) (n : ℕ) :
    f 0 + ∑ j ∈ Finset.range n, f (j + 1) =
      f n + ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ]
    rw [← add_assoc, ih]
    ac_rfl

/-- A finite additive telescope yields the desired loss from one Boolean UD distance. -/
private theorem finite_hybrid_boolDist_bound
    (source terminal real ideal distance : ℝ≥0∞) (n : ℕ)
    (hfinite : (n : ℝ≥0∞) * ideal ≠ ∞)
    (htelescope : source + (n : ℝ≥0∞) * ideal =
      terminal + (n : ℝ≥0∞) * real)
    (hdistance : real ≤ ideal + distance) :
    source ≤ terminal + (n : ℝ≥0∞) * distance := by
  apply ENNReal.le_of_add_le_add_right hfinite
  calc
    source + (n : ℝ≥0∞) * ideal =
        terminal + (n : ℝ≥0∞) * real := htelescope
    _ ≤ terminal + (n : ℝ≥0∞) * (ideal + distance) := by
      gcongr
    _ = (terminal + (n : ℝ≥0∞) * distance) +
        (n : ℝ≥0∞) * ideal := by
      rw [mul_add]
      ac_rfl

/-- A uniform finite hybrid index averages unconditioned returned true masses. -/
private theorem uniform_fin_bind_true_mass (n : ℕ) [NeZero n]
    (f : Fin n → ProbComp Bool) :
    𝒟[($ᵗ (Fin n) : ProbComp (Fin n)) >>= f] {true} =
      (n : ℝ≥0∞)⁻¹ * ∑ j : Fin n, 𝒟[f j] {true} := by
  rw [evalDist_bind_of_discrete, SampleableType.evalDist_uniformSample,
    ProbabilityTheory.uniformOn_univ_bind_apply (fun j => 𝒟[f j]) {true}
      (measurableSet_singleton true)]
  simp only [Fintype.card_fin, Finset.mul_sum]

/-- Zeroing all hybrid indices beyond a selected cut leaves its finite prefix sum. -/
private theorem fin_sum_lt_eq_range (n g : ℕ) (hg : g ≤ n)
    (f : ℕ → ℝ≥0∞) :
    (∑ j : Fin n, if j.val < g then f j.val else 0) =
      ∑ j ∈ Finset.range g, f j := by
  change (∑ j : Fin n, (fun k : ℕ => if k < g then f k else 0) j.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => if k < g then f k else 0) n]
  have hsum := Finset.sum_range_add_sum_Ico
    (fun j : ℕ => if j < g then f j else 0) hg
  rw [← hsum]
  have hprefix : (∑ j ∈ Finset.range g, if j < g then f j else 0) =
      ∑ j ∈ Finset.range g, f j := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [Finset.mem_range.mp hj]
  have htail : (∑ j ∈ Finset.Ico g n, if j < g then f j else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp [not_lt.mpr (Finset.mem_Ico.mp hj).1]
  rw [hprefix, htail, add_zero]

/-- Pointwise selected-cut masses average to the exact finite-prefix sum. -/
private theorem uniform_fin_prefix_true_mass_of_pointwise
    (n g : ℕ) [NeZero n] (hg : g ≤ n)
    (actual : Fin n → ProbComp Bool) (f : ℕ → ℝ≥0∞)
    (hpoint : ∀ j : Fin n,
      𝒟[actual j] {true} = if j.val < g then f j.val else 0) :
    𝒟[do let j ← ($ᵗ (Fin n) : ProbComp (Fin n)); actual j] {true} =
      (n : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range g, f j := by
  rw [uniform_fin_bind_true_mass]
  simp_rw [hpoint]
  exact congrArg ((n : ℝ≥0∞)⁻¹ * ·) (fin_sum_lt_eq_range n g hg f)

private theorem finite_chain_hybrid_mean_telescope (real ideal : ℕ → ℝ≥0∞)
    (n g : ℕ) [NeZero n]
    (htelescope : real 0 + ∑ j ∈ Finset.range g, ideal j =
      real g + ∑ j ∈ Finset.range g, real j) :
    real 0 + (n : ℝ≥0∞) * ((n : ℝ≥0∞)⁻¹ *
      ∑ j ∈ Finset.range g, ideal j) =
    real g + (n : ℝ≥0∞) * ((n : ℝ≥0∞)⁻¹ *
      ∑ j ∈ Finset.range g, real j) := by
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (NeZero.ne n)
  have hntop : (n : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top n
  simpa only [← mul_assoc, ENNReal.mul_inv_cancel hn0 hntop, one_mul] using htelescope

/-- For one seed and one selector, the filtered ideal cut advances to the next real cut.
The resulting finite telescope concerns returned true mass only. -/
private theorem fixed_selector_filtered_hybrid_telescope
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) (pp : PP) (selector : Guess h w v) :
    let ep := guessedEpoch selector
    let i := guessedChain selector
    let g := (guessedPosition selector).val
    let cut : ℕ → Guess h w v := fun j => (ep, i, Fin.ofNat (2 ^ w - 1) j)
    let event : Option (Result PP H M R h v) → Bool := fun out => out.elim false
      (fun result => jointChainObservation hash enc K (selector, result))
    let real : ℕ → ℝ≥0∞ := fun j => 𝒟[do
      let starts ← GXMSS.sampleStarts H h v
      let x ← ($ᵗ H : ProbComp H)
      let out ← runFilteredSpliced hash enc K adv pp selector (cut j)
        (hash.chain pp ep i j 1 x) starts
      return event out] {true}
    let ideal : ℕ → ℝ≥0∞ := fun j => 𝒟[do
      let starts ← GXMSS.sampleStarts H h v
      let x ← ($ᵗ H : ProbComp H)
      let out ← runFilteredSpliced hash enc K adv pp selector (cut j) x starts
      return event out] {true}
    real 0 + ∑ j ∈ Finset.range g, ideal j =
      real g + ∑ j ∈ Finset.range g, real j := by
  let ep := guessedEpoch selector
  let i := guessedChain selector
  let g := (guessedPosition selector).val
  let cut : ℕ → Guess h w v := fun j => (ep, i, Fin.ofNat (2 ^ w - 1) j)
  let event : Option (Result PP H M R h v) → Bool := fun out => out.elim false
    (fun result => jointChainObservation hash enc K (selector, result))
  let real : ℕ → ℝ≥0∞ := fun j => 𝒟[do
    let starts ← GXMSS.sampleStarts H h v
    let x ← ($ᵗ H : ProbComp H)
    let out ← runFilteredSpliced hash enc K adv pp selector (cut j)
      (hash.chain pp ep i j 1 x) starts
    return event out] {true}
  let ideal : ℕ → ℝ≥0∞ := fun j => 𝒟[do
    let starts ← GXMSS.sampleStarts H h v
    let x ← ($ᵗ H : ProbComp H)
    let out ← runFilteredSpliced hash enc K adv pp selector (cut j) x starts
    return event out] {true}
  change real 0 + ∑ j ∈ Finset.range g, ideal j =
    real g + ∑ j ∈ Finset.range g, real j
  have hnext (j : ℕ) (hj : j < g) : ideal j = real (j + 1) := by
    have hjlt : j < 2 ^ w - 1 := by
      have := (guessedPosition selector).isLt
      omega
    have hj1lt : j + 1 < 2 ^ w - 1 := by
      have := (guessedPosition selector).isLt
      omega
    have hcutj : (guessedPosition (cut j)).val = j := by
      simp [cut, guessedPosition, Nat.mod_eq_of_lt hjlt]
    have hcutj1 : (guessedPosition (cut (j + 1))).val = j + 1 := by
      simp [cut, guessedPosition, Nat.mod_eq_of_lt hj1lt]
    have hstep (starts : Epoch h → Fin v → H) (x : H) :
        runFilteredSpliced hash enc K adv pp selector (cut j) x starts =
        runFilteredSpliced hash enc K adv pp selector (cut (j + 1))
          (hash.chain pp ep i (j + 1) 1 x) starts := by
      have h := runFilteredSpliced_advance hash enc K adv pp selector
        (cut j) (cut (j + 1)) x starts
        (by rfl) (by rfl) (by omega) (by rfl) (by rfl)
        (by apply Fin.le_iff_val_le_val.mpr; simpa only [hcutj1, g] using Nat.succ_le_iff.mpr hj)
      simpa only [cut, guessedEpoch, guessedChain, hcutj] using h
    apply congrArg (fun mx : ProbComp Bool => 𝒟[mx] {true})
    apply bind_congr
    intro starts
    apply bind_congr
    intro x
    simp only [event]
    rw [hstep starts x]
  have hsum : (∑ j ∈ Finset.range g, ideal j) =
      ∑ j ∈ Finset.range g, real (j + 1) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact hnext j (Finset.mem_range.mp hj)
  rw [hsum]
  exact finite_chain_hybrid_telescope real g

/-- A returned spliced execution retains the supplied seed and all spliced endpoints. -/
private theorem runSpliced_support_keys [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) (pp : PP) (guess : Guess h w v)
    (answer : H) (starts : Epoch h → Fin v → H)
    (out : Result PP H M R h v)
    (hout : out ∈ support (runSpliced hash enc K adv pp guess answer starts)) :
    out.pk.seed = pp ∧ out.sk.endpoints =
      splicedEndpoints hash pp guess answer starts := by
  simp only [runSpliced, mem_support_bind_iff] at hout
  obtain ⟨pair, _, hret⟩ := hout
  simp only [support_pure, Set.mem_singleton_iff] at hret
  subst out
  exact ⟨rfl, rfl⟩

/-- A successful record in a returned spliced run is exactly the signature made from its
successful retry codeword. -/
private theorem runSpliced_successful_record_signature
    [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) (pp : PP) (guess : Guess h w v)
    (answer : H) (starts : Epoch h → Fin v → H)
    (out : Result PP H M R h v)
    (hout : out ∈ support (runSpliced hash enc K adv pp guess answer starts))
    (ep : Epoch h) (msg : M) (sig : GXMSS.Signature R H h v)
    (hrecord : out.history ep = some (msg, some sig)) :
    ∃ wr, sig = splicedSignatureOfWord hash pp guess answer starts
        (splicedEndpoints hash pp guess answer starts) ep wr ∧
      enc.value pp msg wr.2 ep = some wr.1 := by
  let endpoints := splicedEndpoints hash pp guess answer starts
  let impl : QueryImpl
      (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
        (GXMSS.Signature R H h v))
      (StateT (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v)) ProbComp) :=
    (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (StateT (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v)) ProbComp) +
      splicedSigningOracle hash enc K pp guess answer starts endpoints
  have hpres : QueryImpl.PreservesInv impl
      (splicedSuccessfulHistoryEncodes hash enc pp guess answer starts endpoints) := by
    intro q history hinv z hz
    cases q with
    | inl uniform =>
      simp only [impl, QueryImpl.add_apply_inl] at hz
      simp only [QueryImpl.liftTarget_apply] at hz
      change z ∈ support
        ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) uniform) >>= fun a =>
          pure (a, history)) at hz
      simp only [mem_support_bind_iff] at hz
      obtain ⟨a, _, hret⟩ := hz
      simp only [support_pure, Set.mem_singleton_iff] at hret
      subst z
      exact hinv
    | inr signing =>
      simpa only [impl, QueryImpl.add_apply_inr] using
        (splicedSigningOracle_preserves_successfulHistoryEncodes hash enc K pp guess
          answer starts endpoints signing history hinv z hz)
  have hinit : splicedSuccessfulHistoryEncodes hash enc pp guess answer starts
      endpoints SyncSignatureUnforgeability.emptyHistory := by
    intro ep msg sig hentry
    simp [SyncSignatureUnforgeability.emptyHistory] at hentry
  simp only [runSpliced, mem_support_bind_iff] at hout
  obtain ⟨pair, hpair, hret⟩ := hout
  simp only [support_pure, Set.mem_singleton_iff] at hret
  subst out
  have hfinal := OracleComp.simulateQ_run_preservesInv impl
    (splicedSuccessfulHistoryEncodes hash enc pp guess answer starts endpoints)
      hpres (adv.forge ⟨hash.merkleRoot pp endpoints, pp⟩)
      SyncSignatureUnforgeability.emptyHistory hinit pair
  exact hfinal (by simpa only [impl, endpoints] using hpair) ep msg sig hrecord

/-- A non-maximum forged digit yields a preimage of a spliced final response whenever Game 1
equates the forged chain endpoint with that response. This is the deterministic PRE witness;
the distributional relation to the PRE experiment is separate. -/
private theorem spliced_final_nonSuccess_preimage_sound
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (pp : PP) (guess : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H) (out : Result PP H M R h v)
    (word : Codeword v (2 ^ w)) (i : Fin v)
    (hseed : out.pk.seed = pp)
    (hendpoints : out.sk.endpoints = splicedEndpoints hash pp guess answer starts)
    (hword : enc.value out.pk.seed out.forgery.2.1
      out.forgery.2.2.randomizer out.forgery.1 = some word)
    (hone : gameOneObservation hash enc K out = true)
    (hi : findNonMaximumCoordinate word = some i)
    (hepoch : guessedEpoch guess = out.forgery.1)
    (hchain : guessedChain guess = i)
    (hfinal : (guessedPosition guess).val + 1 = 2 ^ w - 1) :
    (HashInstance.thf hash).eval pp (hash.chainTweak
      (guessedEpoch guess, guessedChain guess, guessedPosition guess))
      (hash.digestInput (hash.chain pp out.forgery.1 i (word i)
        (2 ^ w - 2 - (word i).val) (out.forgery.2.2.ots i))) = answer := by
  have hsmall := findNonMaximumCoordinate_sound word hi
  have hendpoint := gameOneObservation_endpoint_eq_forged hash enc K out word hword hone i
  rw [hseed] at hendpoint
  have hselected : out.sk.endpoints out.forgery.1 i = answer := by
    rw [hendpoints, ← hepoch, ← hchain]
    exact splicedEndpoints_guess_final hash pp guess answer starts hfinal
  rw [hselected] at hendpoint
  have hlen : (word i).val + (2 ^ w - 2 - (word i).val) + 1 ≤ 2 ^ w - 1 := by
    omega
  have hstep := hash.chain_succ pp out.forgery.1 i (word i)
    (2 ^ w - 2 - (word i).val) (out.forgery.2.2.ots i) hlen
  have hcount : 2 ^ w - 2 - (word i).val + 1 =
      2 ^ w - 1 - (word i).val := by omega
  rw [hcount] at hstep
  have hposition : (⟨(word i).val + (2 ^ w - 2 - (word i).val), by omega⟩ :
      Fin (2 ^ w - 1)) = guessedPosition guess := by
    apply Fin.ext
    change (word i).val + (2 ^ w - 2 - (word i).val) = (guessedPosition guess).val
    omega
  rw [hposition] at hstep
  have heval := hstep.symm.trans hendpoint.symm
  simpa only [hepoch, hchain] using heval

/-- In a returned spliced execution, the enlarged selector's unused or failed-consumed branch
produces the concrete final-step PRE witness from the forged OTS suffix. -/
private theorem joint_nonSuccess_selected_preimage_sound
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) (pp : PP) (guess : Guess h w v)
    (answer : H) (starts : Epoch h → Fin v → H)
    (out : Result PP H M R h v)
    (hout : out ∈ support (runSpliced hash enc K adv pp guess answer starts))
    (hsource : forgedEpochSource out = .unused ∨
      ∃ msg, forgedEpochSource out = .failedConsumed msg)
    (hwin : jointChainObservation hash enc K (guess, out) = true) :
    ∃ word : Codeword v (2 ^ w), ∃ i : Fin v,
      enc.value pp out.forgery.2.1 out.forgery.2.2.randomizer out.forgery.1 =
        some word ∧
      findNonMaximumCoordinate word = some i ∧
      (HashInstance.thf hash).eval pp (hash.chainTweak
        (guessedEpoch guess, guessedChain guess, guessedPosition guess))
        (hash.digestInput (hash.chain pp out.forgery.1 i (word i)
          (2 ^ w - 2 - (word i).val) (out.forgery.2.2.ots i))) = answer := by
  obtain ⟨hseed, hendpoints⟩ := runSpliced_support_keys hash enc K adv pp guess
    answer starts out hout
  have hfilter := hwin
  rcases hsource with hs | ⟨msg, hs⟩
  · simp only [jointChainObservation, hs, Bool.and_eq_true] at hfilter
    have hfour := hfilter.1
    have hselected := hfilter.2
    rw [hseed] at hselected
    cases hword : enc.value pp out.forgery.2.1 out.forgery.2.2.randomizer
        out.forgery.1 with
    | none => simp [hword] at hselected
    | some word =>
      cases hi : findNonMaximumCoordinate word with
      | none => simp [hword, hi] at hselected
      | some i =>
        simp only [hword, hi] at hselected
        have hguess : guessedEpoch guess = out.forgery.1 ∧
            guessedChain guess = i ∧
            (guessedPosition guess).val + 1 = 2 ^ w - 1 := by
          exact of_decide_eq_true hselected
        have hone : gameOneObservation hash enc K out = true := by
          have hfour' := hfour
          simp only [gameFourObservation, Bool.and_eq_true] at hfour'
          have hthree := hfour'.1
          simp only [gameThreeObservation, Bool.and_eq_true] at hthree
          have htwo := hthree.1
          simp only [gameTwoObservation, Bool.and_eq_true] at htwo
          exact htwo.1
        refine ⟨word, i, rfl, hi, ?_⟩
        exact spliced_final_nonSuccess_preimage_sound hash enc K pp guess answer
          starts out word i hseed hendpoints (by rw [hseed]; exact hword)
          hone hi hguess.1 hguess.2.1 hguess.2.2
  · simp only [jointChainObservation, hs, Bool.and_eq_true] at hfilter
    have hfour := hfilter.1
    have hselected := hfilter.2
    rw [hseed] at hselected
    cases hword : enc.value pp out.forgery.2.1 out.forgery.2.2.randomizer
        out.forgery.1 with
    | none => simp [hword] at hselected
    | some word =>
      cases hi : findNonMaximumCoordinate word with
      | none => simp [hword, hi] at hselected
      | some i =>
        simp only [hword, hi] at hselected
        have hguess : guessedEpoch guess = out.forgery.1 ∧
            guessedChain guess = i ∧
            (guessedPosition guess).val + 1 = 2 ^ w - 1 := by
          exact of_decide_eq_true hselected
        have hone : gameOneObservation hash enc K out = true := by
          have hfour' := hfour
          simp only [gameFourObservation, Bool.and_eq_true] at hfour'
          have hthree := hfour'.1
          simp only [gameThreeObservation, Bool.and_eq_true] at hthree
          have htwo := hthree.1
          simp only [gameTwoObservation, Bool.and_eq_true] at htwo
          exact htwo.1
        refine ⟨word, i, rfl, hi, ?_⟩
        exact spliced_final_nonSuccess_preimage_sound hash enc K pp guess answer
          starts out word i hseed hendpoints (by rw [hseed]; exact hword)
          hone hi hguess.1 hguess.2.1 hguess.2.2

/-- The successful selected branch uses the existing designated cut. Its extracted predecessor
hashes to the PRE challenge response supplied at the guessed tweak. -/
private theorem joint_successful_selected_preimage_sound
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) (pp : PP) (guess : Guess h w v)
    (answer : H) (starts : Epoch h → Fin v → H)
    (out : Result PP H M R h v)
    (hout : out ∈ support (runSpliced hash enc K adv pp guess answer starts))
    (msg : M) (sig : GXMSS.Signature R H h v)
    (hsource : forgedEpochSource out = .successful msg sig)
    (hwin : jointChainObservation hash enc K (guess, out) = true) :
    ∃ honestWord forgedWord : Codeword v (2 ^ w), ∃ i : Fin v,
      enc.value pp msg sig.randomizer out.forgery.1 = some honestWord ∧
      enc.value pp out.forgery.2.1 out.forgery.2.2.randomizer out.forgery.1 =
        some forgedWord ∧
      findSmallerCoordinate honestWord forgedWord = some i ∧
      ∃ preimage : H,
        hash.findChainCut pp out.forgery.1 i (forgedWord i) (honestWord i)
          (2 ^ w - 1) (sig.ots i) (out.forgery.2.2.ots i) = some (.inl preimage) ∧
        (HashInstance.thf hash).eval pp (hash.chainTweak
          (guessedEpoch guess, guessedChain guess, guessedPosition guess))
          (hash.digestInput preimage) = answer := by
  obtain ⟨hseed, _⟩ := runSpliced_support_keys hash enc K adv pp guess answer
    starts out hout
  obtain ⟨honestWord, forgedWord, i, hfour, hhonest, hforged, hi,
      hepoch, hchain, hposition⟩ :=
    jointChainObservation_successful_cut hash enc K guess out msg sig hsource hwin
  have hrecord := history_of_successful_source out msg sig hsource
  obtain ⟨wr, hsig, hwr⟩ := runSpliced_successful_record_signature hash enc K
    adv pp guess answer starts out hout out.forgery.1 msg sig hrecord
  have hhonest' : enc.value pp msg wr.2 out.forgery.1 = some honestWord := by
    rw [hseed] at hhonest
    simpa [hsig, splicedSignatureOfWord] using hhonest
  have hwordEq : wr.1 = honestWord := Option.some.inj (hwr.symm.trans hhonest')
  have hsigAnswer : sig.ots i = answer := by
    rw [hsig, ← hchain]
    apply splicedSignatureOfWord_guess_succ hash pp guess answer starts
      (splicedEndpoints hash pp guess answer starts) out.forgery.1 wr hepoch.symm
    rw [hwordEq, hchain]
    exact hposition.symm
  have hfour' := hfour
  simp only [gameFourObservation, Bool.and_eq_true] at hfour'
  have hcut := hfour'.2
  simp only [designatedCutHolds, hsource, hhonest, hforged, hi] at hcut
  have hcutEq := of_decide_eq_true hcut
  rw [hseed, hsigAnswer] at hcutEq
  let preimage : H := hash.chain pp out.forgery.1 i (forgedWord i)
    ((honestWord i).val - (forgedWord i).val - 1) (out.forgery.2.2.ots i)
  have hfind : hash.findChainCut pp out.forgery.1 i (forgedWord i)
      (honestWord i) (2 ^ w - 1) (sig.ots i) (out.forgery.2.2.ots i) =
        some (.inl preimage) := by
    simp [HashInstance.findChainCut, preimage, hcutEq, hsigAnswer]
  have hsmaller := findSmallerCoordinate_sound honestWord forgedWord hi
  have hlen : (forgedWord i).val +
      ((honestWord i).val - (forgedWord i).val - 1) + 1 ≤ 2 ^ w - 1 := by
    have := (honestWord i).isLt
    omega
  have hstep := hash.chain_succ pp out.forgery.1 i (forgedWord i)
    ((honestWord i).val - (forgedWord i).val - 1) (out.forgery.2.2.ots i) hlen
  have hcount : (honestWord i).val - (forgedWord i).val - 1 + 1 =
      (honestWord i).val - (forgedWord i).val := by omega
  rw [hcount] at hstep
  have hpos : (⟨(forgedWord i).val +
      ((honestWord i).val - (forgedWord i).val - 1), by omega⟩ :
      Fin (2 ^ w - 1)) = guessedPosition guess := by
    apply Fin.ext
    change (forgedWord i).val +
      ((honestWord i).val - (forgedWord i).val - 1) = (guessedPosition guess).val
    omega
  rw [hpos] at hstep
  have heval : (HashInstance.thf hash).eval pp (hash.chainTweak
      (guessedEpoch guess, guessedChain guess, guessedPosition guess))
      (hash.digestInput preimage) = answer := by
    have := hstep.symm.trans hcutEq
    simpa only [preimage, hepoch, hchain] using this
  refine ⟨honestWord, forgedWord, i, ?_, ?_, hi, preimage, hfind, heval⟩
  · rw [hseed] at hhonest
    exact hhonest
  · rw [hseed] at hforged
    exact hforged

private noncomputable def udPick [NeZero v] [NeZero (2 ^ w - 1)] [SampleableType H]
    (hash : HashInstance PP T X H h w v) :
    OracleComp (unifSpec + (SM_DT_UD_challengeSpec T H +
      collectionSpec (chainUDProblem hash).thColl)) (UDTargetState H h w v) := do
  let guess ← OracleComp.liftComp ($ᵗ (Guess h w v)) _
  let hybrid ← OracleComp.liftComp ($ᵗ (Fin (2 ^ w - 1))) _
  let starts ← OracleComp.liftComp (GXMSS.sampleStarts H h v) _
  let answer ← liftM ((unifSpec + (SM_DT_UD_challengeSpec T H +
    collectionSpec (chainUDProblem hash).thColl)).query (.inr (.inl
      (hash.chainTweak (guessedEpoch guess, guessedChain guess, hybrid)))))
  return ⟨guess, hybrid, answer, starts⟩

/-- Executable one-target undetectability reduction driven by the fixed source adversary. -/
noncomputable def undetectabilityReduction [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (advGXMSS : SchemeAdversary PP H M R h v) :
    SM_DT_UD_Adversary (chainUDProblem hash) := by
  letI : NeZero v := ⟨Nat.ne_of_gt hv⟩
  letI : NeZero (2 ^ w - 1) := ⟨by have := Nat.one_lt_two_pow (by omega : w ≠ 0); omega⟩
  exact {
  State := UDTargetState H h w v
  pick := udPick hash
  distinguish state pp := do
    match state.answer with
    | none => return false
    | some answer =>
      let spliceGuess : Guess h w v :=
        (guessedEpoch state.guess, guessedChain state.guess, state.hybrid)
      let out ← runSpliced hash enc K advGXMSS pp spliceGuess answer state.starts
      return gameFiveObservation hash enc K (state.guess, out) }

/-- One undetectability adversary observes the enlarged selected event across successful,
unused, and failed-consumed forged epochs. It issues one challenge before seed reveal. -/
noncomputable def jointUndetectabilityReduction [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (advGXMSS : SchemeAdversary PP H M R h v) :
    SM_DT_UD_Adversary (chainUDProblem hash) := by
  letI : NeZero v := ⟨Nat.ne_of_gt hv⟩
  letI : NeZero (2 ^ w - 1) := ⟨by have := Nat.one_lt_two_pow (by omega : w ≠ 0); omega⟩
  exact {
  State := UDTargetState H h w v
  pick := udPick hash
  distinguish state pp := do
    if state.hybrid.val < (guessedPosition state.guess).val then
      match state.answer with
      | none => return false
      | some answer =>
        let spliceGuess : Guess h w v :=
          (guessedEpoch state.guess, guessedChain state.guess, state.hybrid)
        let out ← runSpliced hash enc K advGXMSS pp spliceGuess answer state.starts
        return jointChainObservation hash enc K (state.guess, out)
    else return false }

end GXMSS.ReductionGames
