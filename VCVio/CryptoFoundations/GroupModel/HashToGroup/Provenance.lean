/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.HashToGroup.Coins
public import VCVio.CryptoFoundations.HardnessAssumptions.DiscreteLogRelation.Algebra

/-! # Receipt provenance and normalized representations

Receipts retain their chronological positions. Their symbolic origins distinguish fixed-input
slots from hash labels, independently of group values and programmed coefficient rows.
-/

public section

namespace GroupModel.HashToGroup

open OracleComp OracleSpec Interaction

variable {Label F G κ C ι : Type} {n : ℕ}

/-- A symbolic input is either a fixed-input slot or a hash label. -/
abbrev Origin (n : ℕ) (Label : Type) := Fin n ⊕ Label

/-- A programmed receipt carries its symbolic origin as well as its private coefficient row. -/
abbrev Receipt (n : ℕ) (Label C : Type) := Origin n Label × C

/-- Attach the queried label to a fresh programmed sample. Caching retains this origin. -/
@[expose] def provenanceSample (n : ℕ) (sample : Label → ProbComp C)
    (l : Label) : ProbComp (Receipt n Label C) :=
  (fun c => (Sum.inr l, c)) <$> sample l

/-- Initial receipts have separate fixed-input origins in their original order. -/
@[expose] def provenanceInitial (fixed : Fin n → C) : State Label (Receipt n Label C) :=
  initial (List.ofFn fun i => (Sum.inl i, fixed i))

/-- A programmable hash oracle that retains origins and supports private coins. -/
@[expose] def provenanceGame [DecidableEq Label] (n : ℕ) (decode : C → G)
    (sample : Label → ProbComp C) :
    QueryImpl (plainSpec (fun _ : Unit => G) (CoinQuery Label) (CoinReply (fun _ => Unit)))
      (StateT (State Label (Receipt n Label C)) ProbComp) :=
  gameWithCoins (decode ∘ Prod.snd) (provenanceSample n sample)

/-- Forgetting origins preserves the entire cached execution, including private coins. -/
theorem simulateQ_provenanceGame [DecidableEq Label] (decode : C → G)
    (sample : Label → ProbComp C)
    (p : OracleComp (plainSpec (fun _ : Unit => G) (CoinQuery Label)
      (CoinReply (fun _ => Unit))) ι) (st : State Label (Receipt n Label C)) :
    Prod.map id (mapState Prod.snd) <$> (simulateQ (provenanceGame n decode sample) p).run st =ᵈ
      (simulateQ (gameWithCoins decode sample) p).run (mapState Prod.snd st) := by
  apply simulateQ_gameWithCoins_mapState
  intro l
  simp [provenanceSample]

/-- Perfect simulation may retain the entire provenance log: only the sampled row values
are interpreted, while every fixed-input slot and hash label remains unchanged. -/
theorem simulateQ_provenanceGame_mapState [DecidableEq Label] {D : Type}
    (f : C → D) (decode : D → G) (sample : Label → ProbComp C)
    (target : Label → ProbComp D) (h : ∀ l, f <$> sample l =ᵈ target l)
    (p : OracleComp (plainSpec (fun _ : Unit => G) (CoinQuery Label)
      (CoinReply (fun _ => Unit))) ι) (st : State Label (Receipt n Label C)) :
    Prod.map id (mapState (Prod.map id f)) <$>
        (simulateQ (provenanceGame n (decode ∘ f) sample) p).run st =ᵈ
      (simulateQ (provenanceGame n decode target) p).run (mapState (Prod.map id f) st) := by
  apply simulateQ_gameWithCoins_mapState (Prod.map id f) (decode ∘ Prod.snd)
  intro l
  simpa [provenanceSample, Function.comp_def] using
    (h l).map (fun c => (Sum.inr l, c) : D → Receipt n Label D)

/-- Extract coefficient representations from a randomized run whose receipts also retain origins.
The initial rows may encode fixed inputs; this evaluation identity imposes no distributional
claim. -/
theorem runGameWithCoins_provenance_transport [DecidableEq Label] [CommSemiring F]
    [AddCommMonoid G] [Module F G] [Fintype κ]
    (B : κ → G) (sample : Label → ProbComp (κ → F))
    (p : OracleComp (explainedSpec F (fun _ : Unit => G) (CoinQuery Label)
      (CoinReply (fun _ => Unit))) (Explained F Unit (fun _ : Unit => G)))
    (st : State Label (Receipt n Label (κ → F)))
    (hp : IsAlgebraic (fun _ => st.2.map (basisMap B ∘ Prod.snd)) p)
    (z) (hz : z ∈ support (runGameWithCoins (basisMap B ∘ Prod.snd)
      (provenanceSample n sample) p st)) :
    (transportExplained (fun _ => z.2.2.map Prod.snd) z.1 ()).map (basisMap B) =
      z.1.value.groups () := by
  apply transportExplained_evaluate (fun _ => B) (fun _ => z.2.2.map Prod.snd)
  simpa only [List.map_map] using
    runGameWithCoins_valid (basisMap B ∘ Prod.snd) (provenanceSample n sample) p st hp z hz

/-- The set of fresh labels appearing in a receipt log, excluding fixed-input slots. -/
@[expose] def freshLabels [DecidableEq Label] (origins : List (Origin n Label)) : Finset Label :=
  (origins.filterMap (Sum.elim (fun _ => none) some)).toFinset

/-- For a finite label space, the challenge table provides enough slots for all fresh labels.
This bound concerns distinct origins, independently of repeated receipt positions. -/
theorem freshLabels_card_le [Fintype Label] [DecidableEq Label]
    (origins : List (Origin n Label)) : (freshLabels origins).card ≤ Fintype.card Label :=
  Finset.card_le_univ _

/-- Merge chronological coefficients by symbolic origin, keeping distinct labels separate. -/
@[expose] def merge [Semiring F] [DecidableEq ι] (origins : List ι) (c : List F) : ι → F :=
  transport (origins.map fun i => Pi.single i 1) c

/-- The coordinate row of a symbolic origin evaluates to that origin's group element. -/
@[simp] theorem basisMap_single [CommSemiring F] [AddCommMonoid G] [Module F G]
    [Fintype ι] [DecidableEq ι] (B : ι → G) (i : ι) :
    basisMap (F := F) B (Pi.single i 1) = B i := by
  simp [basisMap, Pi.single_apply, ite_smul]

/-- Merging by origin preserves evaluation over the corresponding symbolic basis. -/
theorem basisMap_merge [CommSemiring F] [AddCommMonoid G] [Module F G]
    [Fintype ι] [DecidableEq ι] (B : ι → G) (origins : List ι) (c : List F) :
    basisMap B (merge origins c) = evaluate c (origins.map B) := by
  simp [merge, basisMap_transport, List.map_map, Function.comp_def]

/-- Equal group outputs win only when their representations differ after merging by origin. -/
@[expose] def NormalizedCollision [Semiring F] [DecidableEq ι] (origins : List ι)
    (out : Explained F Unit (fun _ : Unit => G)) : Prop :=
  ∃ (a b : List F) (g : G), out.coefficients () = [a, b] ∧
    out.value.groups () = [g, g] ∧ merge origins a ≠ merge origins b

/-- The merged difference of the first two output representations. -/
@[expose] def mergedDifference [Ring F] [DecidableEq ι] (origins : List ι)
    (out : Explained F Unit (fun _ : Unit => G)) : ι → F :=
  merge origins (((out.coefficients ())[0]?).getD []) -
    merge origins (((out.coefficients ())[1]?).getD [])

/-- A normalized collision yields a nonzero merged difference. -/
theorem mergedDifference_ne_zero [Ring F] [DecidableEq ι] (origins : List ι)
    (out : Explained F Unit (fun _ : Unit => G)) (h : NormalizedCollision origins out) :
    mergedDifference origins out ≠ 0 := by
  obtain ⟨a, b, g, ha, _, hne⟩ := h
  simpa [mergedDifference, ha, sub_eq_zero] using hne

/-- Valid colliding outputs give a relation over symbolic fixed-input and hash coordinates. -/
@[expose] def normalizedRelation [Fintype ι] [DecidableEq ι] [CommRing F] [AddCommGroup G]
    [Module F G] (B : ι → G) (origins : List ι)
    (out : Explained F Unit (fun _ : Unit => G))
    (hv : out.Valid (fun _ => origins.map B)) (hc : NormalizedCollision origins out) :
    DiscreteLogRelation.RelationWitness (F := F) B where
  coeffs := mergedDifference origins out
  nonzero := mergedDifference_ne_zero origins out hc
  relation := by
    obtain ⟨a, b, g, ha, hg, _⟩ := hc
    have h := hv ()
    simp only [ha, hg, List.forall₂_cons, List.forall₂_nil_right_iff, and_true] at h
    change basisMap B (mergedDifference origins out) = 0
    simp [mergedDifference, ha, map_sub, basisMap_merge, h.1.2, h.2.2]

/-- Duplicate receipts for one origin have identical singleton merged representations. -/
theorem merge_duplicate [Semiring F] [DecidableEq ι] (i : ι) :
    merge (F := F) [i, i] [1, 0] = merge [i, i] [0, 1] := by
  simp [merge, transport, evaluate, List.mapIdx_cons, List.mapIdx_nil]

/-- Distinct origins remain different even when their visible group values are equal. -/
theorem merge_pair_ne [Semiring F] [Nontrivial F] [DecidableEq ι] (i j : ι) (h : i ≠ j) :
    merge (F := F) [i, j] [1, 0] ≠ merge [i, j] [0, 1] := by
  intro heq
  have hi := congrFun heq i
  simp [merge, transport, evaluate, List.mapIdx_cons, List.mapIdx_nil, h] at hi

end GroupModel.HashToGroup
