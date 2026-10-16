/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.VectorCommitment
public import VCVio.OracleComp.Constructions.SampleableType.Basic

/-!
# Salted Merkle trees as vector commitments

The salted Merkle commitment `MT[σ, Σ, ℓ = 2^d, ν]` of Chiesa, Di, Hu and Zheng
(ePrint 2025/2166, Def 8.2, pp. 52–53) over one oracle `f : X → Y`:

* `Commit^f(m)` samples salts `γ_ι` and hashes bottom-up: the leaf labels are
  `z_{d,ι} = f(m_ι, γ_ι)` and the internal labels are `z_{j,ι} = f(z_{j+1,2ι}, z_{j+1,2ι+1})`
  (positions counted from `0`). The commitment is the root `rt = z_{0,0}` and the trapdoor is
  `td = (γ, C)`, with `C` the table of all labels.
* `Open(Q, td)` returns, for every `ι ∈ Q`, the salt `γ_ι` and, for each level `j ∈ [1, d]`, the
  node `a_{ι,j}` on the path from the root to the leaf `ι` and its sibling `b_{ι,j}`.
* `Check^f(rt, Q, ans, pf)` runs `OutputIO`, which lists the input-output pairs
  `(f(ans_ι, γ_ι) ↦ a_{ι,d})` and `(f(L_{ι,j}, R_{ι,j}) ↦ a_{ι,j-1})` with `a_{ι,0} = rt`, and
  then `CheckIO`.

Tree inputs sit in the single oracle domain `X` through an `SaltedMerkle.Encoding`: the paper uses
one function `f` with no domain separation (p. 52), and tagged domains are the special case
`X = (Y × Y) ⊕ (Msg × Salt)`.

The trapdoor stores the label table with the paper's level indexing, as level arrays
`(j : Fin (d + 1)) → Fin (2 ^ j) → Option Y`; `none` is `⊥`, so the same type holds the trapdoors
that the extractor of §8.3 produces (`VCVio.CryptoFoundations.MerkleTree.Salted.Extract`).

## Parsing and the query count

`OutputIO` returns `none`, so that `Check` rejects without a query, unless the proof has an entry
exactly at the positions of `Q = dom ans`: the paper's proof `pf = (ST_ι)_{ι ∈ Q}` is indexed by
`Q`. Identical pairs are listed once; repeating a check is idempotent, so this does not change the
acceptance predicate (`checkIOOn_dedup`).

The verifier hashes the leaf as well as the `d` internal nodes of a path. One opened position
therefore lists `d + 1` pairs before deduplication, so the check makes at most `d + 1` queries per
opened position (fewer when pairs repeat), and `checkIOForm` has `qVC q = q * (d + 1)`. The
openings of all positions read from one trapdoor contain at most
`2 ^ d + (2 ^ d - 1) = 2ℓ - 1` distinct pairs, with `ℓ = 2 ^ d` (`length_outputIO_opening_le`).
These counts differ from the `q_s · log ℓ` and `ℓ` stated in ePrint 2025/2166, §8.3
(p. 55), which do not count the leaf hash; for `ℓ = 1` the verifier still makes one query.

## Universes

The tree data, the opening, `OutputIO`, `checkOn` and the consistency lemmas take `X`, `Y`, `Msg`
and `Salt` in independent universes. `commitTree`, which samples no coins, takes `Y` and `Salt` in
one common universe. `scheme`, `checkIOForm` and completeness take `Y` and `Salt` in `Type`: `Y`
is the answer type of the oracle, which is combined with the uniform-sampling oracle `unifSpec`,
and the salts are sampled uniformly. `X` and `Msg` stay in arbitrary universes.

## Main definitions

* `SaltedMerkle.Encoding`, `SaltedMerkle.Labels`, `SaltedMerkle.Td`, `SaltedMerkle.PathProof`,
  `SaltedMerkle.Pf`.
* `SaltedMerkle.commitTree`, `SaltedMerkle.opening`, `SaltedMerkle.outputIO`.
* `SaltedMerkle.scheme enc d : DetVectorCommitment X Y Msg Y (Td Y Salt d) (Pf Y Salt d) (2 ^ d)`,
  a deterministic vector commitment; `(scheme enc d).toVectorCommitment` is the general form.
* `SaltedMerkle.checkIOForm enc d : (scheme enc d).toVectorCommitment.CheckIOForm`: the check is
  coin-free, `OutputIO` then `CheckIO`, with `qVC q = q * (d + 1)`.
* `SaltedMerkle.checkOn enc d D`: the check against a partial table `D : X → Option Y`; it is
  `(checkIOForm enc d).checkOn D` (`checkIOForm_checkOn`).
* `SaltedMerkle.Consistent G enc rt ans td`: every hash relation that the opening of `dom ans`
  from `td` lists holds for the relation `G`.

## Main results

* `SaltedMerkle.Consistent.outputIO_opening`: the opening of a consistent trapdoor parses, and
  every listed pair satisfies `G`.
* `SaltedMerkle.consistent_honestTree`, `SaltedMerkle.perfectlyComplete`: perfect completeness
  against every fixed oracle function; `SaltedMerkle.perfectlyComplete_toVectorCommitment`: perfect
  completeness relative to every oracle distribution (Def 3.7).
* `SaltedMerkle.length_outputIO_opening_le`: the openings read from one trapdoor list at most
  `2 · 2 ^ d - 1` distinct pairs.
-/

public section

open OracleComp OracleSpec

universe uX uY uM uS

namespace SaltedMerkle

/-! ## Data -/

/-- How the inputs of a salted Merkle tree sit in the single oracle domain `X`: an internal node
hashes a pair of labels and a leaf hashes a message with its salt. The paper uses one function `f`
with no domain separation, distinguishing node and leaf inputs only by their length (p. 52,
pp. 54–55); tagged domains are the special case `X = (Y × Y) ⊕ (Msg × Salt)`. -/
structure Encoding (X : Type uX) (Y : Type uY) (Msg : Type uM) (Salt : Type uS) where
  /-- The input of an internal node with children labels `(L, R)`. -/
  node : Y × Y → X
  /-- The input of a leaf with message `m` and salt `γ`. -/
  leaf : Msg × Salt → X
  /-- Distinct children give distinct node inputs. -/
  node_injective : Function.Injective node
  /-- Distinct messages or salts give distinct leaf inputs. -/
  leaf_injective : Function.Injective leaf

/-- A table of node labels: level `j ∈ {0, …, d}`, position `ι < 2 ^ j` (the list `C`, p. 52).
`none` is `⊥` (p. 55). -/
abbrev Labels (Y : Type uY) (d : ℕ) := (j : Fin (d + 1)) → Fin (2 ^ (j : ℕ)) → Option Y

/-- A trapdoor `td = (γ, C)` (p. 52): the salts and the label table. Both are `Option`-valued, so
an extracted trapdoor with `⊥` entries has the same type. -/
abbrev Td (Y : Type uY) (Salt : Type uS) (d : ℕ) := (Fin (2 ^ d) → Option Salt) × Labels Y d

/-- The all-`⊥` trapdoor. -/
@[expose]
def tdBot {Y : Type uY} {Salt : Type uS} {d : ℕ} : Td Y Salt d := (fun _ ↦ none, fun _ _ ↦ none)

/-- The opening `ST_ι` of one leaf (p. 52): its salt and, for `j ∈ [1, d]` (stored at `j - 1`),
the node `a_{ι,j}` on the path from the root to the leaf and its sibling `b_{ι,j}`. The leaf label
is `a_{ι,d}`. The root in `ST_ι` is the commitment and is not repeated. -/
structure PathProof (Y : Type uY) (Salt : Type uS) (d : ℕ) where
  /-- The salt `γ_ι`. -/
  salt : Salt
  /-- The pairs `(a_{ι,j+1}, b_{ι,j+1})` for `j < d`. -/
  path : Fin d → Y × Y
  deriving DecidableEq

/-- A proof `pf = (ST_ι)_{ι ∈ Q}`: the entry is `none` off `Q`. -/
abbrev Pf (Y : Type uY) (Salt : Type uS) (d : ℕ) := Fin (2 ^ d) → Option (PathProof Y Salt d)

section Generic

variable {X : Type uX} {Y : Type uY} {Msg : Type uM} {Salt : Type uS} {d : ℕ}

/-! ## Positions -/

/-- The label at level `j` and position `p` of a table, and `none` out of range. -/
@[expose]
def labelAt (C : Labels Y d) (j p : ℕ) : Option Y :=
  if h : j ≤ d ∧ p < 2 ^ j then C ⟨j, Nat.lt_succ_of_le h.1⟩ ⟨p, h.2⟩ else none

/-- In range, `labelAt` reads the table. -/
theorem labelAt_of_lt (C : Labels Y d) {j p : ℕ} (hj : j ≤ d) (hp : p < 2 ^ j) :
    labelAt C j p = C ⟨j, Nat.lt_succ_of_le hj⟩ ⟨p, hp⟩ := by
  simp [labelAt, hj, hp]

/-- `labelAt` of a table read off a function of the level and the position. -/
@[simp]
theorem labelAt_mk (T : ℕ → ℕ → Option Y) {j p : ℕ} (hj : j ≤ d) (hp : p < 2 ^ j) :
    labelAt (d := d) (fun j p ↦ T j p) j p = T j p := by
  simp [labelAt, hj, hp]

/-- The position at level `j` of the ancestor of the leaf `ι`. -/
@[expose]
def anc (d : ℕ) (ι : ℕ) (j : ℕ) : ℕ := ι / 2 ^ (d - j)

/-- The position of the sibling of position `p` within its level. -/
@[expose]
def sib (p : ℕ) : ℕ := if p % 2 = 0 then p + 1 else p - 1

/-- The ancestor of a leaf at the leaf level is the leaf. -/
theorem anc_self (ι : ℕ) : anc d ι d = ι := by
  simp [anc]

/-- The parent of the ancestor at level `j + 1` is the ancestor at level `j`. -/
theorem anc_succ_div_two {ι j : ℕ} (hj : j < d) : anc d ι (j + 1) / 2 = anc d ι j := by
  simp only [anc, Nat.div_div_eq_div_mul]
  congr 1
  rw [← pow_succ]
  congr 1
  omega

/-- The ancestor at level `j` is a position of level `j`. -/
theorem anc_lt {ι j : ℕ} (hι : ι < 2 ^ d) (hj : j ≤ d) : anc d ι j < 2 ^ j := by
  rw [anc, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add]
  convert hι using 2
  omega

/-- The ancestor at level `0` is the root position. -/
theorem anc_zero {ι : ℕ} (hι : ι < 2 ^ d) : anc d ι 0 = 0 := by
  have := anc_lt (j := 0) hι (Nat.zero_le d)
  simpa using this

/-- A position and its sibling have the same parent. -/
theorem sib_div_two (p : ℕ) : sib p / 2 = p / 2 := by
  unfold sib; split_ifs <;> omega

/-- The sibling of a position of level `j + 1` is a position of level `j + 1`. -/
theorem sib_lt {p j : ℕ} (hp : p < 2 ^ (j + 1)) : sib p < 2 ^ (j + 1) := by
  have h2 : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
  unfold sib; split_ifs <;> omega

/-- Order a path node `a` and its sibling `b` at position `p` as `(L, R)`: `a` is the left child
exactly when `p` is even (the paper's odd, 1-indexed positions). -/
@[expose]
def order (p : ℕ) (ab : Y × Y) : Y × Y := if p % 2 = 0 then ab else ab.swap

/-- The node `a_{ι,j}` on the path of an opening, with `a_{ι,0} = rt`. -/
@[expose]
def PathProof.node (rt : Y) (pp : PathProof Y Salt d) (j : ℕ) : Y :=
  if h : 0 < j ∧ j ≤ d then (pp.path ⟨j - 1, by omega⟩).1 else rt

/-! ## Honest hashing -/

section Hashing

variable {m : Type uY → Type*} [Monad m]

/-- Hash every entry of a vector of inputs, from the first to the last. -/
@[expose]
def hashAll (hash : X → m Y) : (n : ℕ) → (Fin n → X) → m (Fin n → Y)
  | 0, _ => pure Fin.elim0
  | n + 1, f => do
      let y ← hash (f 0)
      let ys ← hashAll hash n (Fin.tail f)
      pure (Fin.cons y ys)

/-- The inputs of level `j` of a tree from the labels of level `j + 1`. -/
@[expose]
def parentInputs (enc : Encoding X Y Msg Salt) {j : ℕ} (c : Fin (2 ^ (j + 1)) → Y) :
    Fin (2 ^ j) → X :=
  fun q ↦ enc.node (c ⟨2 * q, by rw [pow_succ]; omega⟩, c ⟨2 * q + 1, by rw [pow_succ]; omega⟩)

/-- Hash a tree bottom-up from the labels `c` of its level `j`. It returns the root and the table
of the labels at every level `i ≤ j`, as a function of the level and the position. -/
@[expose]
def buildUp (enc : Encoding X Y Msg Salt) (hash : X → m Y) :
    (j : ℕ) → (Fin (2 ^ j) → Y) → m (Y × (ℕ → ℕ → Option Y))
  | 0, c => pure (c ⟨0, Nat.two_pow_pos 0⟩,
      fun i q ↦ if i = 0 ∧ q = 0 then some (c ⟨0, Nat.two_pow_pos 0⟩) else none)
  | j + 1, c => do
      let c' ← hashAll hash (2 ^ j) (parentInputs enc c)
      let r ← buildUp enc hash j c'
      pure (r.1, fun i q ↦
        if i = j + 1 then (if h : q < 2 ^ (j + 1) then some (c ⟨q, h⟩) else none) else r.2 i q)

/-- Simulating `hashAll` simulates each hash. -/
theorem simulateQ_hashAll {ι : Type*} {spec : OracleSpec ι} {r : Type uY → Type*} [Monad r]
    [LawfulMonad r] (impl : QueryImpl spec r) (hash : X → OracleComp spec Y) (n : ℕ)
    (f : Fin n → X) :
    simulateQ impl (hashAll hash n f) = hashAll (fun x ↦ simulateQ impl (hash x)) n f := by
  induction n with
  | zero => rfl
  | succ n ih => simp [hashAll, ih]

/-- Simulating `buildUp` simulates each hash. -/
theorem simulateQ_buildUp {ι : Type*} {spec : OracleSpec ι} {r : Type uY → Type*} [Monad r]
    [LawfulMonad r] (impl : QueryImpl spec r) (enc : Encoding X Y Msg Salt)
    (hash : X → OracleComp spec Y) (j : ℕ) (c : Fin (2 ^ j) → Y) :
    simulateQ impl (buildUp enc hash j c) =
      buildUp enc (fun x ↦ simulateQ impl (hash x)) j c := by
  induction j with
  | zero => rfl
  | succ j ih => simp [buildUp, ih, simulateQ_hashAll]

variable [LawfulMonad m]

/-- `hashAll` with a deterministic hash applies it to every entry. -/
theorem hashAll_pure (H : X → Y) (n : ℕ) (f : Fin n → X) :
    hashAll (fun x ↦ (pure (H x) : m Y)) n f = pure fun i ↦ H (f i) := by
  induction n with
  | zero => simp only [hashAll]; congr 1; funext i; exact i.elim0
  | succ n ih =>
      simp only [hashAll, ih, pure_bind]
      congr 1
      funext i
      refine Fin.cases rfl (fun i ↦ ?_) i
      simp [Fin.tail]

end Hashing

/-- The root and the label table of the tree with level-`j` labels `c`, hashed with the function
`H`: the value of `buildUp` when every query is answered by `H` (`buildUp_pure`). -/
@[expose]
def hashTable (enc : Encoding X Y Msg Salt) (H : X → Y) :
    (j : ℕ) → (Fin (2 ^ j) → Y) → Y × (ℕ → ℕ → Option Y)
  | 0, c => (c ⟨0, Nat.two_pow_pos 0⟩,
      fun i q ↦ if i = 0 ∧ q = 0 then some (c ⟨0, Nat.two_pow_pos 0⟩) else none)
  | j + 1, c =>
      let r := hashTable enc H j fun q ↦ H (parentInputs enc c q)
      (r.1, fun i q ↦
        if i = j + 1 then (if h : q < 2 ^ (j + 1) then some (c ⟨q, h⟩) else none) else r.2 i q)

/-- `buildUp` with a deterministic hash is `hashTable`. -/
theorem buildUp_pure {m : Type uY → Type*} [Monad m] [LawfulMonad m] (enc : Encoding X Y Msg Salt)
    (H : X → Y) (j : ℕ) (c : Fin (2 ^ j) → Y) :
    buildUp enc (fun x ↦ (pure (H x) : m Y)) j c = pure (hashTable enc H j c) := by
  induction j with
  | zero => rfl
  | succ j ih => simp [buildUp, hashAll_pure, ih, hashTable]

section HonestTable

variable (enc : Encoding X Y Msg Salt) (H : X → Y)

/-- At its own level, the table of `hashTable` holds the labels it was given. -/
theorem hashTable_snd_self (j : ℕ) (c : Fin (2 ^ j) → Y) (q : ℕ) (hq : q < 2 ^ j) :
    (hashTable enc H j c).2 j q = some (c ⟨q, hq⟩) := by
  cases j with
  | zero =>
      have : q = 0 := by simpa using hq
      subst this
      simp [hashTable]
  | succ j => simp [hashTable, hq]

/-- The table of `hashTable` holds the root at level `0`, position `0`. -/
theorem hashTable_snd_root (j : ℕ) (c : Fin (2 ^ j) → Y) :
    (hashTable enc H j c).2 0 0 = some (hashTable enc H j c).1 := by
  induction j with
  | zero => simp [hashTable]
  | succ j ih => simpa [hashTable] using ih _

/-- Every label strictly above the given level is the hash of its two children. -/
theorem hashTable_snd_closed (j : ℕ) (c : Fin (2 ^ j) → Y) (i : ℕ) (hi : i < j) (p : ℕ)
    (hp : p < 2 ^ (i + 1)) :
    ∃ u L R, (hashTable enc H j c).2 i (p / 2) = some u ∧
      (hashTable enc H j c).2 (i + 1) (2 * (p / 2)) = some L ∧
      (hashTable enc H j c).2 (i + 1) (2 * (p / 2) + 1) = some R ∧
      H (enc.node (L, R)) = u := by
  induction j generalizing i with
  | zero => omega
  | succ j ih =>
      have h2 : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [pow_succ]; ring
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · simpa [hashTable, show i ≠ j + 1 by omega, show i ≠ j by omega] using ih _ i hi hp
      · have hq : p / 2 < 2 ^ i := by omega
        refine ⟨_, c ⟨2 * (p / 2), by omega⟩, c ⟨2 * (p / 2) + 1, by omega⟩, ?_, ?_, ?_, rfl⟩
        · simp [hashTable, hashTable_snd_self _ _ _ _ _ hq, parentInputs]
        · simp [hashTable, show 2 * (p / 2) < 2 ^ (i + 1) by omega]
        · simp [hashTable, show 2 * (p / 2) + 1 < 2 ^ (i + 1) by omega]

end HonestTable

/-- The honest root and trapdoor for the function `H`. -/
@[expose]
def honestTree (enc : Encoding X Y Msg Salt) (d : ℕ) (H : X → Y) (msg : Fin (2 ^ d) → Msg)
    (γ : Fin (2 ^ d) → Salt) : Y × Td Y Salt d :=
  let r := hashTable enc H d fun ι ↦ H (enc.leaf (msg ι, γ ι))
  (r.1, (fun ι ↦ some (γ ι), fun j q ↦ r.2 j q))

/-! ## Opening and the check -/

/-- Collect a vector of options into an optional vector: `some` exactly when every entry is. -/
@[expose]
def optionPi {n : ℕ} {α : Type*} (f : Fin n → Option α) : Option (Fin n → α) :=
  if h : ∀ i, (f i).isSome then some fun i ↦ (f i).get (h i) else none

/-- `optionPi f = some g` exactly when every entry of `f` is the entry of `g`. -/
theorem optionPi_eq_some_iff {n : ℕ} {α : Type*} {f : Fin n → Option α} {g : Fin n → α} :
    optionPi f = some g ↔ ∀ i, f i = some (g i) := by
  unfold optionPi
  split_ifs with h
  · simp only [Option.some.injEq]
    constructor
    · rintro rfl i; simp
    · intro hg; funext i; simp [hg i]
  · simp only [false_iff, not_forall]
    obtain ⟨i, hi⟩ := not_forall.mp h
    exact ⟨i, fun hg ↦ by simp [hg] at hi⟩

/-- `optionPi f` is present exactly when every entry of `f` is. -/
theorem isSome_optionPi {n : ℕ} {α : Type*} {f : Fin n → Option α} :
    (optionPi f).isSome ↔ ∀ i, (f i).isSome := by
  unfold optionPi
  split_ifs with h <;> simp [h]

/-- The pair `(a_{ι,j+1}, b_{ι,j+1})` read from a label table, if both labels are present. -/
@[expose]
def pathPair (C : Labels Y d) (ι : Fin (2 ^ d)) (j : Fin d) : Option (Y × Y) := do
  let a ← labelAt C (j + 1) (anc d ι (j + 1))
  let b ← labelAt C (j + 1) (sib (anc d ι (j + 1)))
  pure (a, b)

/-- `Open(Q, td)` (p. 52): for `ι ∈ Q`, the salt and the path pairs read from the trapdoor;
`none` off `Q`, and also where the trapdoor has a `⊥` on the path. -/
@[expose]
def opening (d : ℕ) (Q : Finset (Fin (2 ^ d))) (td : Td Y Salt d) : Pf Y Salt d :=
  fun ι ↦ if ι ∈ Q then
    (td.1 ι).bind fun s ↦ (optionPi (pathPair td.2 ι)).map fun path ↦ ⟨s, path⟩
  else none

/-- The pairs `OutputIO` lists for one opened leaf `ι` with answer `a` (p. 53): the leaf
pair `(f(a, γ_ι) ↦ a_{ι,d})`, then for `j ∈ [1, d]` the node pair
`(f(L_{ι,j}, R_{ι,j}) ↦ a_{ι,j-1})`. -/
@[expose]
def leafIO (enc : Encoding X Y Msg Salt) (rt : Y) (ι : Fin (2 ^ d)) (a : Msg)
    (pp : PathProof Y Salt d) : List (X × Y) :=
  (enc.leaf (a, pp.salt), pp.node rt d) ::
    List.ofFn fun j : Fin d ↦ (enc.node (order (anc d ι (j + 1)) (pp.path j)), pp.node rt j)

/-- The pairs of the leaf `ι`, if it is answered and opened. -/
@[expose]
def entryIO (enc : Encoding X Y Msg Salt) (rt : Y) (ι : Fin (2 ^ d)) :
    Option Msg → Option (PathProof Y Salt d) → List (X × Y)
  | some a, some pp => leafIO enc rt ι a pp
  | _, _ => []

/-- `OutputIO(rt, Q, ans, pf)` (p. 53). It returns `none` unless `pf` has an entry exactly
at the positions of `Q = dom ans`; otherwise it lists the pairs of every opened leaf, each
distinct pair once. -/
@[expose]
def outputIO [DecidableEq X] [DecidableEq Y] (enc : Encoding X Y Msg Salt) (d : ℕ) (rt : Y)
    (ans : PartialVec (2 ^ d) Msg) (pf : Pf Y Salt d) : Option (List (X × Y)) :=
  if ∀ ι, (pf ι).isSome = (ans ι).isSome then
    some ((List.finRange (2 ^ d)).flatMap fun ι ↦ entryIO enc rt ι (ans ι) (pf ι)).dedup
  else none

/-- The check of `scheme enc d` against a partial table `D : X → Option Y`: reject if `OutputIO`
does not parse, and otherwise accept exactly when `D` holds every listed pair. Against the total
table of a function `H` it is the check evaluated at `H` (`checkIOForm_checkOn` and
`VectorCommitment.CheckIOForm.simulateQ_check`). -/
@[expose]
def checkOn [DecidableEq X] [DecidableEq Y] (enc : Encoding X Y Msg Salt) (d : ℕ)
    (D : X → Option Y) (rt : Y) (ans : PartialVec (2 ^ d) Msg) (pf : Pf Y Salt d) : Bool :=
  (outputIO enc d rt ans pf).elim false (checkIOOn D)

section Lemmas

variable (enc : Encoding X Y Msg Salt)

/-- One opened leaf lists `d + 1` pairs: the leaf pair and one node pair per level. -/
theorem length_leafIO (rt : Y) (ι : Fin (2 ^ d)) (a : Msg) (pp : PathProof Y Salt d) :
    (leafIO enc rt ι a pp).length = d + 1 := by
  simp [leafIO]

/-- A position lists `d + 1` pairs if it is answered, and none otherwise. -/
theorem length_entryIO_le (rt : Y) (ι : Fin (2 ^ d)) (a : Option Msg)
    (pp : Option (PathProof Y Salt d)) :
    (entryIO enc rt ι a pp).length ≤ if a.isSome then d + 1 else 0 := by
  rcases a with _ | a <;> rcases pp with _ | pp <;> simp [entryIO, length_leafIO]

/-- An entry of an opening read from a trapdoor holds the path pairs of the trapdoor. -/
theorem path_of_opening_eq_some {Q : Finset (Fin (2 ^ d))} {td : Td Y Salt d} {ι : Fin (2 ^ d)}
    {pp : PathProof Y Salt d} (h : opening d Q td ι = some pp) (j : Fin d) :
    labelAt td.2 ((j : ℕ) + 1) (anc d ι ((j : ℕ) + 1)) = some (pp.path j).1 ∧
      labelAt td.2 ((j : ℕ) + 1) (sib (anc d ι ((j : ℕ) + 1))) = some (pp.path j).2 := by
  unfold opening at h
  split_ifs at h
  obtain ⟨s, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨path, hpath, rfl⟩ := Option.map_eq_some_iff.mp h
  have hj := optionPi_eq_some_iff.mp hpath j
  simp only [pathPair, Option.bind_eq_bind, Option.pure_def] at hj
  obtain ⟨a, ha, hj⟩ := Option.bind_eq_some_iff.mp hj
  obtain ⟨b, hb, hj⟩ := Option.bind_eq_some_iff.mp hj
  dsimp only
  rw [← Option.some.inj hj]
  exact ⟨ha, hb⟩

variable [DecidableEq X] [DecidableEq Y]

/-- `OutputIO` lists at most `d + 1` pairs per opened position. -/
theorem length_outputIO_le (rt : Y) (ans : PartialVec (2 ^ d) Msg) (pf : Pf Y Salt d)
    (io : List (X × Y)) (h : outputIO enc d rt ans pf = some io) :
    io.length ≤ ans.dom.card * (d + 1) := by
  unfold outputIO at h
  split_ifs at h with hpf
  obtain rfl := Option.some.inj h.symm
  refine (List.dedup_sublist _).length_le.trans ?_
  rw [List.length_flatMap]
  calc ((List.finRange (2 ^ d)).map fun ι ↦ (entryIO enc rt ι (ans ι) (pf ι)).length).sum
      ≤ ((List.finRange (2 ^ d)).map fun ι ↦ if (ans ι).isSome then d + 1 else 0).sum :=
        List.sum_le_sum fun ι _ ↦ length_entryIO_le enc rt ι _ _
    _ = ∑ ι, if (ans ι).isSome then d + 1 else 0 := by
        rw [← List.sum_ofFn, List.ofFn_eq_map]
    _ = ans.dom.card * (d + 1) := by
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
        rfl

end Lemmas

/-! ## Consistent trapdoors and completeness -/

/-- A trapdoor `td` is consistent with the root `rt`, the answers `ans` and a relation `G` between
oracle inputs and outputs when every hash relation that the opening of `dom ans` lists holds for
`G`:

* the root label is `rt`;
* above a present label, both children and the parent are present, and the parent is related by
  `G` to the node input of the children;
* at every answered position the salt and the leaf label are present, and the leaf label is
  related by `G` to the leaf input.

The honest trapdoor is consistent for `G x y := H x = y` (`consistent_honestTree`); the extracted
trapdoor of §8.3 is consistent for `G x y := D x = some y`. -/
structure Consistent (G : X → Y → Prop) (enc : Encoding X Y Msg Salt) (rt : Y)
    (ans : PartialVec (2 ^ d) Msg) (td : Td Y Salt d) : Prop where
  /-- The root label is `rt`. -/
  root : labelAt td.2 0 0 = some rt
  /-- Above a present label, the parent and both children are present and hash under `G`. -/
  closed : ∀ i < d, ∀ p < 2 ^ (i + 1), (labelAt td.2 (i + 1) p).isSome →
    ∃ u L R, labelAt td.2 i (p / 2) = some u ∧ labelAt td.2 (i + 1) (2 * (p / 2)) = some L ∧
      labelAt td.2 (i + 1) (2 * (p / 2) + 1) = some R ∧ G (enc.node (L, R)) u
  /-- At an answered position, the salt and the leaf label are present and hash under `G`. -/
  leaf : ∀ ι a, ans ι = some a → ∃ s l, td.1 ι = some s ∧ labelAt td.2 d ι = some l ∧
    G (enc.leaf (a, s)) l

namespace Consistent

variable {G : X → Y → Prop} {enc : Encoding X Y Msg Salt} {rt : Y} {ans : PartialVec (2 ^ d) Msg}
  {td : Td Y Salt d}

/-- Below a present leaf label, every label on the path to the root is present. -/
theorem isSome_anc (hc : Consistent G enc rt ans td) (ι : Fin (2 ^ d))
    (hι : (labelAt td.2 d ι).isSome) (j : ℕ) (hj : j ≤ d) :
    (labelAt td.2 j (anc d ι j)).isSome := by
  suffices h : ∀ k j, j + k = d → (labelAt td.2 j (anc d ι j)).isSome from
    h (d - j) j (by omega)
  intro k
  induction k with
  | zero =>
      intro j hj
      obtain rfl : j = d := by omega
      simpa [anc_self] using hι
  | succ k ih =>
      intro j hj
      obtain ⟨u, -, -, hu, -, -, -⟩ :=
        hc.closed j (by omega) _ (anc_lt ι.isLt (by omega)) (ih (j + 1) (by omega))
      rw [anc_succ_div_two (by omega)] at hu
      simp [hu]

/-- The sibling of a present label is present. -/
theorem isSome_sib (hc : Consistent G enc rt ans td) {j p : ℕ} (hj : j < d)
    (hp : p < 2 ^ (j + 1)) (h : (labelAt td.2 (j + 1) p).isSome) :
    (labelAt td.2 (j + 1) (sib p)).isSome := by
  obtain ⟨u, L, R, -, hL, hR, -⟩ := hc.closed j hj p hp h
  unfold sib
  split_ifs with h2
  · rw [show p + 1 = 2 * (p / 2) + 1 by omega, hR]; rfl
  · rw [show p - 1 = 2 * (p / 2) by omega, hL]; rfl

/-- A present label and its sibling, put in order, hash under `G` to their parent. -/
theorem node_rel (hc : Consistent G enc rt ans td) {j p : ℕ} (hj : j < d)
    (hp : p < 2 ^ (j + 1)) {A B : Y} (hA : labelAt td.2 (j + 1) p = some A)
    (hB : labelAt td.2 (j + 1) (sib p) = some B) :
    ∃ u, labelAt td.2 j (p / 2) = some u ∧ G (enc.node (order p (A, B))) u := by
  obtain ⟨u, L, R, hu, hL, hR, hG⟩ := hc.closed j hj p hp (by simp [hA])
  refine ⟨u, hu, ?_⟩
  unfold sib at hB
  unfold order
  split_ifs at hB ⊢ with h
  · rw [show 2 * (p / 2) = p by omega, hA] at hL
    rw [show 2 * (p / 2) + 1 = p + 1 by omega, hB] at hR
    cases hL; cases hR; exact hG
  · rw [show 2 * (p / 2) + 1 = p by omega, hA] at hR
    rw [show 2 * (p / 2) = p - 1 by omega, hB] at hL
    cases hL; cases hR; exact hG

/-- Every answered position of a consistent trapdoor is opened. -/
theorem opening_eq_some (hc : Consistent G enc rt ans td) {ι : Fin (2 ^ d)} {a : Msg}
    (ha : ans ι = some a) :
    ∃ pp : PathProof Y Salt d, opening d ans.dom td ι = some pp ∧ td.1 ι = some pp.salt := by
  obtain ⟨s, l, hs, hl, -⟩ := hc.leaf ι a ha
  have hpair : ∀ j : Fin d, ∃ A B, labelAt td.2 ((j : ℕ) + 1) (anc d ι ((j : ℕ) + 1)) = some A ∧
      labelAt td.2 ((j : ℕ) + 1) (sib (anc d ι ((j : ℕ) + 1))) = some B := by
    intro j
    have h₁ := hc.isSome_anc ι (by simp [hl]) (j + 1) j.isLt
    have h₂ := hc.isSome_sib j.isLt (anc_lt ι.isLt j.isLt) h₁
    exact ⟨_, _, (Option.some_get h₁).symm, (Option.some_get h₂).symm⟩
  choose A B hA hB using hpair
  refine ⟨⟨s, fun j ↦ (A j, B j)⟩, ?_, hs⟩
  have hpath : optionPi (pathPair td.2 ι) = some fun j ↦ (A j, B j) :=
    optionPi_eq_some_iff.mpr fun j ↦ by simp [pathPair, hA j, hB j]
  simp [opening, PartialVec.mem_dom, ha, hs, hpath]

variable [DecidableEq X] [DecidableEq Y]

/-- **The opening of a consistent trapdoor is accepted relative to `G`**: `OutputIO` parses the
opening of `dom ans`, and every pair it lists satisfies `G`. -/
theorem outputIO_opening (hc : Consistent G enc rt ans td) :
    ∃ io, outputIO enc d rt ans (opening d ans.dom td) = some io ∧ ∀ p ∈ io, G p.1 p.2 := by
  have hpf : ∀ ι, (opening d ans.dom td ι).isSome = (ans ι).isSome := by
    intro ι
    cases ha : ans ι with
    | none => simp [opening, PartialVec.mem_dom, ha]
    | some a =>
        obtain ⟨pp, h, -⟩ := hc.opening_eq_some ha
        simp [h]
  refine ⟨_, ite_eq_left hpf, fun p hp ↦ ?_⟩
  rw [List.mem_dedup, List.mem_flatMap] at hp
  obtain ⟨ι, -, hp⟩ := hp
  cases ha : ans ι with
  | none => simp [ha, entryIO] at hp
  | some a =>
      obtain ⟨pp, hpp, hs⟩ := hc.opening_eq_some ha
      have hpath := path_of_opening_eq_some hpp
      rw [ha, hpp] at hp
      simp only [entryIO, leafIO, List.mem_cons, List.mem_ofFn] at hp
      rcases hp with rfl | ⟨j, rfl⟩
      · obtain ⟨s, l, hs', hl, hG⟩ := hc.leaf ι a ha
        rw [hs] at hs'
        cases hs'
        suffices pp.node rt d = l by rw [this]; exact hG
        unfold PathProof.node
        split_ifs with hd
        · have h' : labelAt td.2 (d - 1 + 1) (anc d ι (d - 1 + 1)) =
              some (pp.path ⟨d - 1, by omega⟩).1 := (hpath ⟨d - 1, by omega⟩).1
          rw [show d - 1 + 1 = d by omega, anc_self, hl] at h'
          exact (Option.some.inj h').symm
        · obtain rfl : d = 0 := by omega
          have hι : (ι : ℕ) = 0 := by have := ι.isLt; simp at this; omega
          rw [hι, hc.root] at hl
          exact Option.some.inj hl
      · obtain ⟨u, hu, hG⟩ :=
          hc.node_rel j.isLt (anc_lt ι.isLt j.isLt) (hpath j).1 (hpath j).2
        rw [anc_succ_div_two j.isLt] at hu
        suffices pp.node rt j = u by rw [this]; exact hG
        unfold PathProof.node
        split_ifs with hj
        · have h' : labelAt td.2 ((j : ℕ) - 1 + 1) (anc d ι ((j : ℕ) - 1 + 1)) =
              some (pp.path ⟨(j : ℕ) - 1, by omega⟩).1 := (hpath ⟨(j : ℕ) - 1, by omega⟩).1
          rw [show (j : ℕ) - 1 + 1 = j by omega, hu] at h'
          exact (Option.some.inj h').symm
        · rw [show (j : ℕ) = 0 by omega, anc_zero ι.isLt, hc.root] at hu
          exact Option.some.inj hu

end Consistent

/-- The honest trapdoor is consistent with the honest root and with any restriction of the
committed message, for the relation `H x = y`. -/
theorem consistent_honestTree (enc : Encoding X Y Msg Salt) (d : ℕ) (H : X → Y)
    (msg : Fin (2 ^ d) → Msg) (γ : Fin (2 ^ d) → Salt) (Q : Finset (Fin (2 ^ d))) :
    Consistent (fun x y ↦ H x = y) enc (honestTree enc d H msg γ).1 (PartialVec.restrict msg Q)
      (honestTree enc d H msg γ).2 := by
  have hT : ∀ j p, j ≤ d → p < 2 ^ j → labelAt (honestTree enc d H msg γ).2.2 j p =
      (hashTable enc H d fun ι ↦ H (enc.leaf (msg ι, γ ι))).2 j p :=
    fun j p hj hp ↦ labelAt_mk _ hj hp
  refine ⟨?_, ?_, ?_⟩
  · rw [hT 0 0 (Nat.zero_le d) (Nat.two_pow_pos 0)]
    exact hashTable_snd_root enc H d _
  · intro i hi p hp _
    obtain ⟨u, L, R, hu, hL, hR, hG⟩ := hashTable_snd_closed enc H d _ i hi p hp
    have h2 : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [pow_succ]; ring
    refine ⟨u, L, R, ?_, ?_, ?_, hG⟩
    · rwa [hT _ _ (by omega) (by omega)]
    · rwa [hT _ _ (by omega) (by omega)]
    · rwa [hT _ _ (by omega) (by omega)]
  · intro ι a ha
    have : a = msg ι := by
      by_cases hq : ι ∈ Q <;> simp [hq] at ha
      exact ha.symm
    subst this
    refine ⟨γ ι, H (enc.leaf (msg ι, γ ι)), rfl, ?_, rfl⟩
    rw [hT _ _ le_rfl ι.isLt]
    exact hashTable_snd_self enc H d _ ι ι.isLt

/-! ## The number of distinct pairs -/

section Count

variable (enc : Encoding X Y Msg Salt)

/-- The leaf pair of the opened position `ι`, if there is one. -/
private def leafPair (d : ℕ) (rt : Y) (ans : PartialVec (2 ^ d) Msg) (pf : Pf Y Salt d)
    (ι : Fin (2 ^ d)) : Option (X × Y) :=
  (ans ι).bind fun a ↦ (pf ι).map fun pp ↦ (enc.leaf (a, pp.salt), pp.node rt d)

/-- The node pair of the internal vertex `(j, q)` of a label table, if its labels are present. -/
private def nodePair (rt : Y) (C : Labels Y d) (j q : ℕ) : Option (X × Y) :=
  (labelAt C (j + 1) (2 * q)).bind fun L ↦ (labelAt C (j + 1) (2 * q + 1)).bind fun R ↦
    (if j = 0 then some rt else labelAt C j q).map fun u ↦ (enc.node (L, R), u)

/-- The node pair at level `j` of an opening read from a trapdoor depends only on the vertex
`(j, anc d ι j)`. -/
private theorem nodePair_opening (rt : Y) {Q : Finset (Fin (2 ^ d))} {td : Td Y Salt d}
    {ι : Fin (2 ^ d)} {pp : PathProof Y Salt d} (h : opening d Q td ι = some pp) (j : Fin d) :
    nodePair enc rt td.2 j (anc d ι j) =
      some (enc.node (order (anc d ι (j + 1)) (pp.path j)), pp.node rt j) := by
  obtain ⟨hA, hB⟩ := path_of_opening_eq_some h j
  have hu : (if (j : ℕ) = 0 then some rt else labelAt td.2 j (anc d ι j)) =
      some (pp.node rt j) := by
    unfold PathProof.node
    by_cases h0 : (j : ℕ) = 0
    · rw [ite_eq_left h0, dite_eq_right (by omega)]
    · rw [ite_eq_right h0, dite_eq_left ⟨by omega, j.isLt.le⟩]
      have h' : labelAt td.2 ((j : ℕ) - 1 + 1) (anc d ι ((j : ℕ) - 1 + 1)) =
          some (pp.path ⟨(j : ℕ) - 1, by omega⟩).1 :=
        (path_of_opening_eq_some h ⟨j - 1, by omega⟩).1
      rwa [show (j : ℕ) - 1 + 1 = j by omega] at h'
  have hP : anc d ι j = anc d ι (j + 1) / 2 := (anc_succ_div_two j.isLt).symm
  have hLR : labelAt td.2 ((j : ℕ) + 1) (2 * anc d ι j) =
        some (order (anc d ι (j + 1)) (pp.path j)).1 ∧
      labelAt td.2 ((j : ℕ) + 1) (2 * anc d ι j + 1) =
        some (order (anc d ι (j + 1)) (pp.path j)).2 := by
    rw [hP]
    unfold sib at hB
    unfold order
    split_ifs at hB ⊢ with hpar
    · rw [show 2 * (anc d ι (j + 1) / 2) = anc d ι (j + 1) by omega]
      exact ⟨hA, hB⟩
    · rw [show 2 * (anc d ι (j + 1) / 2) + 1 = anc d ι (j + 1) by omega,
        show 2 * (anc d ι (j + 1) / 2) = anc d ι (j + 1) - 1 by omega]
      exact ⟨hB, hA⟩
  by_cases h0 : (j : ℕ) = 0
  · rw [ite_eq_left h0] at hu
    rw [← Option.some.inj hu]
    simp only [nodePair]
    rw [hLR.1, hLR.2]
    simp [h0]
  · rw [ite_eq_right h0] at hu
    simp only [nodePair]
    rw [hLR.1, hLR.2]
    simp [h0, hu]

/-- Every pair of an opening read from a trapdoor is a leaf pair or a node pair. -/
private theorem mem_entryIO_opening (rt : Y) {ans : PartialVec (2 ^ d) Msg}
    {Q : Finset (Fin (2 ^ d))} {td : Td Y Salt d} {ι : Fin (2 ^ d)} {p : X × Y}
    (hp : p ∈ entryIO enc rt ι (ans ι) (opening d Q td ι)) :
    leafPair enc d rt ans (opening d Q td) ι = some p ∨
      ∃ j : Fin d, nodePair enc rt td.2 j (anc d ι j) = some p := by
  cases ha : ans ι with
  | none => simp [ha, entryIO] at hp
  | some a =>
      cases hpp : opening d Q td ι with
      | none => simp [ha, hpp, entryIO] at hp
      | some pp =>
          rw [ha, hpp] at hp
          simp only [entryIO, leafIO, List.mem_cons, List.mem_ofFn] at hp
          rcases hp with rfl | ⟨j, rfl⟩
          · left
            simp [leafPair, ha, hpp]
          · exact Or.inr ⟨j, nodePair_opening enc rt hpp j⟩

private theorem card_toFinset_le {α : Type*} (o : Option α) : o.toFinset.card ≤ 1 := by
  cases o <;> simp

private theorem sum_two_pow_fin (d : ℕ) : ∑ j : Fin d, 2 ^ (j : ℕ) + 1 = 2 ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [pow_succ]
      omega

variable [DecidableEq X] [DecidableEq Y]

/-- **The openings read from one trapdoor list at most `2 · 2 ^ d - 1` distinct pairs**: one leaf
pair per position and one node pair per internal vertex. For arbitrary proofs the `d + 1` pairs of
the different positions can all differ (`length_outputIO_le`). -/
theorem length_outputIO_opening_le (rt : Y) (ans : PartialVec (2 ^ d) Msg)
    (Q : Finset (Fin (2 ^ d))) (td : Td Y Salt d) (io : List (X × Y))
    (h : outputIO enc d rt ans (opening d Q td) = some io) : io.length ≤ 2 * 2 ^ d - 1 := by
  unfold outputIO at h
  split_ifs at h with hpf
  obtain rfl := Option.some.inj h.symm
  let A : Finset (X × Y) :=
    Finset.univ.biUnion fun ι ↦ (leafPair enc d rt ans (opening d Q td) ι).toFinset
  let B : Finset (X × Y) := Finset.univ.biUnion fun j : Fin d ↦
    (Finset.univ : Finset (Fin (2 ^ (j : ℕ)))).biUnion fun q ↦ (nodePair enc rt td.2 j q).toFinset
  have hsub : ((List.finRange (2 ^ d)).flatMap fun ι ↦
      entryIO enc rt ι (ans ι) (opening d Q td ι)).dedup.toFinset ⊆ A ∪ B := by
    intro p hp
    rw [List.mem_toFinset, List.mem_dedup, List.mem_flatMap] at hp
    obtain ⟨ι, -, hp⟩ := hp
    rcases mem_entryIO_opening enc rt hp with h | ⟨j, h⟩
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨ι, Finset.mem_univ _, by simp [h]⟩)
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, ?_⟩)
      exact Finset.mem_biUnion.mpr
        ⟨⟨anc d ι j, anc_lt ι.isLt j.isLt.le⟩, Finset.mem_univ _, by simp [h]⟩
  have hA : A.card ≤ 2 ^ d := by
    refine Finset.card_biUnion_le.trans ?_
    calc _ ≤ ∑ _ι : Fin (2 ^ d), 1 := Finset.sum_le_sum fun _ _ ↦ card_toFinset_le _
      _ = 2 ^ d := by simp
  have hB : B.card ≤ ∑ j : Fin d, 2 ^ (j : ℕ) := by
    refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun j _ ↦ ?_)
    refine Finset.card_biUnion_le.trans ?_
    calc _ ≤ ∑ _q : Fin (2 ^ (j : ℕ)), 1 := Finset.sum_le_sum fun _ _ ↦ card_toFinset_le _
      _ = 2 ^ (j : ℕ) := by simp
  have hsum := sum_two_pow_fin d
  rw [← List.toFinset_card_of_nodup (List.nodup_dedup _)]
  calc _ ≤ (A ∪ B).card := Finset.card_le_card hsub
    _ ≤ A.card + B.card := Finset.card_union_le _ _
    _ ≤ 2 * 2 ^ d - 1 := by omega

end Count

end Generic

/-! ## Commitment with fixed salts

`commitTree` samples no coins and only queries `X →ₒ Y`, so `Y` and `Salt` may live in any
universe. They share one: `OracleComp` binds results of a single universe, and the result pairs
the root in `Y` with a trapdoor holding salts. -/

section Commit

variable {X : Type uX} {Y Salt : Type uY} {Msg : Type uM}

/-- `Commit^f(m)` after the salts are fixed (p. 52): hash the leaves `f(m_ι, γ_ι)` and then
the tree bottom-up. It returns the root and the trapdoor `(γ, C)`. -/
@[expose]
def commitTree (enc : Encoding X Y Msg Salt) (d : ℕ) (msg : Fin (2 ^ d) → Msg)
    (γ : Fin (2 ^ d) → Salt) : OracleComp (X →ₒ Y) (Y × Td Y Salt d) := do
  let leaves ← hashAll (fun x ↦ ((X →ₒ Y).query x : OracleComp (X →ₒ Y) Y)) (2 ^ d)
    fun ι ↦ enc.leaf (msg ι, γ ι)
  let r ← buildUp enc (fun x ↦ ((X →ₒ Y).query x : OracleComp (X →ₒ Y) Y)) d leaves
  pure (r.1, (fun ι ↦ some (γ ι), fun j q ↦ r.2 j q))

/-- Answering the queries of `commitTree` with `H` gives the honest root and trapdoor. -/
theorem simulateQ_commitTree {m : Type uY → Type*} [Monad m] [LawfulMonad m]
    (enc : Encoding X Y Msg Salt) (d : ℕ) (H : X → Y) (msg : Fin (2 ^ d) → Msg)
    (γ : Fin (2 ^ d) → Salt) :
    simulateQ (fun x ↦ (pure (H x) : m Y)) (commitTree enc d msg γ) =
      pure (honestTree enc d H msg γ) := by
  simp only [commitTree, simulateQ_bind, simulateQ_hashAll, simulateQ_buildUp,
    simulateQ_spec_query, hashAll_pure, pure_bind, buildUp_pure, simulateQ_pure]
  rfl

end Commit

/-! ## The scheme

`Commit` samples the salts with `unifSpec` and queries `X →ₒ Y`, so this section takes `Y` and
`Salt` in `Type`. -/

section Scheme

variable {X : Type uX} {Y Salt : Type} {Msg : Type uM}

/-- The salted Merkle commitment `MT[σ, Σ, ℓ = 2 ^ d, ν]` (Def 8.2, pp. 52–53). `Commit` samples
the salts uniformly with `unifSpec` and hashes bottom-up, `Open` reads the paths from the
trapdoor, and `Check` is `OutputIO` then `CheckIO`. `Open` is deterministic and `Check` is
coin-free, so the scheme is a `DetVectorCommitment`. -/
@[expose]
def scheme [DecidableEq X] [DecidableEq Y] [SampleableType Salt] (enc : Encoding X Y Msg Salt)
    (d : ℕ) : DetVectorCommitment X Y Msg Y (Td Y Salt d) (Pf Y Salt d) (2 ^ d) where
  commit msg := do
    let γ ← OracleComp.liftComp ($ᵗ (Fin (2 ^ d) → Salt)) (unifSpec + (X →ₒ Y))
    OracleComp.liftComp (commitTree enc d msg γ) (unifSpec + (X →ₒ Y))
  opening := opening d
  check rt ans pf := (outputIO enc d rt ans pf).elim (pure false) checkIO

/-- The check of `scheme enc d` has the `CheckIO` form, with at most `d + 1` pairs per opened
position. -/
@[expose]
def checkIOForm [DecidableEq X] [DecidableEq Y] [SampleableType Salt]
    (enc : Encoding X Y Msg Salt) (d : ℕ) :
    (scheme (Msg := Msg) enc d).toVectorCommitment.CheckIOForm where
  outputIO := outputIO enc d
  check_eq _ _ _ := rfl
  qVC q := q * (d + 1)
  qVC_mono _ _ h := Nat.mul_le_mul_right _ h
  length_le rt ans pf io h := length_outputIO_le enc rt ans pf io h

/-- The table check of `checkIOForm enc d` is `checkOn enc d`. -/
theorem checkIOForm_checkOn [DecidableEq X] [DecidableEq Y] [SampleableType Salt]
    (enc : Encoding X Y Msg Salt) (d : ℕ) :
    (checkIOForm enc d).checkOn = checkOn enc d :=
  rfl

/-- **Perfect completeness** of the salted Merkle commitment against every fixed oracle function
(Def 3.7, p. 27; §8.3, p. 55). -/
theorem perfectlyComplete [DecidableEq X] [DecidableEq Y] [SampleableType Salt]
    (enc : Encoding X Y Msg Salt) (d : ℕ) : (scheme (Msg := Msg) enc d).PerfectlyComplete := by
  unfold DetVectorCommitment.PerfectlyComplete
  intro H msg Q z hz
  simp only [scheme, VectorCommitment.fixedOracleImpl, simulateQ_bind] at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨γ, -, hz⟩ := hz
  rw [QueryImpl.simulateQ_add_liftComp_right (QueryImpl.id' unifSpec)
    (fun x ↦ (pure (H x) : ProbComp Y)) (commitTree enc d msg γ)] at hz
  rw [simulateQ_commitTree] at hz
  rw [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  obtain ⟨io, hio, hG⟩ := (consistent_honestTree enc d H msg γ Q).outputIO_opening
  rw [PartialVec.dom_restrict] at hio
  change evalWithAnswerFn _ ((outputIO enc d _ _ (opening d Q _)).elim (pure false) checkIO) = true
  rw [hio, Option.elim_some, evalWithAnswerFn_checkIO, List.all_eq_true]
  intro p hp
  simp [hG p hp]

/-- **Perfect completeness relative to every oracle distribution** (Def 3.7, p. 27): the salted
Merkle commitment, as a general vector commitment, is perfectly complete for every distribution `D`
on oracle functions. -/
theorem perfectlyComplete_toVectorCommitment [DecidableEq X] [DecidableEq Y] [SampleableType Salt]
    [MeasurableSpace (X → Y)] (enc : Encoding X Y Msg Salt) (d : ℕ)
    (D : MeasureTheory.Measure (X → Y)) [MeasureTheory.IsProbabilityMeasure D] :
    (scheme (Msg := Msg) enc d).toVectorCommitment.PerfectlyComplete D :=
  (perfectlyComplete enc d).toVectorCommitment D

end Scheme

end SaltedMerkle
