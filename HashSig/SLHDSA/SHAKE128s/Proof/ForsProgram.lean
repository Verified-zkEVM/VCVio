/-
Copyright (c) 2026 Tom Wambsgans, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans, Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Statement.Scheme
public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Option

/-!
# Ordered FORS path and recovery views

The addressed Merkle path and climb have leaf-first views over finite authentication families.
The FORS forest uses the same global leaf index throughout; its lower ancestor parity agrees
with the local leaf index. The equations retain the complete monadic program in lawful monads.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s

/-- Finite function and vector collections correspond through componentwise monad morphisms. -/
theorem sequenceFin_ofFnM_bridge {m : Type → Type} {n r : Type → Type*}
    [Monad m] [Monad n] [LawfulMonad n] [Monad r] [LawfulMonad r]
    (F : m →ᵐ r) (G : n →ᵐ r) {α β : Type} {size : Nat}
    (left : Fin size → m α) (right : Fin size → n β) (convert : β → α)
    (h : ∀ i, F (left i) = convert <$> G (right i)) :
    F (sequenceFin size left) =
      (fun (values : Vector β size) (i : Fin size) => convert values[i]) <$>
        G (Vector.ofFnM right) := by
  induction size with
  | zero =>
      rw [sequenceFin, Vector.ofFnM_zero, F.mmap_pure, G.mmap_pure, map_pure]
      congr 1
      funext i
      exact i.elim0
  | succ size ih =>
      rw [sequenceFin, Vector.ofFnM_succ', F.mmap_bind, h 0, bind_map_left,
        G.mmap_bind, map_bind]
      refine bind_congr fun first => ?_
      rw [F.mmap_bind, ih (fun i => left i.succ) (fun i => right i.succ)
        (fun i => h i.succ), bind_map_left, G.mmap_bind, map_bind]
      refine bind_congr fun rest => ?_
      simp only [F.mmap_pure, G.mmap_pure, map_pure]
      congr 1
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp
      · simp

/-- Collecting a finite family as a function is the pointwise view of its monadic vector. -/
theorem sequenceFin_eq_ofFnM_get {m : Type → Type} [Monad m] [LawfulMonad m]
    {α : Type} {size : Nat} (family : Fin size → m α) :
    sequenceFin size family =
      (fun (values : Vector α size) (i : Fin size) => values[i]) <$> Vector.ofFnM family := by
  simpa using sequenceFin_ofFnM_bridge (MonadHom.id m) (MonadHom.id m)
    family family id (fun _ => by simp)

namespace Fors

variable {m : Type → Type} [Monad m] [LawfulMonad m] [HasQuery HashSpec m]

/-- The pointwise view of a FORS authentication path collects sibling roots in level order. -/
theorem authenticationPath_eq_sequenceFin (secretSeed publicSeed : Digest) (address : Address)
    (height index : Nat) :
    (fun (values : Vector Digest height) (j : Fin height) => values[j]) <$>
        authenticationPath (m := m) secretSeed publicSeed address height index =
      sequenceFin height (fun j => node secretSeed publicSeed address j.val
        (PerfectMerkleTree.sibling (index / 2 ^ j.val))) := by
  unfold authenticationPath
  rw [PerfectMerkleTree.intrinsicAuthPathM_eq_ofFnM]
  exact (sequenceFin_eq_ofFnM_get _).symm

/-- FORS signing collects each tree's selected secret before its leaf-first sibling roots. -/
theorem sign_eq_sequenceFin (indices : Indices) (secretSeed publicSeed : Digest)
    (address : Address) :
    sign (m := m) indices secretSeed publicSeed address =
      (sequenceFin forsTrees fun i => do
        let selected ← secret secretSeed publicSeed address
          (i.val * 2 ^ forsHeight + (indices i).val)
        let authentication ← sequenceFin forsHeight fun j =>
          node secretSeed publicSeed address j.val
            (i.val * 2 ^ (forsHeight - j.val) + Nat.xor ((indices i).val / 2 ^ j.val) 1)
        return { secret := selected, authentication } : m ForsSignature) := by
  unfold sign
  apply congrArg (sequenceFin forsTrees)
  funext i
  apply congrArg (fun next : Digest → m ForsTreeSignature =>
    secret secretSeed publicSeed address
      (i.val * 2 ^ forsHeight + (indices i).val) >>= next)
  funext selected
  have hpath :
      (fun (values : Vector Digest forsHeight) (j : Fin forsHeight) => values[j]) <$>
          authenticationPath (m := m) secretSeed publicSeed address forsHeight
            (i.val * 2 ^ forsHeight + (indices i).val) =
        sequenceFin forsHeight (fun j => node secretSeed publicSeed address j.val
          (i.val * 2 ^ (forsHeight - j.val) + Nat.xor ((indices i).val / 2 ^ j.val) 1)) := by
    rw [authenticationPath_eq_sequenceFin]
    apply congrArg (sequenceFin forsHeight)
    funext j
    rw [PerfectMerkleTree.sibling_add_tree_offset j.isLt,
      PerfectMerkleTree.sibling_eq_xor]
  rw [← hpath, bind_map_left]

/-- A FORS climb through an indexed path is the ordered fold of its node hashes. -/
theorem climb_eq_fold (publicSeed : Digest) (address : Address) (index : Nat)
    (leaf : Digest) {height : Nat} (authentication : Fin height → Digest) :
    climb (m := m) publicSeed address index leaf (List.ofFn authentication) =
      (List.finRange height).foldlM (fun value j => do
        let payload := if index / 2 ^ j.val % 2 = 0 then
          bytesBE n value ++ bytesBE n (authentication j)
          else bytesBE n (authentication j) ++ bytesBE n value
        Hashing.tweakable publicSeed (nodeAddress address (j.val + 1)
          (index / 2 ^ (j.val + 1))) payload) leaf := by
  rw [climb, PerfectMerkleTree.climbM_ofFn]
  apply congrArg (fun step : Digest → Fin height → m Digest =>
    (List.finRange height).foldlM step leaf)
  funext value j
  split_ifs <;> rfl

/-- FORS recovery has a per-tree fold view with local-leaf parity and global node addresses. -/
theorem publicKeyFromSignature_eq_fold (signature : ForsSignature) (indices : Indices)
    (publicSeed : Digest) (address : Address) :
    publicKeyFromSignature (m := m) signature indices publicSeed address = (do
      let roots ← sequenceFin forsTrees fun i => do
        let index := i.val * 2 ^ forsHeight + (indices i).val
        let leaf ← Hashing.tweakable publicSeed (nodeAddress address 0 index)
          (bytesBE n (signature i).secret)
        (List.finRange forsHeight).foldlM (fun value j => do
          let payload := if (indices i).val / 2 ^ j.val % 2 = 0 then
            bytesBE n value ++ bytesBE n ((signature i).authentication j)
            else bytesBE n ((signature i).authentication j) ++ bytesBE n value
          Hashing.tweakable publicSeed (nodeAddress address (j.val + 1)
            (index / 2 ^ (j.val + 1))) payload) leaf
      let rootAddress := { address.setTypeAndClear .forsRoots with keyPair := address.keyPair }
      Hashing.tweakable publicSeed rootAddress (digestArrayBytes roots) : m Digest) := by
  have hpar (i : Fin forsTrees) (j : Fin forsHeight) :
      (i.val * 2 ^ forsHeight + (indices i).val) / 2 ^ j.val % 2 =
        (indices i).val / 2 ^ j.val % 2 :=
    PerfectMerkleTree.ancestor_mod_two_add_tree_offset j.isLt i.val (indices i).val
  unfold publicKeyFromSignature
  simp_rw [climb_eq_fold, hpar]

end Fors

end SLHDSA.SHAKE128s
