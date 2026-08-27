/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import HashSig.SLHDSA.Oracle
public import HashSig.SLHDSA.Encoding
public import HashSig.SLHDSA.WotsChecksum
public import VCVio.OracleComp.HasQuery.Morphism
public import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# WOTS+ (FIPS 205 §5)

The Winternitz one-time signature over the abstract `Primitives` bundle.  Each algorithm has one
effectful owner implementation parameterized by its public-hash callbacks.  The legacy pure API
and the explicit-oracle API are thin interpretations of that same control flow.

The headline result is `wotsPkFromSig_wotsSign`: recovering the public key from an honest
signature reproduces `wotsPkGen`. Its only ingredient is the hash-chain composition law
`chain_compose`, proved by induction with no hash hypotheses — the deterministic core that
drives XMSS/hypertree correctness downstream.

## References

- NIST FIPS 205, §5 (Algorithms 5–8), §5.4 (the checksum, validated in `WotsChecksum`)
-/

@[expose] public section


namespace SLHDSA

open OracleComp
open WotsChecksum

variable {p : Params}

/-- `0 < w = 2^lgw`. -/
theorem Params.w_pos (p : Params) : 0 < p.w := by
  unfold Params.w; positivity

/-! ### The hash chain (FIPS 205 Algorithm 5) -/

/-- Callback-parametric owner implementation of the WOTS+ chain. -/
def chainWith {Y : Type} {m : Type → Type*} [Monad m]
    (hash : Adrs → Y → m Y) (adrs : Adrs) (x : Y) (i : ℕ) : ℕ → m Y
  | 0 => pure x
  | s + 1 => do
      let y ← chainWith hash adrs x i s
      hash (adrs.setHashAddress (i + s)) y

/-- `chain(X, i, s, PK.seed, ADRS)`: apply `F` `s` times to `X`, starting at hash index `i`
(the `j`-th step uses hash address `i + j`). Structural recursion on the step count. -/
def chain (prims : Primitives p) (pkSeed : prims.PkSeed) (adrs : Adrs) (x : prims.Y)
    (i s : ℕ) : prims.Y :=
  Id.run (chainWith (m := Id) (fun a y => pure (prims.F pkSeed a y)) adrs x i s)

/-- Explicit-public-hash interpretation of the canonical chain control flow. -/
def chainM (prims : Primitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec prims) m] (pkSeed : prims.PkSeed) (adrs : Adrs) (x : prims.Y)
    (i s : ℕ) : m prims.Y :=
  chainWith (PublicHash.f prims pkSeed) adrs x i s

/-- A monad morphism commutes with the callback-parametric WOTS+ chain when it commutes with the
hash callback. -/
theorem chainWith_natural {Y : Type} {m n : Type → Type*} [Monad m] [Monad n]
    (F : m →ᵐ n) (hashm : Adrs → Y → m Y) (hashn : Adrs → Y → n Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y) (adrs : Adrs) (x : Y) (i s : ℕ) :
    F (chainWith hashm adrs x i s) = chainWith hashn adrs x i s := by
  induction s with
  | zero => simp [chainWith, F.mmap_pure]
  | succ s ih => simp [chainWith, F.mmap_bind, ih, hhash]

/-- Query-preserving monad morphisms commute with the explicit-public-hash WOTS+ chain. -/
theorem chainM_natural (prims : Primitives p) {m n : Type → Type*} [Monad m] [Monad n]
    [HasQuery (publicHashSpec prims) m] [HasQuery (publicHashSpec prims) n]
    (F : HasQuery.QueryHom (publicHashSpec prims) m n)
    (pkSeed : prims.PkSeed) (adrs : Adrs) (x : prims.Y) (i s : ℕ) :
    F.toMonadHom (chainM prims pkSeed adrs x i s) =
      chainM prims pkSeed adrs x i s := by
  apply chainWith_natural F.toMonadHom
  intro a y
  change F.toMonadHom
      (query (spec := publicHashSpec prims)
        (PublicHashQuery.thash pkSeed (prims.adrsToKey a) [y])) =
    query (spec := publicHashSpec prims)
      (PublicHashQuery.thash pkSeed (prims.adrsToKey a) [y])
  exact HasQuery.map_query F _

/-- Hash-chain composition: chaining `a` steps then `b` more (from index `i + a`) equals
chaining `a + b` steps from `i`. The deterministic backbone of WOTS+ correctness. -/
theorem chain_compose (prims : Primitives p) (pkSeed : prims.PkSeed) (adrs : Adrs)
    (x : prims.Y) (i a b : ℕ) :
    chain prims pkSeed adrs (chain prims pkSeed adrs x i a) (i + a) b
      = chain prims pkSeed adrs x i (a + b) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change prims.F pkSeed (adrs.setHashAddress (i + a + b))
          (chain prims pkSeed adrs (chain prims pkSeed adrs x i a) (i + a) b)
        = prims.F pkSeed (adrs.setHashAddress (i + (a + b)))
          (chain prims pkSeed adrs x i (a + b))
    rw [ih, Nat.add_assoc]

/-! ### WOTS+ addresses -/

/-- Address for deriving the secret value of chain `i` (type `WOTS_PRF`, keypair preserved). -/
def wotsSkAdrs (adrs : Adrs) (i : ℕ) : Adrs :=
  ((adrs.setTypeAndClear .wotsPrf).setKeyPairAddress adrs.getKeyPairAddress).setChainAddress i

/-- Base address for the `F`-steps of chain `i` (type `WOTS_HASH`, key-pair preserved,
chain address `i`). -/
def wotsChainAdrs (adrs : Adrs) (i : ℕ) : Adrs :=
  ((adrs.setTypeAndClear .wotsHash).setKeyPairAddress adrs.getKeyPairAddress).setChainAddress i

/-- Address for compressing the `len` chain ends into the WOTS public key (type `WOTS_PK`). -/
def wotsPkAdrs (adrs : Adrs) : Adrs :=
  (adrs.setTypeAndClear .wotsPk).setKeyPairAddress adrs.getKeyPairAddress

/-! ### Message-to-digit derivation (FIPS 205 §5.2–5.4) -/

/-- The `len1` base-`w` message digits of the node being signed. -/
def wotsMsgDigits (prims : Primitives p) (msg : prims.Y) : List ℕ :=
  base2b (prims.yToBytes msg).toList p.lgw p.len1

/-- The full step-count list: message digits followed by the base-`w` checksum digits; length
`len`. -/
def chainLengths (prims : Primitives p) (msg : prims.Y) : List ℕ :=
  wotsFullDigits (wotsMsgDigits prims msg) p.w p.len1 p.len2

/-- Every entry of `chainLengths` is a genuine base-`w` digit (`< w`). -/
theorem chainLengths_mem_lt (prims : Primitives p) (msg : prims.Y) :
    ∀ d ∈ chainLengths prims msg, d < p.w := by
  intro d hd
  unfold chainLengths wotsFullDigits at hd
  rcases List.mem_append.mp hd with h | h
  · have hb := base2b_lt (prims.yToBytes msg).toList p.lgw p.len1 d h
    rwa [Params.w]
  · exact digitsOfBaseW_lt _ p.w p.len2 (Params.w_pos p) d h

/-- The step count of chain `i`: the `i`-th entry of `chainLengths` (`0` past the end). -/
def chainSteps (prims : Primitives p) (msg : prims.Y) (i : ℕ) : ℕ :=
  (chainLengths prims msg).getD i 0

theorem chainSteps_lt (prims : Primitives p) (msg : prims.Y) (i : ℕ) :
    chainSteps prims msg i < p.w := by
  unfold chainSteps
  rw [List.getD_eq_getElem?_getD]
  rcases lt_or_ge i (chainLengths prims msg).length with h | h
  · rw [List.getElem?_eq_getElem h]
    simpa using chainLengths_mem_lt prims msg _ (List.getElem_mem h)
  · rw [List.getElem?_eq_none h]
    simpa using Params.w_pos p

theorem chainSteps_le (prims : Primitives p) (msg : prims.Y) (i : ℕ) :
    chainSteps prims msg i ≤ p.w - 1 :=
  Nat.le_sub_one_of_lt (chainSteps_lt prims msg i)

/-! ### Public-key generation, signing, and recovery -/

/-- A WOTS+ signature: the `len` chain values, length-indexed. -/
abbrev WotsSig (p : Params) (prims : Primitives p) := Vector prims.Y p.len

/-- Callback-parametric owner implementation of all WOTS+ public-key chain ends. -/
def wotsPkGenTopsWith (prims : Primitives p) {m : Type → Type*} [Monad m]
    (hash : Adrs → prims.Y → m prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) : m (Vector prims.Y p.len) :=
  Vector.ofFnM fun i =>
    chainWith hash (wotsChainAdrs adrs i.val)
      (prims.PRF pk sk (wotsSkAdrs adrs i.val)) 0 (p.w - 1)

/-- Callback-parametric owner implementation of WOTS+ public-key generation. -/
def wotsPkGenWith (prims : Primitives p) {m : Type → Type*} [Monad m]
    (hash : Adrs → prims.Y → m prims.Y)
    (compress : Adrs → List prims.Y → m prims.Y)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) : m prims.Y := do
  let tops ← wotsPkGenTopsWith prims hash sk pk adrs
  compress (wotsPkAdrs adrs) tops.toList

/-- The `len` chain ends of the WOTS+ public key (chain every secret value to the top, `w-1`). -/
def wotsPkGenTops (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) : Vector prims.Y p.len :=
  Id.run (wotsPkGenTopsWith prims
    (m := Id) (fun a y => pure (prims.F pk a y)) sk pk adrs)

/-- WOTS+ public-key generation (FIPS 205 Algorithm 6). -/
def wotsPkGen (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    prims.Y :=
  Id.run (wotsPkGenWith prims
    (m := Id) (fun a y => pure (prims.F pk a y))
    (fun a ys => pure (prims.Tl pk a ys)) sk pk adrs)

/-- Explicit-public-hash WOTS+ public-key chain ends. -/
def wotsPkGenTopsM (prims : Primitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec prims) m]
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) : m (Vector prims.Y p.len) :=
  wotsPkGenTopsWith prims (PublicHash.f prims pk) sk pk adrs

/-- Explicit-public-hash WOTS+ public-key generation. -/
def wotsPkGenM (prims : Primitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec prims) m]
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) : m prims.Y :=
  wotsPkGenWith prims (PublicHash.f prims pk) (PublicHash.tl prims pk) sk pk adrs

/-- Callback-parametric owner implementation of WOTS+ signing. -/
def wotsSignWith (prims : Primitives p) {m : Type → Type*} [Monad m]
    (hash : Adrs → prims.Y → m prims.Y)
    (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) : m (WotsSig p prims) :=
  Vector.ofFnM fun i =>
    chainWith hash (wotsChainAdrs adrs i.val)
      (prims.PRF pk sk (wotsSkAdrs adrs i.val)) 0 (chainSteps prims msg i.val)

/-- WOTS+ signing (FIPS 205 Algorithm 7): chain each secret value to its message height. -/
def wotsSign (prims : Primitives p) (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) : WotsSig p prims :=
  Id.run (wotsSignWith prims
    (m := Id) (fun a y => pure (prims.F pk a y)) msg sk pk adrs)

/-- Explicit-public-hash WOTS+ signing. -/
def wotsSignM (prims : Primitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec prims) m]
    (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) : m (WotsSig p prims) :=
  wotsSignWith prims (PublicHash.f prims pk) msg sk pk adrs

/-- Callback-parametric owner implementation of recovered WOTS+ chain ends. -/
def wotsPkFromSigTopsWith (prims : Primitives p) {m : Type → Type*} [Monad m]
    (hash : Adrs → prims.Y → m prims.Y)
    (sig : WotsSig p prims) (msg : prims.Y) (adrs : Adrs) : m (Vector prims.Y p.len) :=
  Vector.ofFnM fun i =>
    chainWith hash (wotsChainAdrs adrs i.val) sig[i.val] (chainSteps prims msg i.val)
      (p.w - 1 - chainSteps prims msg i.val)

/-- Callback-parametric owner implementation of WOTS+ public-key recovery. -/
def wotsPkFromSigWith (prims : Primitives p) {m : Type → Type*} [Monad m]
    (hash : Adrs → prims.Y → m prims.Y)
    (compress : Adrs → List prims.Y → m prims.Y)
    (sig : WotsSig p prims) (msg : prims.Y) (adrs : Adrs) : m prims.Y := do
  let tops ← wotsPkFromSigTopsWith prims hash sig msg adrs
  compress (wotsPkAdrs adrs) tops.toList

/-- The `len` chain ends recovered from a signature (complete each chain from its message height
to the top). -/
def wotsPkFromSigTops (prims : Primitives p) (sig : WotsSig p prims) (msg : prims.Y)
    (pk : prims.PkSeed) (adrs : Adrs) : Vector prims.Y p.len :=
  Id.run (wotsPkFromSigTopsWith prims
    (m := Id) (fun a y => pure (prims.F pk a y)) sig msg adrs)

/-- WOTS+ public-key recovery from a signature (FIPS 205 Algorithm 8). -/
def wotsPkFromSig (prims : Primitives p) (sig : WotsSig p prims) (msg : prims.Y)
    (pk : prims.PkSeed) (adrs : Adrs) : prims.Y :=
  Id.run (wotsPkFromSigWith prims
    (m := Id) (fun a y => pure (prims.F pk a y))
    (fun a ys => pure (prims.Tl pk a ys)) sig msg adrs)

/-- Explicit-public-hash recovered WOTS+ chain ends. -/
def wotsPkFromSigTopsM (prims : Primitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec prims) m]
    (sig : WotsSig p prims) (msg : prims.Y) (pk : prims.PkSeed)
    (adrs : Adrs) : m (Vector prims.Y p.len) :=
  wotsPkFromSigTopsWith prims (PublicHash.f prims pk) sig msg adrs

/-- Explicit-public-hash WOTS+ public-key recovery. -/
def wotsPkFromSigM (prims : Primitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec prims) m]
    (sig : WotsSig p prims) (msg : prims.Y) (pk : prims.PkSeed)
    (adrs : Adrs) : m prims.Y :=
  wotsPkFromSigWith prims (PublicHash.f prims pk) (PublicHash.tl prims pk)
    sig msg adrs

/-! ### Naturality -/

private theorem monadHom_ofFnM {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n) {α : Type} {k : ℕ}
    (fm : Fin k → m α) (fn : Fin k → n α) (h : ∀ i, F (fm i) = fn i) :
    F (Vector.ofFnM fm) = Vector.ofFnM fn := by
  induction k with
  | zero => simp [F.mmap_pure]
  | succ k ih =>
      rw [Vector.ofFnM_succ, Vector.ofFnM_succ, F.mmap_bind]
      rw [ih (fun i => fm i.castSucc) (fun i => fn i.castSucc) (fun i => h i.castSucc)]
      congr 1
      funext xs
      rw [F.mmap_bind, h (Fin.last k)]
      simp [F.mmap_pure]

/-- A monad morphism commutes with WOTS+ public-key chain generation when it commutes with the
hash callback. -/
theorem wotsPkGenTopsWith_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n) (prims : Primitives p)
    (hashm : Adrs → prims.Y → m prims.Y) (hashn : Adrs → prims.Y → n prims.Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    F (wotsPkGenTopsWith prims hashm sk pk adrs) =
      wotsPkGenTopsWith prims hashn sk pk adrs := by
  apply monadHom_ofFnM F
  intro i
  exact chainWith_natural F hashm hashn hhash _ _ _ _

/-- A monad morphism commutes with WOTS+ public-key generation when it commutes with the public
hash and compression callbacks. -/
theorem wotsPkGenWith_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n) (prims : Primitives p)
    (hashm : Adrs → prims.Y → m prims.Y) (hashn : Adrs → prims.Y → n prims.Y)
    (compressm : Adrs → List prims.Y → m prims.Y)
    (compressn : Adrs → List prims.Y → n prims.Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y)
    (hcompress : ∀ a ys, F (compressm a ys) = compressn a ys)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    F (wotsPkGenWith prims hashm compressm sk pk adrs) =
      wotsPkGenWith prims hashn compressn sk pk adrs := by
  simp [wotsPkGenWith, F.mmap_bind,
    wotsPkGenTopsWith_natural F prims hashm hashn hhash, hcompress]

/-- A monad morphism commutes with WOTS+ signing when it commutes with the hash callback. -/
theorem wotsSignWith_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n) (prims : Primitives p)
    (hashm : Adrs → prims.Y → m prims.Y) (hashn : Adrs → prims.Y → n prims.Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y)
    (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    F (wotsSignWith prims hashm msg sk pk adrs) =
      wotsSignWith prims hashn msg sk pk adrs := by
  apply monadHom_ofFnM F
  intro i
  exact chainWith_natural F hashm hashn hhash _ _ _ _

/-- A monad morphism commutes with WOTS+ recovery-chain generation when it commutes with the
hash callback. -/
theorem wotsPkFromSigTopsWith_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n) (prims : Primitives p)
    (hashm : Adrs → prims.Y → m prims.Y) (hashn : Adrs → prims.Y → n prims.Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y)
    (sig : WotsSig p prims) (msg : prims.Y) (adrs : Adrs) :
    F (wotsPkFromSigTopsWith prims hashm sig msg adrs) =
      wotsPkFromSigTopsWith prims hashn sig msg adrs := by
  apply monadHom_ofFnM F
  intro i
  exact chainWith_natural F hashm hashn hhash _ _ _ _

/-- A monad morphism commutes with WOTS+ public-key recovery when it commutes with the public
hash and compression callbacks. -/
theorem wotsPkFromSigWith_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n) (prims : Primitives p)
    (hashm : Adrs → prims.Y → m prims.Y) (hashn : Adrs → prims.Y → n prims.Y)
    (compressm : Adrs → List prims.Y → m prims.Y)
    (compressn : Adrs → List prims.Y → n prims.Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y)
    (hcompress : ∀ a ys, F (compressm a ys) = compressn a ys)
    (sig : WotsSig p prims) (msg : prims.Y) (adrs : Adrs) :
    F (wotsPkFromSigWith prims hashm compressm sig msg adrs) =
      wotsPkFromSigWith prims hashn compressn sig msg adrs := by
  simp [wotsPkFromSigWith, F.mmap_bind,
    wotsPkFromSigTopsWith_natural F prims hashm hashn hhash, hcompress]

private theorem queryHom_f (prims : Primitives p) {m n : Type → Type*}
    [Monad m] [Monad n] [HasQuery (publicHashSpec prims) m]
    [HasQuery (publicHashSpec prims) n]
    (F : HasQuery.QueryHom (publicHashSpec prims) m n) (pk : prims.PkSeed) :
    ∀ a y, F.toMonadHom (PublicHash.f prims pk a y) = PublicHash.f prims pk a y := by
  intro a y
  change F.toMonadHom
      (query (spec := publicHashSpec prims)
        (PublicHashQuery.thash pk (prims.adrsToKey a) [y])) =
    query (spec := publicHashSpec prims)
      (PublicHashQuery.thash pk (prims.adrsToKey a) [y])
  exact HasQuery.map_query F _

private theorem queryHom_tl (prims : Primitives p) {m n : Type → Type*}
    [Monad m] [Monad n] [HasQuery (publicHashSpec prims) m]
    [HasQuery (publicHashSpec prims) n]
    (F : HasQuery.QueryHom (publicHashSpec prims) m n) (pk : prims.PkSeed) :
    ∀ a ys, F.toMonadHom (PublicHash.tl prims pk a ys) = PublicHash.tl prims pk a ys := by
  intro a ys
  change F.toMonadHom
      (query (spec := publicHashSpec prims)
        (PublicHashQuery.thash pk (prims.adrsToKey a) ys)) =
    query (spec := publicHashSpec prims)
      (PublicHashQuery.thash pk (prims.adrsToKey a) ys)
  exact HasQuery.map_query F _

/-- Query-preserving monad morphisms commute with explicit WOTS+ public-key chain generation. -/
theorem wotsPkGenTopsM_natural (prims : Primitives p)
    {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [HasQuery (publicHashSpec prims) m]
    [HasQuery (publicHashSpec prims) n]
    (F : HasQuery.QueryHom (publicHashSpec prims) m n)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    F.toMonadHom (wotsPkGenTopsM prims sk pk adrs) = wotsPkGenTopsM prims sk pk adrs :=
  wotsPkGenTopsWith_natural F.toMonadHom prims _ _ (queryHom_f prims F pk) sk pk adrs

/-- Query-preserving monad morphisms commute with explicit WOTS+ public-key generation. -/
theorem wotsPkGenM_natural (prims : Primitives p)
    {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [HasQuery (publicHashSpec prims) m]
    [HasQuery (publicHashSpec prims) n]
    (F : HasQuery.QueryHom (publicHashSpec prims) m n)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    F.toMonadHom (wotsPkGenM prims sk pk adrs) = wotsPkGenM prims sk pk adrs :=
  wotsPkGenWith_natural F.toMonadHom prims _ _ _ _
    (queryHom_f prims F pk) (queryHom_tl prims F pk) sk pk adrs

/-- Query-preserving monad morphisms commute with explicit WOTS+ signing. -/
theorem wotsSignM_natural (prims : Primitives p)
    {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [HasQuery (publicHashSpec prims) m]
    [HasQuery (publicHashSpec prims) n]
    (F : HasQuery.QueryHom (publicHashSpec prims) m n)
    (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) :
    F.toMonadHom (wotsSignM prims msg sk pk adrs) = wotsSignM prims msg sk pk adrs :=
  wotsSignWith_natural F.toMonadHom prims _ _ (queryHom_f prims F pk) msg sk pk adrs

/-- Query-preserving monad morphisms commute with explicit WOTS+ recovery-chain generation. -/
theorem wotsPkFromSigTopsM_natural (prims : Primitives p)
    {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [HasQuery (publicHashSpec prims) m]
    [HasQuery (publicHashSpec prims) n]
    (F : HasQuery.QueryHom (publicHashSpec prims) m n)
    (sig : WotsSig p prims) (msg : prims.Y)
    (pk : prims.PkSeed) (adrs : Adrs) :
    F.toMonadHom (wotsPkFromSigTopsM prims sig msg pk adrs) =
      wotsPkFromSigTopsM prims sig msg pk adrs :=
  wotsPkFromSigTopsWith_natural F.toMonadHom prims _ _ (queryHom_f prims F pk) sig msg adrs

/-- Query-preserving monad morphisms commute with explicit WOTS+ public-key recovery. -/
theorem wotsPkFromSigM_natural (prims : Primitives p)
    {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [HasQuery (publicHashSpec prims) m]
    [HasQuery (publicHashSpec prims) n]
    (F : HasQuery.QueryHom (publicHashSpec prims) m n)
    (sig : WotsSig p prims) (msg : prims.Y)
    (pk : prims.PkSeed) (adrs : Adrs) :
    F.toMonadHom (wotsPkFromSigM prims sig msg pk adrs) =
      wotsPkFromSigM prims sig msg pk adrs :=
  wotsPkFromSigWith_natural F.toMonadHom prims _ _ _ _
    (queryHom_f prims F pk) (queryHom_tl prims F pk) sig msg adrs

/-! ### Structural query bounds -/

private theorem isTotalQueryBound_ofFnM {ι α : Type} {spec : OracleSpec ι} {k : ℕ}
    (g : Fin k → OracleComp spec α) (budget : Fin k → ℕ)
    (h : ∀ i, IsTotalQueryBound (g i) (budget i)) :
    IsTotalQueryBound (Vector.ofFnM g) (∑ i, budget i) := by
  induction k with
  | zero =>
      rw [Vector.ofFnM_zero]
      trivial
  | succ k ih =>
      rw [Vector.ofFnM_succ]
      rw [Fin.sum_univ_castSucc]
      apply isTotalQueryBound_bind
        (ih (fun i => g i.castSucc) (fun i => budget i.castSucc) (fun i => h i.castSucc))
      intro xs
      simpa using isTotalQueryBound_bind (n₂ := 0) (h (Fin.last k))
        (fun a => show IsTotalQueryBound (pure (xs.push a) : OracleComp spec _) 0 from trivial)

private theorem publicHash_f_isTotalQueryBound_one (prims : Primitives p)
    (pk : prims.PkSeed) (adrs : Adrs) (x : prims.Y) :
    IsTotalQueryBound
      (PublicHash.f prims pk adrs x : OracleComp (publicHashSpec prims) prims.Y) 1 := by
  simp [PublicHash.f, IsTotalQueryBound]

private theorem publicHash_tl_isTotalQueryBound_one (prims : Primitives p)
    (pk : prims.PkSeed) (adrs : Adrs) (xs : List prims.Y) :
    IsTotalQueryBound
      (PublicHash.tl prims pk adrs xs : OracleComp (publicHashSpec prims) prims.Y) 1 := by
  simp [PublicHash.tl, IsTotalQueryBound]

/-- An explicit WOTS+ chain of length `s` makes at most `s` public-hash queries. -/
theorem chainM_isTotalQueryBound (prims : Primitives p) (pk : prims.PkSeed)
    (adrs : Adrs) (x : prims.Y) (i s : ℕ) :
    IsTotalQueryBound
      (chainM prims pk adrs x i s : OracleComp (publicHashSpec prims) prims.Y) s := by
  induction s with
  | zero => trivial
  | succ s ih =>
      change IsTotalQueryBound
        (chainM prims pk adrs x i s >>= fun y =>
          PublicHash.f prims pk (adrs.setHashAddress (i + s)) y) (s + 1)
      exact isTotalQueryBound_bind ih fun y =>
        publicHash_f_isTotalQueryBound_one prims pk _ y

/-- WOTS+ public-key chain generation makes at most `len * (w - 1)` public-hash queries. -/
theorem wotsPkGenTopsM_isTotalQueryBound (prims : Primitives p)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    IsTotalQueryBound
      (wotsPkGenTopsM prims sk pk adrs :
        OracleComp (publicHashSpec prims) (Vector prims.Y p.len))
      (p.len * (p.w - 1)) := by
  simpa [wotsPkGenTopsM, wotsPkGenTopsWith, chainM] using
    (isTotalQueryBound_ofFnM
      (fun i : Fin p.len =>
        chainM prims pk (wotsChainAdrs adrs i.val)
          (prims.PRF pk sk (wotsSkAdrs adrs i.val)) 0 (p.w - 1))
      (fun _ => p.w - 1)
      (fun i => chainM_isTotalQueryBound prims pk (wotsChainAdrs adrs i.val)
        (prims.PRF pk sk (wotsSkAdrs adrs i.val)) 0 (p.w - 1)))

/-- WOTS+ public-key generation adds one `T_l` query after generating all chain tops. -/
theorem wotsPkGenM_isTotalQueryBound (prims : Primitives p)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    IsTotalQueryBound
      (wotsPkGenM prims sk pk adrs : OracleComp (publicHashSpec prims) prims.Y)
      (p.len * (p.w - 1) + 1) := by
  exact isTotalQueryBound_bind (wotsPkGenTopsM_isTotalQueryBound prims sk pk adrs)
    fun tops => publicHash_tl_isTotalQueryBound_one prims pk (wotsPkAdrs adrs) tops.toList

/-- WOTS+ signing is bounded by one query for every message-selected chain step. -/
theorem wotsSignM_isTotalQueryBound (prims : Primitives p) (msg : prims.Y)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    IsTotalQueryBound
      (wotsSignM prims msg sk pk adrs :
        OracleComp (publicHashSpec prims) (WotsSig p prims))
      (∑ i : Fin p.len, chainSteps prims msg i.val) := by
  exact isTotalQueryBound_ofFnM _ _ fun i =>
    chainM_isTotalQueryBound prims pk (wotsChainAdrs adrs i.val)
      (prims.PRF pk sk (wotsSkAdrs adrs i.val)) 0 (chainSteps prims msg i.val)

/-- WOTS+ recovery-chain generation is bounded by the complementary number of chain queries. -/
theorem wotsPkFromSigTopsM_isTotalQueryBound (prims : Primitives p)
    (sig : WotsSig p prims) (msg : prims.Y) (pk : prims.PkSeed) (adrs : Adrs) :
    IsTotalQueryBound
      (wotsPkFromSigTopsM prims sig msg pk adrs :
        OracleComp (publicHashSpec prims) (Vector prims.Y p.len))
      (∑ i : Fin p.len, (p.w - 1 - chainSteps prims msg i.val)) := by
  exact isTotalQueryBound_ofFnM _ _ fun i =>
    chainM_isTotalQueryBound prims pk (wotsChainAdrs adrs i.val) sig[i.val]
      (chainSteps prims msg i.val) (p.w - 1 - chainSteps prims msg i.val)

/-- WOTS+ public-key recovery adds one `T_l` query after completing the chains. -/
theorem wotsPkFromSigM_isTotalQueryBound (prims : Primitives p)
    (sig : WotsSig p prims) (msg : prims.Y) (pk : prims.PkSeed) (adrs : Adrs) :
    IsTotalQueryBound
      (wotsPkFromSigM prims sig msg pk adrs : OracleComp (publicHashSpec prims) prims.Y)
      ((∑ i : Fin p.len, (p.w - 1 - chainSteps prims msg i.val)) + 1) := by
  exact isTotalQueryBound_bind
    (wotsPkFromSigTopsM_isTotalQueryBound prims sig msg pk adrs)
    fun tops => publicHash_tl_isTotalQueryBound_one prims pk (wotsPkAdrs adrs) tops.toList

/-- Signing followed by recovery is bounded by one full pass over every WOTS+ chain plus the
final `T_l` compression query. -/
theorem wotsSignM_then_wotsPkFromSigM_isTotalQueryBound (prims : Primitives p)
    (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    IsTotalQueryBound ((do
      let sig ← wotsSignM prims msg sk pk adrs
      wotsPkFromSigM prims sig msg pk adrs) :
        OracleComp (publicHashSpec prims) prims.Y)
      (p.len * (p.w - 1) + 1) := by
  have hbound := isTotalQueryBound_bind
    (wotsSignM_isTotalQueryBound prims msg sk pk adrs)
    (fun sig => wotsPkFromSigM_isTotalQueryBound prims sig msg pk adrs)
  have hsum :
      (∑ i : Fin p.len, chainSteps prims msg i.val) +
          (∑ i : Fin p.len, (p.w - 1 - chainSteps prims msg i.val)) =
        p.len * (p.w - 1) := by
    rw [← Finset.sum_add_distrib]
    simp_rw [Nat.add_sub_of_le (chainSteps_le prims msg _)]
    simp
  simpa [← Nat.add_assoc, hsum] using hbound

/-! ### Pure interpretations -/

@[simp]
theorem wotsPkGenTops_eq_ofFn (prims : Primitives p) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) :
    wotsPkGenTops prims sk pk adrs = Vector.ofFn fun i : Fin p.len =>
      chain prims pk (wotsChainAdrs adrs i.val)
        (prims.PRF pk sk (wotsSkAdrs adrs i.val)) 0 (p.w - 1) := by
  unfold wotsPkGenTops wotsPkGenTopsWith
  rw [Vector.idRun_ofFnM]
  rfl

@[simp]
theorem wotsSign_eq_ofFn (prims : Primitives p) (msg : prims.Y) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) :
    wotsSign prims msg sk pk adrs = Vector.ofFn fun i : Fin p.len =>
      chain prims pk (wotsChainAdrs adrs i.val)
        (prims.PRF pk sk (wotsSkAdrs adrs i.val)) 0 (chainSteps prims msg i.val) := by
  unfold wotsSign wotsSignWith
  rw [Vector.idRun_ofFnM]
  rfl

@[simp]
theorem wotsPkFromSigTops_eq_ofFn (prims : Primitives p) (sig : WotsSig p prims)
    (msg : prims.Y) (pk : prims.PkSeed) (adrs : Adrs) :
    wotsPkFromSigTops prims sig msg pk adrs = Vector.ofFn fun i : Fin p.len =>
      chain prims pk (wotsChainAdrs adrs i.val) sig[i.val] (chainSteps prims msg i.val)
        (p.w - 1 - chainSteps prims msg i.val) := by
  unfold wotsPkFromSigTops wotsPkFromSigTopsWith
  rw [Vector.idRun_ofFnM]
  rfl

@[simp]
theorem wotsPkGen_eq_tl (prims : Primitives p) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) :
    wotsPkGen prims sk pk adrs =
      prims.Tl pk (wotsPkAdrs adrs) (wotsPkGenTops prims sk pk adrs).toList := by
  simp [wotsPkGen, wotsPkGenWith, wotsPkGenTops]

@[simp]
theorem wotsPkFromSig_eq_tl (prims : Primitives p) (sig : WotsSig p prims)
    (msg : prims.Y) (pk : prims.PkSeed) (adrs : Adrs) :
    wotsPkFromSig prims sig msg pk adrs =
      prims.Tl pk (wotsPkAdrs adrs) (wotsPkFromSigTops prims sig msg pk adrs).toList := by
  simp [wotsPkFromSig, wotsPkFromSigWith, wotsPkFromSigTops]

/-! ### Deterministic interpretations -/

/-- Interpreting an `ofFnM` traversal pointwise commutes with the free-monad handler. -/
private theorem simulateQ_ofFnM {ι α : Type} {spec : OracleSpec ι} {k : ℕ}
    (answer : QueryImpl spec Id) (g : Fin k → OracleComp spec α) :
    simulateQ answer (Vector.ofFnM g) = Vector.ofFn fun i => simulateQ answer (g i) := by
  calc
    simulateQ answer (Vector.ofFnM g) =
        Vector.ofFnM (fun i => simulateQ answer (g i)) :=
      monadHom_ofFnM (simulateQ' answer) g _ (fun _ => rfl)
    _ = Vector.ofFn fun i => simulateQ answer (g i) := Vector.idRun_ofFnM

/-- Any total deterministic public-hash handler turns the explicit chain into the pure chain for
the induced primitive bundle. -/
@[simp]
theorem simulateQ_chainM_withPublicHash (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) (pkSeed : prims.PkSeed) (adrs : Adrs)
    (x : prims.Y) (i s : ℕ) :
    simulateQ answer
        (chainM prims pkSeed adrs x i s : OracleComp (publicHashSpec prims) prims.Y) =
      chain (PublicHash.withPublicHash prims answer) pkSeed adrs x i s := by
  induction s with
  | zero => rfl
  | succ s ih =>
      change simulateQ answer
          (do
            let y ← chainM prims pkSeed adrs x i s
            PublicHash.f prims pkSeed (adrs.setHashAddress (i + s)) y) =
        (PublicHash.withPublicHash prims answer).F pkSeed
          (adrs.setHashAddress (i + s))
          (chain (PublicHash.withPublicHash prims answer) pkSeed adrs x i s)
      simp [simulateQ_bind, ih, PublicHash.f]
      rfl

/-- The canonical concrete handler recovers the legacy pure WOTS+ chain. -/
@[simp]
theorem simulateQ_chainM (prims : Primitives p) (pkSeed : prims.PkSeed) (adrs : Adrs)
    (x : prims.Y) (i s : ℕ) :
    simulateQ (PublicHash.impl prims)
        (chainM prims pkSeed adrs x i s : OracleComp (publicHashSpec prims) prims.Y) =
      chain prims pkSeed adrs x i s := by
  convert
    simulateQ_chainM_withPublicHash prims (PublicHash.impl prims) pkSeed adrs x i s using 1
  all_goals rfl

/-- Replacing public hashes leaves WOTS+ message-digit derivation unchanged. -/
@[simp]
theorem chainSteps_withPublicHash (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) (msg : prims.Y) (i : ℕ) :
    chainSteps (PublicHash.withPublicHash prims answer) msg i = chainSteps prims msg i := rfl

/-- A deterministic public-hash handler turns explicit key-generation tops into their pure
counterpart for the induced primitive bundle. -/
@[simp]
theorem simulateQ_wotsPkGenTopsM_withPublicHash (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) :
    simulateQ answer
        (wotsPkGenTopsM prims sk pk adrs :
          OracleComp (publicHashSpec prims) (Vector prims.Y p.len)) =
      wotsPkGenTops (PublicHash.withPublicHash prims answer) sk pk adrs := by
  rw [wotsPkGenTops_eq_ofFn]
  apply Vector.ext
  intro j hj
  simp only [wotsPkGenTopsM, wotsPkGenTopsWith, simulateQ_ofFnM,
    Vector.getElem_ofFn]
  exact simulateQ_chainM_withPublicHash prims answer pk (wotsChainAdrs adrs j)
    (prims.PRF pk sk (wotsSkAdrs adrs j)) 0 (p.w - 1)

/-- Canonical deterministic-handler parity for WOTS+ key-generation tops. -/
@[simp]
theorem simulateQ_wotsPkGenTopsM (prims : Primitives p) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ (PublicHash.impl prims)
        (wotsPkGenTopsM prims sk pk adrs :
          OracleComp (publicHashSpec prims) (Vector prims.Y p.len)) =
      wotsPkGenTops prims sk pk adrs := by
  convert
    simulateQ_wotsPkGenTopsM_withPublicHash prims (PublicHash.impl prims) sk pk adrs using 1
  all_goals rfl

/-- A deterministic public-hash handler turns explicit WOTS+ public-key generation into its pure
counterpart for the induced primitive bundle. -/
@[simp]
theorem simulateQ_wotsPkGenM_withPublicHash (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) :
    simulateQ answer
        (wotsPkGenM prims sk pk adrs : OracleComp (publicHashSpec prims) prims.Y) =
      wotsPkGen (PublicHash.withPublicHash prims answer) sk pk adrs := by
  simp only [wotsPkGenM, wotsPkGenWith, simulateQ_bind, PublicHash.tl,
    simulateQ_HasQuery_query]
  change (do
      let tops ← simulateQ answer
        (wotsPkGenTopsM prims sk pk adrs :
          OracleComp (publicHashSpec prims) (Vector prims.Y p.len))
      answer (.thash pk (prims.adrsToKey (wotsPkAdrs adrs)) tops.toList)) = _
  rw [simulateQ_wotsPkGenTopsM_withPublicHash]
  rfl

/-- Canonical deterministic-handler parity for WOTS+ public-key generation. -/
@[simp]
theorem simulateQ_wotsPkGenM (prims : Primitives p) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ (PublicHash.impl prims)
        (wotsPkGenM prims sk pk adrs : OracleComp (publicHashSpec prims) prims.Y) =
      wotsPkGen prims sk pk adrs := by
  convert simulateQ_wotsPkGenM_withPublicHash prims (PublicHash.impl prims) sk pk adrs using 1
  all_goals rfl

/-- A deterministic public-hash handler turns explicit WOTS+ signing into its pure counterpart
for the induced primitive bundle. -/
@[simp]
theorem simulateQ_wotsSignM_withPublicHash (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) (msg : prims.Y) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ answer
        (wotsSignM prims msg sk pk adrs :
          OracleComp (publicHashSpec prims) (WotsSig p prims)) =
      wotsSign (PublicHash.withPublicHash prims answer) msg sk pk adrs := by
  rw [wotsSign_eq_ofFn]
  apply Vector.ext
  intro j hj
  simp only [wotsSignM, wotsSignWith, simulateQ_ofFnM, Vector.getElem_ofFn]
  exact simulateQ_chainM_withPublicHash prims answer pk (wotsChainAdrs adrs j)
    (prims.PRF pk sk (wotsSkAdrs adrs j)) 0 (chainSteps prims msg j)

/-- Canonical deterministic-handler parity for WOTS+ signing. -/
@[simp]
theorem simulateQ_wotsSignM (prims : Primitives p) (msg : prims.Y) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ (PublicHash.impl prims)
        (wotsSignM prims msg sk pk adrs :
          OracleComp (publicHashSpec prims) (WotsSig p prims)) =
      wotsSign prims msg sk pk adrs := by
  convert
    simulateQ_wotsSignM_withPublicHash prims (PublicHash.impl prims) msg sk pk adrs using 1
  all_goals rfl

/-- A deterministic public-hash handler turns explicit WOTS+ recovery tops into their pure
counterpart for the induced primitive bundle. -/
@[simp]
theorem simulateQ_wotsPkFromSigTopsM_withPublicHash (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) (sig : WotsSig p prims) (msg : prims.Y)
    (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ answer
        (wotsPkFromSigTopsM prims sig msg pk adrs :
          OracleComp (publicHashSpec prims) (Vector prims.Y p.len)) =
      wotsPkFromSigTops (PublicHash.withPublicHash prims answer) sig msg pk adrs := by
  rw [wotsPkFromSigTops_eq_ofFn]
  apply Vector.ext
  intro j hj
  simp only [wotsPkFromSigTopsM, wotsPkFromSigTopsWith, simulateQ_ofFnM,
    Vector.getElem_ofFn]
  exact simulateQ_chainM_withPublicHash prims answer pk (wotsChainAdrs adrs j) sig[j]
    (chainSteps prims msg j) (p.w - 1 - chainSteps prims msg j)

/-- Canonical deterministic-handler parity for WOTS+ recovery tops. -/
@[simp]
theorem simulateQ_wotsPkFromSigTopsM (prims : Primitives p) (sig : WotsSig p prims)
    (msg : prims.Y) (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ (PublicHash.impl prims)
        (wotsPkFromSigTopsM prims sig msg pk adrs :
          OracleComp (publicHashSpec prims) (Vector prims.Y p.len)) =
      wotsPkFromSigTops prims sig msg pk adrs := by
  convert
    simulateQ_wotsPkFromSigTopsM_withPublicHash prims (PublicHash.impl prims) sig msg pk adrs
      using 1
  all_goals rfl

/-- A deterministic public-hash handler turns explicit WOTS+ public-key recovery into its pure
counterpart for the induced primitive bundle. -/
@[simp]
theorem simulateQ_wotsPkFromSigM_withPublicHash (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) (sig : WotsSig p prims) (msg : prims.Y)
    (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ answer
        (wotsPkFromSigM prims sig msg pk adrs : OracleComp (publicHashSpec prims) prims.Y) =
      wotsPkFromSig (PublicHash.withPublicHash prims answer) sig msg pk adrs := by
  simp only [wotsPkFromSigM, wotsPkFromSigWith, simulateQ_bind, PublicHash.tl,
    simulateQ_HasQuery_query]
  change (do
      let tops ← simulateQ answer
        (wotsPkFromSigTopsM prims sig msg pk adrs :
          OracleComp (publicHashSpec prims) (Vector prims.Y p.len))
      answer (.thash pk (prims.adrsToKey (wotsPkAdrs adrs)) tops.toList)) = _
  rw [simulateQ_wotsPkFromSigTopsM_withPublicHash]
  rfl

/-- Canonical deterministic-handler parity for WOTS+ public-key recovery. -/
@[simp]
theorem simulateQ_wotsPkFromSigM (prims : Primitives p) (sig : WotsSig p prims)
    (msg : prims.Y) (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ (PublicHash.impl prims)
        (wotsPkFromSigM prims sig msg pk adrs : OracleComp (publicHashSpec prims) prims.Y) =
      wotsPkFromSig prims sig msg pk adrs := by
  convert simulateQ_wotsPkFromSigM_withPublicHash prims (PublicHash.impl prims) sig msg pk adrs
    using 1
  all_goals rfl

/-! ### Correctness -/

/-- Recovering the chain ends from an honest signature reproduces the public-key chain ends. -/
theorem wotsPkFromSigTops_wotsSign (prims : Primitives p) (msg : prims.Y) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) :
    wotsPkFromSigTops prims (wotsSign prims msg sk pk adrs) msg pk adrs
      = wotsPkGenTops prims sk pk adrs := by
  apply Vector.ext
  intro i hi
  simp only [wotsPkFromSigTops_eq_ofFn, wotsPkGenTops_eq_ofFn, wotsSign_eq_ofFn,
    Vector.getElem_ofFn]
  have hc := chain_compose prims pk (wotsChainAdrs adrs i)
    (prims.PRF pk sk (wotsSkAdrs adrs i)) 0 (chainSteps prims msg i)
    (p.w - 1 - chainSteps prims msg i)
  rw [Nat.zero_add] at hc
  rw [hc, Nat.add_sub_cancel' (chainSteps_le prims msg i)]

/-- **WOTS+ correctness** (FIPS 205, Algorithms 6–8): recovering the public key from an honest
signature reproduces `wotsPkGen`. -/
theorem wotsPkFromSig_wotsSign (prims : Primitives p) (msg : prims.Y) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) :
    wotsPkFromSig prims (wotsSign prims msg sk pk adrs) msg pk adrs
      = wotsPkGen prims sk pk adrs := by
  rw [wotsPkFromSig_eq_tl, wotsPkGen_eq_tl]
  rw [wotsPkFromSigTops_wotsSign]

/-- Extensional WOTS+ completeness for every fixed total public-hash answer table.

This is a stateless `QueryImpl ... Id` theorem. It does not by itself establish completeness for
the lazy cached random-oracle handler; the full-table/lazy-oracle bridge is a separate obligation
for the security layer. -/
theorem simulateQ_wotsPkFromSigM_wotsSignM_withPublicHash (prims : Primitives p)
    (answer : QueryImpl (publicHashSpec prims) Id) (msg : prims.Y) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ answer (do
      let sig ← wotsSignM prims msg sk pk adrs
      wotsPkFromSigM prims sig msg pk adrs) =
    simulateQ answer (wotsPkGenM prims sk pk adrs) := by
  simp only [simulateQ_bind, simulateQ_wotsSignM_withPublicHash,
    simulateQ_wotsPkFromSigM_withPublicHash, simulateQ_wotsPkGenM_withPublicHash]
  exact wotsPkFromSig_wotsSign (PublicHash.withPublicHash prims answer) msg sk pk adrs

end SLHDSA
