import BoltProof.Theorems.Authenticity
import BoltProof.Theorems.Balance

/-!
# A concrete valid run (vacuity check)

The theorems of Layer 1 are only as meaningful as the covenant interface is satisfiable.
This file builds the five-transaction NFT lifecycle the test harness builds
(`test/helpers/minSimpleChain.ts`: mint → commit1 → settle1 → commit2 → settle2, where
settle2 rebuilds commit1 and spends its proof) as a concrete `Run` over `Txid := Nat`, and
proves it `Valid`. The primitives are trivial stand-ins (`txid` is the transaction's
`lockTime`, every signature verifies): the point is the *shape* of the spends, which the
interface must admit.
-/

set_option linter.unusedSectionVars false

namespace BoltProof.Example

/-- Trivial primitives over `Txid := Nat`: a transaction's id is its `lockTime`. -/
def P : Prims Nat :=
  { h160 := fun pk => pk
    verify := fun _ _ _ => true
    txid := fun tx => tx.lockTime
    sighash := fun _ _ => [] }

def iPk : PubKey := [1]
def uPk : PubKey := [2]
def bPk : PubKey := [3]

/-- The genesis identity token, minted by the issuer to itself (tx 0). -/
def g0 : Token Nat :=
  { owner := iPk, commitment := [], commitment2 := [], txoType := 0x00, parent := none,
    grandparent := none, otherGrandparent := none, issuer := iPk, balance := 0, balanceCommit := 0 }

def o0 : Outpoint Nat := ⟨0, 0⟩

/-- commit1 (tx 1): the issuer commits the genesis to the user. -/
def c1 : Token Nat :=
  { owner := iPk, commitment := uPk, commitment2 := [], txoType := 0x21, parent := some o0,
    grandparent := none, otherGrandparent := none, issuer := iPk, balance := 0, balanceCommit := 0 }

def tx1 : TxDesc Nat :=
  { version := 2, inputs := [o0, ⟨100, 0⟩], outputs := [.token c1, .proof uPk, .p2pkh iPk],
    lockTime := 1 }

def s1 : Spend Nat :=
  { tx := tx1, inputIndex := 0, kind := .commit, mode := .transfer, spent := g0,
    spentOutpoint := o0, other := none, signer := iPk, sig := [], sigHashType := 0x41,
    recipient := uPk, recipient2 := [], piece := 0, anc := none, ancB := none }

def o1 : Outpoint Nat := ⟨1, 0⟩

/-- settle1 (tx 2): signed by the issuer (`is2ndTx`), ownership moves to the user. -/
def t2 : Token Nat :=
  { owner := uPk, commitment := [], commitment2 := [], txoType := 0x00, parent := some o1,
    grandparent := some o0, otherGrandparent := none, issuer := iPk, balance := 0,
    balanceCommit := 0 }

def tx2 : TxDesc Nat :=
  { version := 2, inputs := [o1, ⟨101, 0⟩], outputs := [.token t2, .p2pkh iPk], lockTime := 2 }

def s2 : Spend Nat :=
  { tx := tx2, inputIndex := 0, kind := .settle, mode := .transfer, spent := c1,
    spentOutpoint := o1, other := none, signer := iPk, sig := [], sigHashType := 0x41,
    recipient := [], recipient2 := [], piece := 0, anc := none, ancB := none }

def o2 : Outpoint Nat := ⟨2, 0⟩

/-- commit2 (tx 3): the user commits to the bucket. -/
def c3 : Token Nat :=
  { owner := uPk, commitment := bPk, commitment2 := [], txoType := 0x21, parent := some o2,
    grandparent := some o1, otherGrandparent := none, issuer := iPk, balance := 0,
    balanceCommit := 0 }

def tx3 : TxDesc Nat :=
  { version := 2, inputs := [o2, ⟨102, 0⟩], outputs := [.token c3, .proof bPk, .p2pkh uPk],
    lockTime := 3 }

def s3 : Spend Nat :=
  { tx := tx3, inputIndex := 0, kind := .commit, mode := .transfer, spent := t2,
    spentOutpoint := o2, other := none, signer := uPk, sig := [], sigHashType := 0x41,
    recipient := bPk, recipient2 := [], piece := 0, anc := none, ancB := none }

def o3 : Outpoint Nat := ⟨3, 0⟩

/-- settle2 (tx 4): rebuilds commit1 (the grandparent) and co-spends its proof `(1, 1)`. -/
def t4 : Token Nat :=
  { owner := bPk, commitment := [], commitment2 := [], txoType := 0x00, parent := some o3,
    grandparent := some o2, otherGrandparent := none, issuer := iPk, balance := 0,
    balanceCommit := 0 }

def tx4 : TxDesc Nat :=
  { version := 2, inputs := [o3, ⟨1, 1⟩, ⟨103, 0⟩], outputs := [.token t4, .p2pkh uPk],
    lockTime := 4 }

def s4 : Spend Nat :=
  { tx := tx4, inputIndex := 0, kind := .settle, mode := .transfer, spent := c3,
    spentOutpoint := o3, other := none, signer := uPk, sig := [], sigHashType := 0x41,
    recipient := [], recipient2 := [], piece := 0, anc := some tx1, ancB := none }

/-- The run: one genesis token and four accepted spends. -/
def r : Run Nat := { issuer := iPk, genesis := [(o0, g0)], steps := [s1, s2, s3, s4] }

theorem accepts_s1 : Accepts P .nft s1 := by
  refine
    {
      input_is_spent := rfl
      version := (by decide)
      l1_owner := rfl
      l1_sig := rfl
      l1_type := rfl
      commit_type := fun _ => (by decide)
      commit_mode := fun _ => (by decide)
      settle_type := fun h => (by cases h)
      settle_mode := fun h => (by cases h)
      l5_issuer := fun _ => rfl
      l5_no_merge_at_genesis := fun _ => (by decide)
      l2_outs := fun _ => ⟨[.p2pkh iPk], (by decide), rfl⟩
      l2_melt := fun h => (by cases h)
      l6_bound := fun h => (by cases h)
      l6_split := fun _ h => (by cases h)
      l6_merge := fun _ h => (by cases h)
      l6_settle_split := fun h => (by cases h)
      l6_settle_merge := fun h => (by cases h)
      other_iff_merge := (by decide)
      other_input := fun _ h => (by cases h)
      l_merge_same_issuer := fun _ h => (by cases h)
      other_settle_typed := fun _ h => (by cases h)
      l3_rebuild := fun h => (by cases h)
      l3_merge := fun h => (by cases h)
      l4_null := fun _ => ⟨rfl, rfl⟩ }

theorem accepts_s2 : Accepts P .nft s2 := by
  refine
    {
      input_is_spent := rfl
      version := (by decide)
      l1_owner := rfl
      l1_sig := rfl
      l1_type := rfl
      commit_type := fun h => (by cases h)
      commit_mode := fun h => (by cases h)
      settle_type := fun _ => (by decide)
      settle_mode := fun _ => rfl
      l5_issuer := fun _ => rfl
      l5_no_merge_at_genesis := fun h => (by cases h)
      l2_outs := fun _ => ⟨[.p2pkh iPk], (by decide), rfl⟩
      l2_melt := fun h => (by cases h)
      l6_bound := fun h => (by cases h)
      l6_split := fun h => (by cases h)
      l6_merge := fun h => (by cases h)
      l6_settle_split := fun _ h => (by cases h)
      l6_settle_merge := fun _ h => (by cases h)
      other_iff_merge := (by decide)
      other_input := fun _ h => (by cases h)
      l_merge_same_issuer := fun _ h => (by cases h)
      other_settle_typed := fun _ h => (by cases h)
      l3_rebuild := fun _ _ h => (by cases h)
      l3_merge := fun _ _ h => (by cases h)
      l4_null := fun _ => ⟨rfl, rfl⟩ }

theorem accepts_s3 : Accepts P .nft s3 := by
  refine
    {
      input_is_spent := rfl
      version := (by decide)
      l1_owner := rfl
      l1_sig := rfl
      l1_type := rfl
      commit_type := fun _ => (by decide)
      commit_mode := fun _ => (by decide)
      settle_type := fun h => (by cases h)
      settle_mode := fun h => (by cases h)
      l5_issuer := fun h => ?_
      l5_no_merge_at_genesis := fun h => (by cases h)
      l2_outs := fun _ => ⟨[.p2pkh uPk], (by decide), rfl⟩
      l2_melt := fun h => (by cases h)
      l6_bound := fun h => (by cases h)
      l6_split := fun _ h => (by cases h)
      l6_merge := fun _ h => (by cases h)
      l6_settle_split := fun h => (by cases h)
      l6_settle_merge := fun h => (by cases h)
      other_iff_merge := (by decide)
      other_input := fun _ h => (by cases h)
      l_merge_same_issuer := fun _ h => (by cases h)
      other_settle_typed := fun _ h => (by cases h)
      l3_rebuild := fun h => (by cases h)
      l3_merge := fun h => (by cases h)
      l4_null := fun _ => ⟨rfl, rfl⟩ }
  -- the issuer guard does not fire: t2 has a parent and is settle-typed
  exact absurd h (by decide)

theorem accepts_s4 : Accepts P .nft s4 := by
  refine
    {
      input_is_spent := rfl
      version := (by decide)
      l1_owner := rfl
      l1_sig := rfl
      l1_type := rfl
      commit_type := fun h => (by cases h)
      commit_mode := fun h => (by cases h)
      settle_type := fun _ => (by decide)
      settle_mode := fun _ => rfl
      l5_issuer := fun h => ?_
      l5_no_merge_at_genesis := fun h => (by cases h)
      l2_outs := fun _ => ⟨[.p2pkh uPk], (by decide), rfl⟩
      l2_melt := fun h => (by cases h)
      l6_bound := fun h => (by cases h)
      l6_split := fun h => (by cases h)
      l6_merge := fun h => (by cases h)
      l6_settle_split := fun _ h => (by cases h)
      l6_settle_merge := fun _ h => (by cases h)
      other_iff_merge := (by decide)
      other_input := fun _ h => (by cases h)
      l_merge_same_issuer := fun _ h => (by cases h)
      other_settle_typed := fun _ h => (by cases h)
      l3_rebuild := fun _ gp hgp => ?_
      l3_merge := fun _ _ h => (by cases h)
      l4_null := fun h => ?_ }
  · -- the issuer guard does not fire: c3 is commit-typed but has a grandparent
    exact absurd h (by decide)
  · -- the rebuilt ancestor is commit1; its proof (1, 1) is co-spent
    have : gp = o1 := by simpa [s4, c3] using hgp.symm
    subst this
    exact ⟨tx1, c1, rfl, rfl, rfl, ⟨1, uPk, rfl, (by decide)⟩, fun h => (by cases h)⟩
  · rcases h with h | h <;> cases h

/-- The honest NFT lifecycle is a valid run of the interface: the theorems are not vacuous. -/
theorem valid : r.Valid P .nft := by
  refine ⟨⟨(by decide), (by decide), (by decide), fun h => (by cases h), (by decide)⟩, ?_⟩
  intro k s hk
  match k, hk with
  | 0, hk =>
    cases hk
    exact ⟨accepts_s1, (by decide), fun _ h => (by cases h), (by decide)⟩
  | 1, hk =>
    cases hk
    exact ⟨accepts_s2, (by decide), fun _ h => (by cases h), (by decide)⟩
  | 2, hk =>
    cases hk
    exact ⟨accepts_s3, (by decide), fun _ h => (by cases h), (by decide)⟩
  | 3, hk =>
    cases hk
    exact ⟨accepts_s4, (by decide), fun _ h => (by cases h), (by decide)⟩
  | n + 4, hk => simp [r] at hk

/-- The live set after the lifecycle is the single token owned by the bucket. -/
theorem live_eq : r.live P = [(⟨4, 0⟩, t4)] := by decide

end BoltProof.Example
