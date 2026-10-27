import BoltProof.Model.Spend

/-!
# BoltProof.Model.Assumptions

The cryptographic primitives as an abstract interface, and the hardness assumptions of
`docs/formal-proof.md` §1.2 as **hypotheses** (never axioms):

* **A1** (collision resistance of `H`) becomes `CollisionFree P`: `txid` is injective on the
  transactions that occur. It is used only where the hand proof uses it — the ancestor rebuild
  of Lemma 3 (`t1_rebuild_sound`).
* **A2** (existential unforgeability of ECDSA) becomes `OwnerSecrecy P pk signed`: a signature
  that verifies under `pk` was produced by the holder of `pk`'s secret key, and no other key
  hashes to `pk`'s `hash160`. It is used only in Theorem 2.
* **A3** (chain finality) and **A4** (Script correctness) are not modelled in Layer 1. A4 is
  what Layer 2 discharges against the bsv-script-lean semantics for concrete transactions.
-/

namespace BoltProof

/-- The primitives the covenant uses, as opaque functions. -/
structure Prims (Txid : Type) where
  /-- `RIPEMD160(SHA256(·))` on a public key. -/
  h160 : PubKey → PKH
  /-- ECDSA verification `Verify(pk, m, sig)`. -/
  verify : PubKey → Msg → Sig → Bool
  /-- The transaction id, `H(serialised tx)`. -/
  txid : TxDesc Txid → Txid
  /-- The `SIGHASH_ALL | FORKID` digest of input `i` of a transaction. -/
  sighash : TxDesc Txid → Nat → Msg

/-- **Assumption 1** on the domain the covenant hashes: two transactions with the same id are
the same transaction. -/
def CollisionFree {Txid : Type} (P : Prims Txid) : Prop :=
  ∀ a b : TxDesc Txid, P.txid a = P.txid b → a = b

/-- **Assumption 2**, per owner key. `signed m` is the abstract fact "the holder of `pkO`'s
secret key signed `m`"; `euf` says nothing else verifies under `pkO`, and `h160_unique` says
no other key collides with `pkO` under `hash160`. -/
structure OwnerSecrecy {Txid : Type} (P : Prims Txid) (pkO : PubKey) (signed : Msg → Prop) :
    Prop where
  h160_unique : ∀ pk, P.h160 pk = P.h160 pkO → pk = pkO
  euf : ∀ m σ, P.verify pkO m σ = true → signed m

end BoltProof
