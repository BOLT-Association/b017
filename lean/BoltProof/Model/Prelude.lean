/-!
# BoltProof.Model.Prelude

Abstract carriers for the protocol model. Nothing in Layer 1 computes a hash or verifies a
signature: byte strings are opaque lists, transaction ids are a type parameter, and every
cryptographic fact enters as an explicit hypothesis (see `BoltProof.Model.Assumptions`).
-/

namespace BoltProof

/-- A byte string. Only equality is ever used in Layer 1. -/
abbrev Bytes := List Nat

/-- A 20-byte public-key hash, `hash160 pk`. -/
abbrev PKH := Bytes

/-- A compressed public key. -/
abbrev PubKey := Bytes

/-- An ECDSA signature. -/
abbrev Sig := Bytes

/-- A signature message: the sighash digest. -/
abbrev Msg := Bytes

/-- A transaction output reference `(txid, vout)`. `Txid` is abstract: the model never hashes. -/
structure Outpoint (Txid : Type) where
  txid : Txid
  vout : Nat
deriving DecidableEq, Repr

end BoltProof
