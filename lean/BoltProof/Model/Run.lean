import BoltProof.Model.Covenant

/-!
# BoltProof.Model.Run

Token chains (`docs/formal-proof.md` §1.5), generalised to the split/merge DAG the fungible
covenant produces: a **run** is a set of genesis tokens plus a sequence of accepted spends,
each consuming live token UTXOs and producing new ones. `liveAfter k` is the token UTXO set
after `k` steps; `everAfter k` every token output created so far. `ValidRun` is the UTXO-model
validity the chain enforces around the covenant: inputs must be live, new transaction ids are
fresh, and every spend satisfies `Accepts`.
-/

namespace BoltProof

variable {Txid : Type} [DecidableEq Txid]

/-- The token outputs among `outs`, numbered from `j`, keyed by `(txid, index)`. -/
def producedFrom (txid : Txid) : List (Out Txid) → Nat → List (Outpoint Txid × Token Txid)
  | [], _ => []
  | .token t :: os, j => ((⟨txid, j⟩ : Outpoint Txid), t) :: producedFrom txid os (j + 1)
  | _ :: os, j => producedFrom txid os (j + 1)

/-- The token at key `o`, if present (first match). -/
def lookupKey (o : Outpoint Txid) : List (Outpoint Txid × Token Txid) → Option (Token Txid)
  | [] => none
  | x :: xs => if x.1 = o then some x.2 else lookupKey o xs

namespace Spend

/-- The token outputs this spend's transaction creates, keyed by their outpoints. -/
def produced (P : Prims Txid) (s : Spend Txid) : List (Outpoint Txid × Token Txid) :=
  producedFrom (P.txid s.tx) s.tx.outputs 0

end Spend

/-- A run: who issued, the genesis token UTXOs, and the spends in order. -/
structure Run (Txid : Type) where
  issuer : PubKey
  genesis : List (Outpoint Txid × Token Txid)
  steps : List (Spend Txid)

/-- Drop the entries keyed by `o`. -/
def removeKey (o : Outpoint Txid) (l : List (Outpoint Txid × Token Txid)) :
    List (Outpoint Txid × Token Txid) :=
  l.filter fun x => decide (x.1 ≠ o)

/-- Drop the entries keyed by any of `os`. -/
def removeKeys (os : List (Outpoint Txid)) (l : List (Outpoint Txid × Token Txid)) :
    List (Outpoint Txid × Token Txid) :=
  os.foldl (fun acc o => removeKey o acc) l

namespace Run

/-- The token UTXO set after `k` steps. -/
def liveAfter (P : Prims Txid) (r : Run Txid) : Nat → List (Outpoint Txid × Token Txid)
  | 0 => r.genesis
  | k + 1 =>
    match r.steps[k]? with
    | none => r.liveAfter P k
    | some s => removeKeys s.consumed (r.liveAfter P k) ++ s.produced P

/-- Every token output created in the first `k` steps (never pruned). -/
def everAfter (P : Prims Txid) (r : Run Txid) : Nat → List (Outpoint Txid × Token Txid)
  | 0 => r.genesis
  | k + 1 =>
    match r.steps[k]? with
    | none => r.everAfter P k
    | some s => r.everAfter P k ++ s.produced P

/-- The final token UTXO set. -/
def live (P : Prims Txid) (r : Run Txid) : List (Outpoint Txid × Token Txid) :=
  r.liveAfter P r.steps.length

/-- The token that was created at outpoint `o`, if any. -/
def tokenAt (P : Prims Txid) (r : Run Txid) (o : Outpoint Txid) : Option (Token Txid) :=
  lookupKey o (r.everAfter P r.steps.length)

/-- The value held by the live set after `k` steps (Theorem 3). -/
def float (P : Prims Txid) (r : Run Txid) (k : Nat) : Nat :=
  ((r.liveAfter P k).map fun x => x.2.value).sum

/-- The value destroyed by melts in the first `k` steps. -/
def melted (P : Prims Txid) (r : Run Txid) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    r.melted P k +
      match r.steps[k]? with
      | some s => if s.kind = .melt then s.spent.value else 0
      | none => 0

/-- The sum of the genesis balances. -/
def genesisValue (r : Run Txid) : Nat := (r.genesis.map fun x => x.2.value).sum

/-- The genesis set is well-formed: parentless, settle-typed, issued by `r.issuer`, bounded,
and keyed by distinct outpoints. -/
structure GenesisOK (fam : Fam) (r : Run Txid) : Prop where
  parentless : ∀ x ∈ r.genesis,
    x.2.parent = none ∧ x.2.grandparent = none ∧ x.2.otherGrandparent = none
  settleTyped : ∀ x ∈ r.genesis, x.2.txoType ∈ fam.settleTypes
  issuer : ∀ x ∈ r.genesis, x.2.issuer = r.issuer
  bounded : fam = .fungible → ∀ x ∈ r.genesis, x.2.balance ≤ Fam.maxBalance
  nodup : (r.genesis.map (·.1)).Nodup

/-- Step `k` is valid: the covenant accepts it, its token inputs are live with exactly the
fields the spend claims, and its transaction id is new. -/
structure StepOK (P : Prims Txid) (fam : Fam) (r : Run Txid) (k : Nat) (s : Spend Txid) :
    Prop where
  accepts : Accepts P fam s
  spent_live : (s.spentOutpoint, s.spent) ∈ r.liveAfter P k
  other_live : ∀ o, s.other = some o → (o.2, o.1) ∈ r.liveAfter P k
  fresh : ∀ x ∈ r.everAfter P k, x.1.txid ≠ P.txid s.tx

/-- A valid run (§1.5): a well-formed genesis set and valid steps throughout. -/
def Valid (P : Prims Txid) (fam : Fam) (r : Run Txid) : Prop :=
  GenesisOK fam r ∧ ∀ k s, r.steps[k]? = some s → StepOK P fam r k s

end Run

end BoltProof
