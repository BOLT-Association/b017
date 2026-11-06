import BoltProof.Bridge.Glue.AuthBolt.Spec
import BoltProof.Model.Covenant
import BsvScript.Tx

/-!
# The `AuthBOLT` lock and its abstraction into the model

The locking script is the six field pushes followed by the suffix (`lockOf`); `WF` is the widths
the pushes carry, `decodeLock` reads the fields back, and `lock_pushes` runs the pushes
symbolically so a run of the whole lock is a run of the suffix from `Fields.stack`
(`AuthBolt/Spec.lean`).

The second half abstracts a real spend into the model's vocabulary (`Model/Spend.lean`): a lock's
fields become a `Token` (`tokenOf`), an output becomes an `Out` by its script (`outOf`), a
transaction becomes a `TxDesc` (`absTx`), and the spend of a token at input `i` with the
unlocking arguments `a` becomes a `Spend` (`spendOf`). `AuthBolt/Refine.lean` proves that
`Accepts` holds of `spendOf` whenever the bytes accept.
-/

set_option autoImplicit false

namespace BoltProof.Glue.AuthBolt

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget BsvScript.Tx
open BoltProof.Bridge.Generated

/-! ## The lock -/

/-- Well-formed lock fields: the widths the six pushes carry. -/
structure WF (f : Fields) : Prop where
  pkh : f.pkh.length = 20
  com : f.com.length = 20
  ty : f.ty.length = 1
  parent : f.parent.length = 36
  gp : f.gp.length = 36
  issuer : f.issuer.length = 33

/-- The locking script: the six pushes (`pkh`, `com`, `ty`, `parent`, `gp`, `issuer`), then the
suffix. -/
def lockOf (f : Fields) : Bytes :=
  20 :: (f.pkh ++ 20 :: (f.com ++ 1 :: (f.ty ++ 36 :: (f.parent ++ 36 :: (f.gp ++ 33 :: (f.issuer ++
    AuthBolt.suffix))))))

theorem lockOf_length {f : Fields} (hwf : WF f) : (lockOf f).length = 152 + AuthBolt.suffix.length := by
  simp [lockOf, hwf.pkh, hwf.com, hwf.ty, hwf.parent, hwf.gp, hwf.issuer]; omega

/-- The six pushes put the fields on the stack, `issuer` on top: a run of the lock is a run of the
suffix from `Fields.stack`. -/
theorem lock_pushes {env : Env} (he : EnvOK env) {t : Bytes} {r : GOut} {f : Fields} {S A : List Bytes}
    {C : Cond} {cs : Bytes} {m kk : Nat} (hact : C.isActive = true) (hwf : WF f)
    (h : run Eval.opExec env (lockOf f) t (St S A m C kk cs) = r) (hr : r.IsOk) :
    ∃ m' k', run Eval.opExec env AuthBolt.suffix t (St (f.stack ++ S) A m' C k' cs) = r := by
  unfold lockOf at h
  obtain ⟨-, _, _, h⟩ := inv_push_20 he hact h hr
  rw [List.take_left' hwf.pkh, List.drop_left' hwf.pkh] at h
  obtain ⟨-, _, _, h⟩ := inv_push_20 he hact h hr
  rw [List.take_left' hwf.com, List.drop_left' hwf.com] at h
  obtain ⟨-, _, _, h⟩ := inv_push_1 he hact h hr
  rw [List.take_left' hwf.ty, List.drop_left' hwf.ty] at h
  obtain ⟨-, _, _, h⟩ := inv_push_36 he hact h hr
  rw [List.take_left' hwf.parent, List.drop_left' hwf.parent] at h
  obtain ⟨-, _, _, h⟩ := inv_push_36 he hact h hr
  rw [List.take_left' hwf.gp, List.drop_left' hwf.gp] at h
  obtain ⟨-, _, _, h⟩ := inv_push_33 he hact h hr
  rw [List.take_left' hwf.issuer, List.drop_left' hwf.issuer] at h
  exact ⟨_, _, h⟩

/-- The fields read back off a locking script: the push opcodes at their places, the suffix after
them, nothing else. -/
def decodeLock (s : Bytes) : Option Fields :=
  if s.length = 152 + AuthBolt.suffix.length ∧ s[0]? = some 20 ∧ s[21]? = some 20 ∧ s[42]? = some 1 ∧
      s[44]? = some 36 ∧ s[81]? = some 36 ∧ s[118]? = some 33 ∧ s.drop 152 = AuthBolt.suffix then
    some { pkh := (s.drop 1).take 20, com := (s.drop 22).take 20, ty := (s.drop 43).take 1,
           parent := (s.drop 45).take 36, gp := (s.drop 82).take 36, issuer := (s.drop 119).take 33 }
  else none

/-! The lock's layout: what sits after each push, for the decoder and for the welds. -/

theorem lockOf_drop_1 (f : Fields) : (lockOf f).drop 1 =
    f.pkh ++ 20 :: (f.com ++ 1 :: (f.ty ++ 36 :: (f.parent ++ 36 :: (f.gp ++ 33 :: (f.issuer ++ AuthBolt.suffix))))) := rfl
theorem lockOf_drop_21 {f : Fields} (hwf : WF f) : (lockOf f).drop 21 =
    20 :: (f.com ++ 1 :: (f.ty ++ 36 :: (f.parent ++ 36 :: (f.gp ++ 33 :: (f.issuer ++ AuthBolt.suffix))))) := by
  rw [show (21 : Nat) = 1 + 20 from rfl, ← List.drop_drop, lockOf_drop_1, List.drop_left' hwf.pkh]
theorem lockOf_drop_22 {f : Fields} (hwf : WF f) : (lockOf f).drop 22 =
    f.com ++ 1 :: (f.ty ++ 36 :: (f.parent ++ 36 :: (f.gp ++ 33 :: (f.issuer ++ AuthBolt.suffix)))) := by
  rw [show (22 : Nat) = 21 + 1 from rfl, ← List.drop_drop, lockOf_drop_21 hwf]; rfl
theorem lockOf_drop_42 {f : Fields} (hwf : WF f) : (lockOf f).drop 42 =
    1 :: (f.ty ++ 36 :: (f.parent ++ 36 :: (f.gp ++ 33 :: (f.issuer ++ AuthBolt.suffix)))) := by
  rw [show (42 : Nat) = 22 + 20 from rfl, ← List.drop_drop, lockOf_drop_22 hwf, List.drop_left' hwf.com]
theorem lockOf_drop_43 {f : Fields} (hwf : WF f) : (lockOf f).drop 43 =
    f.ty ++ 36 :: (f.parent ++ 36 :: (f.gp ++ 33 :: (f.issuer ++ AuthBolt.suffix))) := by
  rw [show (43 : Nat) = 42 + 1 from rfl, ← List.drop_drop, lockOf_drop_42 hwf]; rfl
theorem lockOf_drop_44 {f : Fields} (hwf : WF f) : (lockOf f).drop 44 =
    36 :: (f.parent ++ 36 :: (f.gp ++ 33 :: (f.issuer ++ AuthBolt.suffix))) := by
  rw [show (44 : Nat) = 43 + 1 from rfl, ← List.drop_drop, lockOf_drop_43 hwf, List.drop_left' hwf.ty]
theorem lockOf_drop_45 {f : Fields} (hwf : WF f) : (lockOf f).drop 45 =
    f.parent ++ 36 :: (f.gp ++ 33 :: (f.issuer ++ AuthBolt.suffix)) := by
  rw [show (45 : Nat) = 44 + 1 from rfl, ← List.drop_drop, lockOf_drop_44 hwf]; rfl
theorem lockOf_drop_81 {f : Fields} (hwf : WF f) : (lockOf f).drop 81 =
    36 :: (f.gp ++ 33 :: (f.issuer ++ AuthBolt.suffix)) := by
  rw [show (81 : Nat) = 45 + 36 from rfl, ← List.drop_drop, lockOf_drop_45 hwf, List.drop_left' hwf.parent]
theorem lockOf_drop_82 {f : Fields} (hwf : WF f) : (lockOf f).drop 82 = f.gp ++ 33 :: (f.issuer ++ AuthBolt.suffix) := by
  rw [show (82 : Nat) = 81 + 1 from rfl, ← List.drop_drop, lockOf_drop_81 hwf]; rfl
theorem lockOf_drop_118 {f : Fields} (hwf : WF f) : (lockOf f).drop 118 = 33 :: (f.issuer ++ AuthBolt.suffix) := by
  rw [show (118 : Nat) = 82 + 36 from rfl, ← List.drop_drop, lockOf_drop_82 hwf, List.drop_left' hwf.gp]
theorem lockOf_drop_119 {f : Fields} (hwf : WF f) : (lockOf f).drop 119 = f.issuer ++ AuthBolt.suffix := by
  rw [show (119 : Nat) = 118 + 1 from rfl, ← List.drop_drop, lockOf_drop_118 hwf]; rfl
theorem lockOf_drop_152 {f : Fields} (hwf : WF f) : (lockOf f).drop 152 = AuthBolt.suffix := by
  rw [show (152 : Nat) = 119 + 33 from rfl, ← List.drop_drop, lockOf_drop_119 hwf, List.drop_left' hwf.issuer]

/-- A well-formed lock decodes to its fields. -/
theorem decodeLock_lockOf {f : Fields} (hwf : WF f) : decodeLock (lockOf f) = some f := by
  have g : ∀ (n : Nat) (b : Nat) (r : Bytes), (lockOf f).drop n = b :: r → (lockOf f)[n]? = some b := by
    intro n b r hn
    have := @List.getElem?_drop _ (lockOf f) n 0
    rw [Nat.add_zero] at this
    rw [← this, hn]; rfl
  unfold decodeLock
  rw [ite_eq_left ⟨lockOf_length hwf, rfl, g _ _ _ (lockOf_drop_21 hwf), g _ _ _ (lockOf_drop_42 hwf),
    g _ _ _ (lockOf_drop_44 hwf), g _ _ _ (lockOf_drop_81 hwf), g _ _ _ (lockOf_drop_118 hwf), lockOf_drop_152 hwf⟩]
  congr 1
  rw [lockOf_drop_1, lockOf_drop_22 hwf, lockOf_drop_43 hwf, lockOf_drop_45 hwf, lockOf_drop_82 hwf,
    lockOf_drop_119 hwf, List.take_left' hwf.pkh, List.take_left' hwf.com, List.take_left' hwf.ty,
    List.take_left' hwf.parent, List.take_left' hwf.gp, List.take_left' hwf.issuer]

/-! ## The abstraction into the model -/

/-- The 36-byte outpoint field as the model's optional outpoint. The covenant tests the field with
`OP_BIN2NUM`, so the genesis marker is the field that reads as the script number zero (the
all-zero field, or zero with the sign bit); everything else is a real outpoint, txid then index. -/
def outpointOf (b : Bytes) : Option (Outpoint Bytes) :=
  if decode b = 0 then none else some ⟨b.take 32, leNat (b.drop 32)⟩

/-- The token a lock's fields describe. The NFT family carries no balance, no second commitment and
no other grandparent. -/
def tokenOf (f : Fields) : Token Bytes :=
  { owner := f.pkh, commitment := f.com, commitment2 := [], txoType := f.ty.headD 0,
    parent := outpointOf f.parent, grandparent := outpointOf f.gp, otherGrandparent := none,
    issuer := f.issuer, balance := 0, balanceCommit := 0 }

/-- The pay-to-proof script a commit emits: `02 b017 OP_EQUALVERIFY OP_DUP OP_HASH160 <pkh>
OP_EQUALVERIFY OP_CHECKSIG`. -/
def proofScript (pkh : Bytes) : Bytes := [2, 0xb0, 0x17, 0x88, 0x76, 0xa9, 0x14] ++ pkh ++ [0x88, 0xac]

/-- A plain P2PKH script. -/
def p2pkhScript (pkh : Bytes) : Bytes := [0x76, 0xa9, 0x14] ++ pkh ++ [0x88, 0xac]

/-- An output as the model sees it, by its script alone: a decodable lock is a token, the
pay-to-proof template is a proof output, P2PKH is P2PKH, anything else is other. -/
def outOf (o : TxOut) : Out Bytes :=
  match decodeLock o.scriptPubKey with
  | some f => .token (tokenOf f)
  | none =>
    if o.scriptPubKey.length = 29 ∧ o.scriptPubKey.take 7 = [2, 0xb0, 0x17, 0x88, 0x76, 0xa9, 0x14] ∧
        o.scriptPubKey.drop 27 = [0x88, 0xac] then .proof ((o.scriptPubKey.drop 7).take 20)
    else if o.scriptPubKey.length = 25 ∧ o.scriptPubKey.take 3 = [0x76, 0xa9, 0x14] ∧
        o.scriptPubKey.drop 23 = [0x88, 0xac] then .p2pkh ((o.scriptPubKey.drop 3).take 20)
    else .other

/-- A transaction as the model sees it. -/
def absTx (tx : Tx) : TxDesc Bytes :=
  { version := tx.version, inputs := tx.inputs.map fun i => ⟨i.prevHash, i.prevIndex⟩,
    outputs := tx.outputs.map outOf, lockTime := tx.lockTime }

/-- The widths `OP_NUM2BIN` gives the varints of the rebuilt grandparent, computed. -/
def w6Of (a : Args) : Bytes := (num2bin (encode ↑(List.length a.ps.p24)) 1).getD []
def w4Of (a : Args) : Bytes := (num2bin (encode ↑(List.length a.ps.p23)) 1).getD []
def w3Of (a : Args) : Bytes := (num2bin (encode ↑(List.length a.ps.p22)) 1).getD []
def w2Of (a : Args) : Bytes :=
  (num2bin (encode ↑(List.length (rebuiltScriptSig a (w3Of a) (w4Of a) (w6Of a)))) 2).getD []

/-- The grandparent transaction a settle rebuilds, computed from the pieces. -/
def rebuiltOf (f : Fields) (a : Args) : Bytes := rebuilt f a (w2Of a) (w3Of a) (w4Of a) (w6Of a)

/-- The kind of a spend: a melt presents no preimage; otherwise the spent type says which half of
the state machine runs. -/
def kindOf (f : Fields) (a : Args) : Kind :=
  if castToBool a.pre then (if f.ty = [0] then .commit else .settle) else .melt

/-- The spend of the token `f` at input `i` of `tx` with the unlocking arguments `a`, as the model
sees it. -/
def spendOf (tx : Tx) (i : Nat) (f : Fields) (a : Args) : Spend Bytes :=
  { tx := absTx tx, inputIndex := i, kind := kindOf f a, mode := .transfer, spent := tokenOf f,
    spentOutpoint := ⟨(Sighash.inputAt tx i).prevHash, (Sighash.inputAt tx i).prevIndex⟩,
    other := none, signer := a.pk, sig := a.sig, sigHashType := a.sig.getLast?.getD 0,
    recipient := a.ben, recipient2 := [], piece := 0,
    anc := if kindOf f a = .settle ∧ decode f.gp ≠ 0 then (decodeTx (rebuiltOf f a)).map absTx else none,
    ancB := none }

end BoltProof.Glue.AuthBolt
