import BoltProof.Bridge.Glue.SimpleMulti.Facts
import BoltProof.Bridge.Glue.Refine.MinSimple

/-!
# `SimpleMultiBOLT`: the residual assumptions

What the fungible refinement assumes beyond the bytes, as `Refine/MinSimple.lean` states it for the NFT family:
the lock's own `OP_PUSH_TX` block is sound (`PushTxSound`, over the fungible block), the byte strings the covenant
hashes have no second preimage, the primitives agree with this spend's cryptography, and the scope assumptions of
the plan's decisions: the change carries no token and a melt pays P2PKH only (Finding 1), and a split settle's
flags are the honest empty ones (the split-flag finding). Also here: the push-tx block is reached by the prologue
alone (`pushTxReached`), which is what lets the refinement derive the preimage before running the paths, and the
scriptCode's `fd` varint the paths assume is the real preimage's (`preimage_varint`).
-/

set_option autoImplicit false

namespace BoltProof.Glue.SimpleMulti

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget BsvScript.Tx
  BsvScript.Sighash BsvScript.TxContext
open BoltProof.Glue.Serial
open BoltProof.Glue.MinSimple (NoSecondPreimage Agrees reached_of_append)
open BoltProof.Bridge.Generated

/-- A preimage the fungible lock's `OP_PUSH_TX` block accepts, under this spend's context, hashes to this spend's
digest over the lock. -/
def PushTxSound (tx : Tx) (i amt : Nat) (lock : Bytes) : Prop :=
  ∀ (pre tail : Bytes) (X A : List Bytes) (m : Nat) (C : Cond) (kk : Nat) (r : GOut),
    C.isActive = true →
    run Eval.opExec (phase2Env (txContext tx i amt)) pushTxBlock tail (St (pre :: X) A m C kk lock) = r →
    r.IsOk → Hash.hash256 pre = sighashBIP143 lock tx i ⟨0x41⟩ amt

/-- The outputs after the first `n` carry no fungible token. -/
def HonestOutputs (tx : Tx) (n : Nat) : Prop := ∀ o ∈ tx.outputs.drop n, (outOf o).isToken = false

/-- A melt pays P2PKH only, in a version-2 transaction. -/
def HonestMelt (tx : Tx) : Prop := (∀ o ∈ tx.outputs, (outOf o).isP2pkh = true) ∧ 2 ≤ tx.version

/-- The number of outputs a spend's covenant reconstructs before the change: a transfer or merge commit's token
and proof output, a split commit's token and two proof outputs, a settle's one token, a split settle's two. -/
def expectedCount (f : Fields) (a : Args) : Nat :=
  if settledTy f.ty then (if a.nty = [0x23] then 3 else 2) else (if f.ty = [0x23] then 2 else 1)

/-- Everything assumed of a fungible spend beyond what its bytes check. -/
structure Residual (P : Prims Bytes) (tx : Tx) (i amt : Nat) (f : Fields) (a : Args) : Prop where
  pushTx : PushTxSound tx i amt (lockScript f)
  preimage : NoSecondPreimage (preimageBIP143 (lockScript f) tx i ⟨0x41⟩ amt)
  outputs : NoSecondPreimage ((tx.outputs.map serTxOut).flatten)
  prevouts : NoSecondPreimage ((tx.inputs.map serOutPoint).flatten)
  agrees : Agrees P tx i amt (lockScript f)
  honest : castToBool a.pre = true → HonestOutputs tx (expectedCount f a)
  melt : castToBool a.pre = false → HonestMelt tx
  splitFlags : castToBool a.pre = true → f.ty = [0x23] → decode a.pkh1 = 0 ∧ decode a.i2 = 0

/-- With a preimage, the run of the suffix passes the lock's own `OP_PUSH_TX` block: the prologue alone gets
there, so the preimage can be weighed before the paths are run. -/
theorem pushTxReached {env : Env} (he : EnvOK env) {k t : Bytes} {r : GOut} {f : Fields} {a : Args}
    {S A : List Bytes} {C : Cond} {cs : Bytes} {m kk : Nat} (hact : C.isActive = true)
    (hpre : castToBool a.pre = true)
    (h : run Eval.opExec env (SimpleMulti.suffix ++ k) t (St (f.stack ++ (a.stack ++ S)) A m C kk cs) = r)
    (hr : r.IsOk) : PushTxReached env a.pre cs := by
  obtain ⟨-, m', k', h⟩ := prologue he hact hpre h hr
  rw [suffix_drop_38_append, pushTxBlock_eq] at h
  obtain ⟨r', hst, hok⟩ := reached_of_append pushTxBlock_framed h hr
  exact ⟨_, _, _, _, _, _, r', by simp [hact], hst, hok⟩

/-- The real preimage carries the scriptCode's length as a `fd` varint at byte 104 when the scriptCode is
between 253 and 65535 bytes long. -/
theorem preimage_varint (lock : Bytes) (hl : 253 ≤ lock.length ∧ lock.length ≤ 0xffff) (tx : Tx) (i amt : Nat)
    (h32 : (inputAt tx i).prevHash.length = 32) :
    List.take 1 (List.drop 104 (preimageBIP143 lock tx i ⟨0x41⟩ amt)) = [0xfd] := by
  have hcs : compactSize lock.length = 253 :: [lock.length % 256, lock.length / 256 % 256] := by
    simp only [compactSize, Nat.not_lt.mpr hl.1, ↓reduceIte, hl.2]
  have h36 : (serOutPoint (inputAt tx i)).length = 36 := by rw [serOutPoint_length, h32]
  have hpre : preimageBIP143 lock tx i ⟨0x41⟩ amt = serVersion tx.version ++ (hashPrevouts tx ++
      (bip143Sequence tx ⟨0x41⟩ ++ (serOutPoint (inputAt tx i) ++ (compactSize lock.length ++ (lock ++
      (le64 amt ++ (le32 (inputAt tx i).sequence ++ (hashOutputs tx ++ (le32 tx.lockTime ++
      SigHashType.serialize ⟨0x41⟩))))))))) := by
    simp only [preimageBIP143, serScript, Serial.bip143Prevouts_all, Serial.bip143Outputs_all, List.append_assoc]
  rw [hpre, show (104 : Nat) = 4 + (32 + (32 + 36)) from rfl, ← List.drop_drop,
    List.drop_left' (serVersion_length _), ← List.drop_drop, List.drop_left' (hashPrevouts_length _),
    ← List.drop_drop, List.drop_left' (bip143Sequence_length _ _), List.drop_left' h36, hcs]
  rfl

end BoltProof.Glue.SimpleMulti
