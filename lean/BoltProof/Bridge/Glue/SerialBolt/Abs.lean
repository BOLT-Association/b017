import BoltProof.Bridge.Glue.SerialBolt.Spec
import BoltProof.Model.Covenant
import BsvScript.Tx

/-!
# The `SerialBOLT` lock and its abstraction into the model

The locking script is the eight field pushes followed by the suffix (`lockOf`): the 36-byte
`genesisOutpoint`, the `mintData` in the push its length selects (`mintPush`: `OP_0`, a direct push, or
`OP_PUSHDATA1`), then `MinSimpleBOLT`'s six pushes (`pushesOf`). `WF` is the widths the pushes carry,
`decodeLock` reads the fields back (and accepts only a lock `lockOf` writes), and `lock_pushes` runs the
pushes symbolically so a run of the whole lock is a run of the suffix from `Fields.stack`
(`SerialBolt/Spec.lean`).

The second half abstracts a real spend into the model's vocabulary (`Model/Spend.lean`) as for
`AuthBOLT`: a lock's fields become a `Token` (`tokenOf`; the model's token has no `genesisOutpoint` or
`mintData`, which the bytes carry alongside), an output becomes an `Out` by its script (`outOf`), a
transaction becomes a `TxDesc` (`absTx`), and the spend of a token at input `i` with the unlocking arguments
`a` becomes a `Spend` (`spendOf`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace BoltProof.Glue.SerialBolt

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget BsvScript.Tx
open BoltProof.Bridge.Generated

/-! ## Two push inversions of any width -/

/-- A direct push of `n` bytes, `1 ≤ n ≤ 75`: the next `n` bytes of the program pushed. -/
theorem inv_push_n {env : Env} {g t : Bytes} {r : GOut} {S A : List Bytes} {C : Cond} {cs : Bytes} {m k n : Nat}
    (hn : 1 ≤ n ∧ n ≤ 75) (he : EnvOK env) (hact : C.isActive = true)
    (h : run Eval.opExec env (n :: g) t (St S A m C k cs) = r) (hr : r.IsOk) :
    n ≤ g.length ∧ ∃ m' k', run Eval.opExec env (g.drop n) t (St (g.take n :: S) A m' C k' cs) = r := by
  obtain ⟨hgen, hera, hmin, hminif, hfork, hcs⟩ := he
  have hp : n ≤ Op.OP_PUSHDATA4 := by simp only [Op.OP_PUSHDATA4]; omega
  have hdis : isOpcodeDisabled n env.utxoEra = false := by simp [isOpcodeDisabled, hera]
  rw [run.eq_2, getOpTail_push hn] at h
  by_cases hlen : g.length < n
  · simp only [hlen, ↓reduceIte] at h; subst h; simp at hr
  simp only [hlen, ↓reduceIte, hgen, Bool.not_true, Bool.false_and, hdis, Bool.false_or, hact, Bool.true_and] at h
  refine ⟨by omega, ?_⟩
  split_ifs at h
  all_goals (try (subst h; simp at hr; done))
  all_goals (simp only [execStep, Bool.true_and, decide_eq_true hp, hmin, Bool.false_and, pushElem] at h)
  all_goals (split_ifs at h <;> (try (subst h; simp at hr; done)))
  all_goals first
    | (subst h; simp at hr; done)
    | (exfalso; simp_all [Op.OP_RETURN, Op.OP_PUSHDATA4]; done)
    | (simp only at h; exact ⟨_, _, h⟩)

theorem getOpTail_pushdata1 (b : Nat) (g : Bytes) :
    getOpTail 76 (b :: g) = if g.length < b then none else some (g.take b, 1 + b) := by
  simp [getOpTail, Op.OP_PUSHDATA4, Op.OP_PUSHDATA1]

/-- `OP_PUSHDATA1 b`: the next `b` bytes of the program pushed. -/
theorem inv_pushdata1 {env : Env} {g t : Bytes} {r : GOut} {S A : List Bytes} {C : Cond} {cs : Bytes} {m k b : Nat}
    (he : EnvOK env) (hact : C.isActive = true)
    (h : run Eval.opExec env (76 :: b :: g) t (St S A m C k cs) = r) (hr : r.IsOk) :
    b ≤ g.length ∧ ∃ m' k', run Eval.opExec env (g.drop b) t (St (g.take b :: S) A m' C k' cs) = r := by
  obtain ⟨hgen, hera, hmin, hminif, hfork, hcs⟩ := he
  have hp : 76 ≤ Op.OP_PUSHDATA4 := by simp only [Op.OP_PUSHDATA4]; omega
  have hdis : isOpcodeDisabled 76 env.utxoEra = false := by simp [isOpcodeDisabled, hera]
  rw [run.eq_2, getOpTail_pushdata1] at h
  by_cases hlen : g.length < b
  · simp only [hlen, ↓reduceIte] at h; subst h; simp at hr
  simp only [hlen, ↓reduceIte, hgen, Bool.not_true, Bool.false_and, hdis, Bool.false_or, hact, Bool.true_and] at h
  refine ⟨by omega, ?_⟩
  rw [show List.drop (1 + b) (b :: g) = List.drop b g by rw [Nat.add_comm]; rfl] at h
  split_ifs at h
  all_goals (try (subst h; simp at hr; done))
  all_goals (simp only [execStep, Bool.true_and, decide_eq_true hp, ↓reduceIte, hmin, Bool.false_and, pushElem] at h)
  all_goals (split_ifs at h <;> (try (subst h; simp at hr; done)))
  all_goals first
    | (subst h; simp at hr; done)
    | (exfalso; simp_all [Op.OP_RETURN, Op.OP_PUSHDATA4, Op.OP_16]; done)
    | (simp only at h; exact ⟨_, _, h⟩)

/-! ## The lock -/

/-- Well-formed lock fields: the widths the eight pushes carry (`mintData` at most 255 bytes, the bound the
prologue checks). -/
structure WF (f : Fields) : Prop where
  genesis : f.genesis.length = 36
  mint : f.mint.length ≤ 255
  pkh : f.pkh.length = 20
  com : f.com.length = 20
  ty : f.ty.length = 1
  parent : f.parent.length = 36
  gp : f.gp.length = 36
  issuer : f.issuer.length = 33

/-- The `mintData` push: `OP_0` when empty, a direct push up to 75 bytes, `OP_PUSHDATA1` beyond. -/
def mintPush (m : Bytes) : Bytes :=
  if m = [] then [0] else if m.length ≤ 75 then m.length :: m else 76 :: m.length :: m

/-- The six pushes after `mintData` (`pkh`, `com`, `ty`, `parent`, `gp`, `issuer`) and the suffix. -/
def pushesOf (f : Fields) : Bytes :=
  20 :: (f.pkh ++ 20 :: (f.com ++ 1 :: (f.ty ++ 36 :: (f.parent ++ 36 :: (f.gp ++ 33 :: (f.issuer ++
    SerialBolt.suffix))))))

/-- The locking script: the `genesisOutpoint` push, the `mintData` push, the six pushes and the suffix. -/
def lockOf (f : Fields) : Bytes := 36 :: (f.genesis ++ (mintPush f.mint ++ pushesOf f))

/-- The `mintData` push is `mintW` bytes wide. -/
theorem mintPush_length {f : Fields} (h : f.mint.length ≤ 255) : (mintPush f.mint).length = mintW f := by
  unfold mintPush mintW
  by_cases h0 : f.mint = []
  · rw [h0]; simp
  · by_cases h75 : f.mint.length ≤ 75
    · have h75' : ((f.mint.length : Nat) : Int) ≤ 75 := by exact_mod_cast h75
      simp only [h0, h75, h75', ↓reduceIte, List.length_cons]; omega
    · have h75' : ¬ ((f.mint.length : Nat) : Int) ≤ 75 := by exact_mod_cast h75
      simp only [h0, h75, h75', ↓reduceIte, List.length_cons]; omega

theorem pushesOf_length {f : Fields} (hwf : WF f) : (pushesOf f).length = 152 + SerialBolt.suffix.length := by
  simp [pushesOf, hwf.pkh, hwf.com, hwf.ty, hwf.parent, hwf.gp, hwf.issuer]; omega

theorem lockOf_length {f : Fields} (hwf : WF f) :
    (lockOf f).length = 37 + mintW f + 152 + SerialBolt.suffix.length := by
  simp only [lockOf, List.length_cons, List.length_append, hwf.genesis, mintPush_length hwf.mint,
    pushesOf_length hwf]
  omega

/-- The lock after its first two pushes is the six pushes and the suffix. -/
theorem lockOf_drop {f : Fields} (hwf : WF f) : (lockOf f).drop (37 + mintW f) = pushesOf f := by
  have h : lockOf f = (36 :: f.genesis ++ mintPush f.mint) ++ pushesOf f := by simp [lockOf]
  rw [h, show 37 + mintW f = (36 :: f.genesis ++ mintPush f.mint).length by
    simp [hwf.genesis, mintPush_length hwf.mint]; omega, List.drop_left]

/-- The eight pushes put the fields on the stack, `issuer` on top: a run of the lock is a run of the
suffix from `Fields.stack`. -/
theorem lock_pushes {env : Env} (he : EnvOK env) {t : Bytes} {r : GOut} {f : Fields} {S A : List Bytes}
    {C : Cond} {cs : Bytes} {m kk : Nat} (hact : C.isActive = true) (hwf : WF f)
    (h : run Eval.opExec env (lockOf f) t (St S A m C kk cs) = r) (hr : r.IsOk) :
    ∃ m' k', run Eval.opExec env SerialBolt.suffix t (St (f.stack ++ S) A m' C k' cs) = r := by
  unfold lockOf at h
  obtain ⟨-, _, _, h⟩ := inv_push_36 he hact h hr
  rw [List.take_left' hwf.genesis, List.drop_left' hwf.genesis] at h
  have hm : ∃ m' k', run Eval.opExec env (pushesOf f) t (St (f.mint :: f.genesis :: S) A m' C k' cs) = r := by
    unfold mintPush at h
    split_ifs at h with h0 h75
    · rw [h0]
      simp only [List.cons_append, List.nil_append] at h
      obtain ⟨_, _, h⟩ := inv_push0 he hact h hr
      exact ⟨_, _, h⟩
    · have hn : 1 ≤ f.mint.length ∧ f.mint.length ≤ 75 := ⟨List.length_pos_iff.mpr h0, h75⟩
      simp only [List.cons_append] at h
      obtain ⟨-, _, _, h⟩ := inv_push_n hn he hact h hr
      rw [List.take_left' rfl, List.drop_left' rfl] at h
      exact ⟨_, _, h⟩
    · simp only [List.cons_append] at h
      obtain ⟨-, _, _, h⟩ := inv_pushdata1 he hact h hr
      rw [List.take_left' rfl, List.drop_left' rfl] at h
      exact ⟨_, _, h⟩
  obtain ⟨_, _, h⟩ := hm
  unfold pushesOf at h
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

/-! The six pushes' layout: what sits after each push, for the decoder and for the welds. -/

theorem pushesOf_drop_1 (f : Fields) : (pushesOf f).drop 1 =
    f.pkh ++ 20 :: (f.com ++ 1 :: (f.ty ++ 36 :: (f.parent ++ 36 :: (f.gp ++ 33 :: (f.issuer ++ SerialBolt.suffix))))) :=
  rfl
theorem pushesOf_drop_21 {f : Fields} (hwf : WF f) : (pushesOf f).drop 21 =
    20 :: (f.com ++ 1 :: (f.ty ++ 36 :: (f.parent ++ 36 :: (f.gp ++ 33 :: (f.issuer ++ SerialBolt.suffix))))) := by
  rw [show (21 : Nat) = 1 + 20 from rfl, ← List.drop_drop, pushesOf_drop_1, List.drop_left' hwf.pkh]
theorem pushesOf_drop_22 {f : Fields} (hwf : WF f) : (pushesOf f).drop 22 =
    f.com ++ 1 :: (f.ty ++ 36 :: (f.parent ++ 36 :: (f.gp ++ 33 :: (f.issuer ++ SerialBolt.suffix)))) := by
  rw [show (22 : Nat) = 21 + 1 from rfl, ← List.drop_drop, pushesOf_drop_21 hwf]; rfl
theorem pushesOf_drop_42 {f : Fields} (hwf : WF f) : (pushesOf f).drop 42 =
    1 :: (f.ty ++ 36 :: (f.parent ++ 36 :: (f.gp ++ 33 :: (f.issuer ++ SerialBolt.suffix)))) := by
  rw [show (42 : Nat) = 22 + 20 from rfl, ← List.drop_drop, pushesOf_drop_22 hwf, List.drop_left' hwf.com]
theorem pushesOf_drop_43 {f : Fields} (hwf : WF f) : (pushesOf f).drop 43 =
    f.ty ++ 36 :: (f.parent ++ 36 :: (f.gp ++ 33 :: (f.issuer ++ SerialBolt.suffix))) := by
  rw [show (43 : Nat) = 42 + 1 from rfl, ← List.drop_drop, pushesOf_drop_42 hwf]; rfl
theorem pushesOf_drop_44 {f : Fields} (hwf : WF f) : (pushesOf f).drop 44 =
    36 :: (f.parent ++ 36 :: (f.gp ++ 33 :: (f.issuer ++ SerialBolt.suffix))) := by
  rw [show (44 : Nat) = 43 + 1 from rfl, ← List.drop_drop, pushesOf_drop_43 hwf, List.drop_left' hwf.ty]
theorem pushesOf_drop_45 {f : Fields} (hwf : WF f) : (pushesOf f).drop 45 =
    f.parent ++ 36 :: (f.gp ++ 33 :: (f.issuer ++ SerialBolt.suffix)) := by
  rw [show (45 : Nat) = 44 + 1 from rfl, ← List.drop_drop, pushesOf_drop_44 hwf]; rfl
theorem pushesOf_drop_81 {f : Fields} (hwf : WF f) : (pushesOf f).drop 81 =
    36 :: (f.gp ++ 33 :: (f.issuer ++ SerialBolt.suffix)) := by
  rw [show (81 : Nat) = 45 + 36 from rfl, ← List.drop_drop, pushesOf_drop_45 hwf, List.drop_left' hwf.parent]
theorem pushesOf_drop_82 {f : Fields} (hwf : WF f) : (pushesOf f).drop 82 =
    f.gp ++ 33 :: (f.issuer ++ SerialBolt.suffix) := by
  rw [show (82 : Nat) = 81 + 1 from rfl, ← List.drop_drop, pushesOf_drop_81 hwf]; rfl
theorem pushesOf_drop_118 {f : Fields} (hwf : WF f) : (pushesOf f).drop 118 = 33 :: (f.issuer ++ SerialBolt.suffix) := by
  rw [show (118 : Nat) = 82 + 36 from rfl, ← List.drop_drop, pushesOf_drop_82 hwf, List.drop_left' hwf.gp]
theorem pushesOf_drop_119 {f : Fields} (hwf : WF f) : (pushesOf f).drop 119 = f.issuer ++ SerialBolt.suffix := by
  rw [show (119 : Nat) = 118 + 1 from rfl, ← List.drop_drop, pushesOf_drop_118 hwf]; rfl
theorem pushesOf_drop_152 {f : Fields} (hwf : WF f) : (pushesOf f).drop 152 = SerialBolt.suffix := by
  rw [show (152 : Nat) = 119 + 33 from rfl, ← List.drop_drop, pushesOf_drop_119 hwf, List.drop_left' hwf.issuer]

/-- The `mintData` and the width of its push, read off a lock at byte 37. -/
def mintAt (s : Bytes) : Bytes × Nat :=
  let op := (s.drop 37).headD 0
  if op = 0 then ([], 1)
  else if op = 76 then ((s.drop 39).take ((s.drop 38).headD 0), (s.drop 38).headD 0 + 2)
  else ((s.drop 38).take op, op + 1)

/-- The fields at the places `lockOf` writes them. -/
def parseLock (s : Bytes) : Fields :=
  let ps := s.drop (37 + (mintAt s).2)
  { genesis := (s.drop 1).take 36, mint := (mintAt s).1, pkh := (ps.drop 1).take 20, com := (ps.drop 22).take 20,
    ty := (ps.drop 43).take 1, parent := (ps.drop 45).take 36, gp := (ps.drop 82).take 36,
    issuer := (ps.drop 119).take 33 }

/-- The fields read back off a locking script: the script must be the lock of the fields read, with the
widths `WF` asks. -/
def decodeLock (s : Bytes) : Option Fields :=
  let f := parseLock s
  if f.genesis.length = 36 ∧ f.mint.length ≤ 255 ∧ f.pkh.length = 20 ∧ f.com.length = 20 ∧ f.ty.length = 1 ∧
      f.parent.length = 36 ∧ f.gp.length = 36 ∧ f.issuer.length = 33 ∧ lockOf f = s then some f
  else none

theorem mintAt_lockOf {f : Fields} (hwf : WF f) : mintAt (lockOf f) = (f.mint, mintW f) := by
  have h37 : (lockOf f).drop 37 = mintPush f.mint ++ pushesOf f := by
    have h : lockOf f = (36 :: f.genesis) ++ (mintPush f.mint ++ pushesOf f) := rfl
    rw [h, show (37 : Nat) = (36 :: f.genesis).length by simp [hwf.genesis], List.drop_left]
  have h38 : (lockOf f).drop 38 = (mintPush f.mint ++ pushesOf f).drop 1 := by
    rw [show (38 : Nat) = 37 + 1 from rfl, ← List.drop_drop, h37]
  have h39 : (lockOf f).drop 39 = (mintPush f.mint ++ pushesOf f).drop 2 := by
    rw [show (39 : Nat) = 37 + 2 from rfl, ← List.drop_drop, h37]
  rw [← mintPush_length hwf.mint]
  unfold mintAt
  simp only [h37, h38, h39]
  unfold mintPush
  by_cases h0 : f.mint = []
  · simp [h0]
  · have hl : 1 ≤ f.mint.length := List.length_pos_iff.mpr h0
    by_cases h75 : f.mint.length ≤ 75
    · have h76 : f.mint.length ≠ 76 := by omega
      have h00 : f.mint.length ≠ 0 := by omega
      simp [h0, h75, h76, h00, List.take_left']
    · simp [h0, h75, List.take_left']

theorem parseLock_lockOf {f : Fields} (hwf : WF f) : parseLock (lockOf f) = f := by
  unfold parseLock
  simp only [mintAt_lockOf hwf, lockOf_drop hwf, pushesOf_drop_1, pushesOf_drop_22 hwf, pushesOf_drop_43 hwf,
    pushesOf_drop_45 hwf, pushesOf_drop_82 hwf, pushesOf_drop_119 hwf, List.take_left' hwf.pkh,
    List.take_left' hwf.com, List.take_left' hwf.ty, List.take_left' hwf.parent, List.take_left' hwf.gp,
    List.take_left' hwf.issuer]
  rw [show List.drop 1 (lockOf f) = f.genesis ++ (mintPush f.mint ++ pushesOf f) from rfl, List.take_left' hwf.genesis]

/-- A well-formed lock decodes to its fields. -/
theorem decodeLock_lockOf {f : Fields} (hwf : WF f) : decodeLock (lockOf f) = some f := by
  simp [decodeLock, parseLock_lockOf hwf, hwf.genesis, hwf.mint, hwf.pkh, hwf.com, hwf.ty, hwf.parent, hwf.gp,
    hwf.issuer]

/-- A script that decodes is the lock of what it decodes to. -/
theorem eq_lockOf_of_decodeLock {s : Bytes} {f : Fields} (h : decodeLock s = some f) : WF f ∧ s = lockOf f := by
  simp only [decodeLock] at h
  split_ifs at h with hc
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hc
  cases h
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, h9.symm⟩

/-! ## The abstraction into the model -/

/-- The 36-byte outpoint field as the model's optional outpoint (`AuthBOLT`'s reading). -/
def outpointOf (b : Bytes) : Option (Outpoint Bytes) :=
  if decode b = 0 then none else some ⟨b.take 32, leNat (b.drop 32)⟩

/-- The token a lock's fields describe. The NFT family carries no balance, no second commitment and
no other grandparent; the model's token has no `genesisOutpoint` or `mintData`. -/
def tokenOf (f : Fields) : Token Bytes :=
  { owner := f.pkh, commitment := f.com, commitment2 := [], txoType := f.ty.headD 0,
    parent := outpointOf f.parent, grandparent := outpointOf f.gp, otherGrandparent := none,
    issuer := f.issuer, balance := 0, balanceCommit := 0 }

/-- The pay-to-proof script a commit emits: `02 b017 OP_EQUALVERIFY OP_DUP OP_HASH160 <pkh>
OP_EQUALVERIFY OP_CHECKSIG`. -/
def proofScript (pkh : Bytes) : Bytes := [2, 0xb0, 0x17, 0x88, 0x76, 0xa9, 0x14] ++ pkh ++ [0x88, 0xac]

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

/-- The widths `OP_NUM2BIN` gives the pushes and varints of the rebuilt grandparent, computed. -/
def w12Of (a : Args) : Bytes := (num2bin (encode ((List.length a.ps.p24 : Nat) : Int)) 1).getD []
def w11Of (a : Args) : Bytes := (num2bin (encode ((List.length a.ps.p23 : Nat) : Int)) 1).getD []
def w6Of (a : Args) : Bytes :=
  (num2bin (encode ((List.length a.ps.p18 : Nat) : Int)) (mintLenWidth ((List.length a.ps.p18 : Nat) : Int))).getD []
def w5Of (f : Fields) (a : Args) : Bytes :=
  (num2bin (encode (((List.length (gpScriptCode f a (w6Of a)) : Nat) : Int) + 2)) 2).getD []
def w4Of (f : Fields) (a : Args) : Bytes :=
  (num2bin (encode ((List.length (gpScriptCode f a (w6Of a)) : Nat) : Int)) 2).getD []
def w2Of (f : Fields) (a : Args) : Bytes :=
  (num2bin (encode ((List.length (rebuiltScriptSig f a (w4Of f a) (w4Of f a) (w5Of f a) (w6Of a) (w11Of a)
    (w12Of a)) : Nat) : Int)) 2).getD []

/-- The grandparent transaction a settle rebuilds, computed from the pieces. -/
def rebuiltOf (f : Fields) (a : Args) : Bytes :=
  rebuilt f a (w2Of f a) (w4Of f a) (w4Of f a) (w5Of f a) (w6Of a) (w11Of a) (w12Of a)

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

end BoltProof.Glue.SerialBolt
