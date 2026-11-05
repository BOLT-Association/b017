import BoltProof.Bridge.Glue.MinSimple.Sound
import BoltProof.Bridge.Glue.Refine.Verify
import BoltProof.Bridge.Glue.Refine.Facts
import BoltProof.Bridge.Glue.Refine.Weld

/-!
# `MinSimpleBOLT`: the bytes refine `Accepts`

**The refinement theorem** (`lean/GLUE-PLAN.md`, M4, route B): a spend the shipped
`MinSimpleBOLT` lock accepts under the post-Chronicle consensus rules is a spend the covenant
interface `Accepts` (`Model/Covenant.lean`) accepts, for the NFT family, once the spend is read
into the model's vocabulary (`spendOf`, `MinSimple/Abs.lean`). Everything Layer 1 proves of
`Accepts` therefore holds of what the bytes let through.

What is assumed beyond the bytes is stated once, in `Residual`:

* `PushTxSound`: a preimage the lock's own `OP_PUSH_TX` block accepts hashes to this spend's
  `SIGHASH_ALL | FORKID` digest (the ECDSA algebra of the fixed-key signature the block
  assembles, with the negligible root cases excluded);
* `NoSecondPreimage` of the four byte strings the covenant hashes: the real preimage, the
  serialised outputs, the serialised outpoints, the real grandparent transaction (A1, stated on the
  spend's own data rather than as a global injectivity, which no hash has);
* `GpReal`: the grandparent txid the token names is a well-formed transaction's, with its token
  output at the named index and a proof output at index 1, whose abstract id the primitives agree
  on (what the accepted commit two steps back guarantees; the run-level argument discharges it);
* `Agrees`: the primitives compute `hash160` and this spend's `OP_CHECKSIG`;
* `HonestOutputs`/`HonestMelt`: the change outputs carry no token, and a melt pays P2PKH only and
  has version 2 (Finding 1 of the plan: the bytes do not enforce these clauses).

`ArgsWF` is the width of the recipient hash and the signing key, which the bytes copy into the
new token's pushes unchecked (a melt reads neither, so it is asked only of a spend with a preimage);
`TxWF` is the serialisation round trip's well-formedness.
-/

set_option autoImplicit false

namespace BoltProof.Glue.MinSimple

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget BsvScript.Tx
  BsvScript.Sighash BsvScript.TxContext
open BoltProof.Glue.Serial
open BoltProof.Bridge (params)
open BoltProof.Bridge.Generated

/-! ## The residual assumptions -/

/-- A preimage the lock's `OP_PUSH_TX` block accepts, under this spend's context, hashes to this
spend's digest over the lock. -/
def PushTxSound (tx : Tx) (i amt : Nat) (lock : Bytes) : Prop :=
  ∀ (pre tail : Bytes) (X A : List Bytes) (m : Nat) (C : Cond) (kk : Nat) (r : GOut),
    C.isActive = true →
    run Eval.opExec (phase2Env (txContext tx i amt)) pushTxBlock tail (St (pre :: X) A m C kk lock) = r →
    r.IsOk → Hash.hash256 pre = sighashBIP143 lock tx i ⟨0x41⟩ amt

/-- Nothing else hashes to what `x` hashes to. -/
def NoSecondPreimage (x : Bytes) : Prop := ∀ y, Hash.hash256 y = Hash.hash256 x → y = x

/-- The grandparent is real. -/
def GpReal (P : Prims Bytes) (f : Fields) : Prop :=
  decode f.gp ≠ 0 → ∃ G : Tx, TxWF G ∧ Sighash.txid G = List.take 32 f.gp ∧ NoSecondPreimage (serTx G) ∧
    P.txid (absTx G) = Sighash.txid G ∧
    (∃ t, (absTx G).outputs[leNat (List.drop 32 f.gp)]? = some (.token t)) ∧
    ∃ pkh, (absTx G).outputs[1]? = some (.proof pkh)

/-- The primitives agree with this spend's cryptography. -/
structure Agrees (P : Prims Bytes) (tx : Tx) (i amt : Nat) (lock : Bytes) : Prop where
  h160 : ∀ pk, P.h160 pk = Hash.hash160 pk
  verify : ∀ pk sig, P.verify pk (P.sighash (absTx tx) i) sig = Ops.Crypto.txCheckSig tx i amt sig pk lock true

/-- The outputs after the first `n` carry no token. -/
def HonestOutputs (tx : Tx) (n : Nat) : Prop := ∀ o ∈ tx.outputs.drop n, (outOf o).isToken = false

/-- A melt pays P2PKH only, in a version-2 transaction. -/
def HonestMelt (tx : Tx) : Prop := (∀ o ∈ tx.outputs, (outOf o).isP2pkh = true) ∧ 2 ≤ tx.version

/-- Everything assumed of a spend beyond what its bytes check. -/
structure Residual (P : Prims Bytes) (tx : Tx) (i amt : Nat) (f : Fields) (a : Args) : Prop where
  pushTx : PushTxSound tx i amt (lockOf f)
  preimage : NoSecondPreimage (preimageBIP143 (lockOf f) tx i ⟨0x41⟩ amt)
  outputs : NoSecondPreimage ((tx.outputs.map serTxOut).flatten)
  prevouts : NoSecondPreimage ((tx.inputs.map serOutPoint).flatten)
  gp : GpReal P f
  agrees : Agrees P tx i amt (lockOf f)
  honest : castToBool a.pre = true → HonestOutputs tx (if f.ty = [0] then 2 else 1)
  melt : castToBool a.pre = false → HonestMelt tx

/-! ## The welds, per path -/

/-- A commit's outputs are the model's expected outputs followed by non-token change. -/
theorem outs_commit {tx : Tx} {i amt : Nat} {f : Fields} {a : Args} (hwf : WF f) (ha : ArgsWF a) (htx : TxWF tx)
    (hamt : amt < 2 ^ 64) (hty : f.ty = [0]) (hpre : castToBool a.pre = true)
    (h32 : (inputAt tx i).prevHash.length = 32) (hidx : (inputAt tx i).prevIndex < 2 ^ 32)
    (hnz : decode (serOutPoint (inputAt tx i)) ≠ 0) (hiss : decode f.parent = 0 → f.issuer = a.pk)
    (hval : preValue a.pre = le64 amt) (hout : preOutpoint a.pre = serOutPoint (inputAt tx i))
    (hsc : sc a.pre = lockOf f)
    (hflat : expectedOuts f a ++ a.chg = (tx.outputs.map serTxOut).flatten) (hhon : HonestOutputs tx 2) :
    ∃ change : List (Out Bytes), (∀ o ∈ change, o.isToken = false) ∧
      (absTx tx).outputs = (spendOf tx i f a).expectedOuts .nft ++ change := by
  have hcwf := commitFields_wf hwf ha h32 (a := a)
  rw [expectedOuts, ite_eq_left hty, commitOuts_eq hwf ha h32 hval hout hsc, List.append_assoc] at hflat
  obtain ⟨os1, hos1, hf1⟩ := flatten_serTxOut_cons htx.outputs
    ⟨hamt, by rw [lockOf_length_eq hcwf]; decide⟩ hflat.symm
  obtain ⟨os2, hos2, hf2⟩ := flatten_serTxOut_cons
    (fun o ho => htx.outputs o (by rw [hos1]; exact List.mem_cons_of_mem _ ho))
    ⟨hamt, by simp [proofScript, ha.ben]⟩ hf1
  refine ⟨os2.map outOf, ?_, ?_⟩
  · intro o ho
    obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
    exact hhon o' (by rw [hos1, hos2]; simpa using ho')
  · have hk : (spendOf tx i f a).kind = .commit := kindOf_commit.mpr ⟨hpre, hty⟩
    simp only [absTx, hos1, hos2, List.map_cons, Spend.expectedOuts, hk, outOf_lock hcwf, outOf_proof ha.ben,
      tokenOf_commitFields tx i hiss hnz h32 hidx]
    simp [spendOf]

/-- A settle's outputs are the model's expected output followed by non-token change. -/
theorem outs_settle {tx : Tx} {i amt : Nat} {f : Fields} {a : Args} (hwf : WF f) (ha : ArgsWF a) (htx : TxWF tx)
    (hamt : amt < 2 ^ 64) (hty : f.ty = [0x21]) (hpre : castToBool a.pre = true)
    (h32 : (inputAt tx i).prevHash.length = 32) (hidx : (inputAt tx i).prevIndex < 2 ^ 32)
    (hnz : decode (serOutPoint (inputAt tx i)) ≠ 0) (hiss : decode f.parent = 0 → f.issuer = a.pk)
    (hval : preValue a.pre = le64 amt) (hout : preOutpoint a.pre = serOutPoint (inputAt tx i))
    (hsc : sc a.pre = lockOf f)
    (hflat : expectedOuts f a ++ a.chg = (tx.outputs.map serTxOut).flatten) (hhon : HonestOutputs tx 1) :
    ∃ change : List (Out Bytes), (∀ o ∈ change, o.isToken = false) ∧
      (absTx tx).outputs = (spendOf tx i f a).expectedOuts .nft ++ change := by
  have hswf := settleFields_wf hwf ha h32 (a := a)
  rw [expectedOuts, ite_eq_right (settle_ne_commit hty), settleOuts_eq hwf ha h32 hval hout hsc] at hflat
  obtain ⟨os1, hos1, hf1⟩ := flatten_serTxOut_cons htx.outputs
    ⟨hamt, by rw [lockOf_length_eq hswf]; decide⟩ hflat.symm
  refine ⟨os1.map outOf, ?_, ?_⟩
  · intro o ho
    obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
    exact hhon o' (by rw [hos1]; simpa using ho')
  · have hk : (spendOf tx i f a).kind = .settle := kindOf_settle.mpr ⟨hpre, settle_ne_commit hty⟩
    simp only [absTx, hos1, List.map_cons, Spend.expectedOuts, hk, outOf_lock hswf,
      tokenOf_settleFields tx i hty hiss hnz h32 hidx]
    simp [spendOf, tokenOf, hty, Fam.modeOfCommitType]

/-- A settle with a grandparent supplies the real grandparent and co-spends its proof output. -/
theorem rebuild_facts {P : Prims Bytes} {tx : Tx} {i : Nat} {f : Fields} {a : Args} {env : Env} {cs : Bytes}
    (htx : TxWF tx) (hty : f.ty = [0x21]) (hpre : castToBool a.pre = true)
    (h32 : (inputAt tx i).prevHash.length = 32)
    (hout : preOutpoint a.pre = serOutPoint (inputAt tx i)) (hprev : preHashPrevouts a.pre = hashPrevouts tx)
    (henf : Enforced env f a cs) (hgpreal : GpReal P f)
    (hnsp : NoSecondPreimage ((tx.inputs.map serOutPoint).flatten)) :
    ∀ gp, outpointOf f.gp = some gp →
      ∃ (A : TxDesc Bytes) (t : Token Bytes), (spendOf tx i f a).anc = some A ∧ P.txid A = gp.txid ∧
        A.outputs[gp.vout]? = some (.token t) ∧
        ∃ j pkh, A.outputs[j]? = some (.proof pkh) ∧ (⟨gp.txid, j⟩ : Outpoint Bytes) ∈ (absTx tx).inputs := by
  intro gp hgp
  have hgp0 : decode f.gp ≠ 0 := by
    intro h; simp [outpointOf, h] at hgp
  have hgpeq : gp = ⟨List.take 32 f.gp, leNat (List.drop 32 f.gp)⟩ := by
    simp [outpointOf, hgp0] at hgp; exact hgp.symm
  obtain ⟨w2, w3, w4, hw4, hw3, hw2, hhash, hprevs⟩ := henf.rebuild hty hgp0
  obtain ⟨G, hG, htxid, hGnsp, hPtxid, ⟨t, htok⟩, ⟨pkh, hproof⟩⟩ := hgpreal hgp0
  -- the rebuilt bytes are the grandparent's serialisation
  have hser : rebuilt f a w2 w3 w4 = serTx G := hGnsp _ (by rw [hhash, ← htxid]; rfl)
  have hw4' : w4Of a = w4 := by unfold w4Of; rw [hw4]; rfl
  have hw3' : w3Of a = w3 := by unfold w3Of; rw [hw3]; rfl
  have hw2' : w2Of a = w2 := by unfold w2Of; rw [hw3', hw4', hw2]; rfl
  have hreb : rebuiltOf f a = serTx G := by unfold rebuiltOf; rw [hw2', hw3', hw4', hser]
  have hk : kindOf f a = .settle := kindOf_settle.mpr ⟨hpre, settle_ne_commit hty⟩
  have hanc : (spendOf tx i f a).anc = some (absTx G) := by
    simp [spendOf, hk, hgp0, hreb, decodeTx_serTx G hG]
  -- the proof output of the grandparent is co-spent at index 1
  have hflat : serOutPoint (inputAt tx i) ++ ((Hash.hash256 (rebuilt f a w2 w3 w4) ++ [1, 0, 0, 0]) ++ a.fund) =
      (tx.inputs.map serOutPoint).flatten := by
    rw [← List.append_assoc, ← hout]
    exact hnsp _ (by rw [hprevs, hprev]; rfl)
  obtain ⟨i0, is1, his1, -, hf1⟩ := flatten_serOutPoint_cons
    (fun j hj => (htx.inputs j hj).1) (by rw [serOutPoint_length, h32]) hflat.symm
  obtain ⟨i1, is2, his2, hi1, -⟩ := flatten_serOutPoint_cons
    (fun j hj => (htx.inputs j (by rw [his1]; exact List.mem_cons_of_mem _ hj)).1)
    (by simp [hash256_length]) hf1
  have hi1mem : i1 ∈ tx.inputs := by rw [his1, his2]; simp
  have h32' : i1.prevHash.length = 32 := (htx.inputs i1 hi1mem).1
  have hidx1 : i1.prevIndex < 2 ^ 32 := (htx.inputs i1 hi1mem).2.1
  have hsplit := List.append_inj (by simpa [serOutPoint] using hi1 : i1.prevHash ++ le32 i1.prevIndex =
    Hash.hash256 (rebuilt f a w2 w3 w4) ++ [1, 0, 0, 0]) (by rw [h32', hash256_length])
  have hprev1 : i1.prevHash = List.take 32 f.gp := by rw [hsplit.1, hhash]
  have hidx1' : i1.prevIndex = 1 := by
    have := congrArg leNat hsplit.2
    rw [leNat_le32 _ hidx1] at this
    simpa [leNat] using this
  refine ⟨absTx G, t, hanc, ?_, ?_, 1, pkh, hproof, ?_⟩
  · rw [hPtxid, htxid, hgpeq]
  · rw [hgpeq]; exact htok
  · rw [hgpeq]
    simp only [absTx, List.mem_map]
    exact ⟨i1, hi1mem, by rw [hprev1, hidx1']⟩

/-! ## The theorem -/

/-- **`MinSimpleBOLT` refines `Accepts`.** A spend of the token `f` at input `i` of `tx`, worth
`amt`, that the consensus rules judge valid, with the unlocking arguments `a` on the stack, is a
spend `Accepts` admits for the NFT family, under the residual assumptions. -/
theorem minSimple_refines (P : Prims Bytes) (tx : Tx) (i amt : Nat) (f : Fields) (a : Args) (S : List Bytes)
    (scriptSig : Bytes) (hwf : WF f) (ha : castToBool a.pre = true → ArgsWF a) (hty : f.ty = [0x00] ∨ f.ty = [0x21])
    (htx : TxWF tx) (hamt : amt < 2 ^ 64) (hi : i < tx.inputs.length)
    (hnz : decode (serOutPoint (inputAt tx i)) ≠ 0)
    (hres : Residual P tx i amt f a)
    (hS1 : ((evalScript Eval.opExec (mkEnv params (txContext tx i amt) params.flags.forkAdjust (some (lockOf f)))
      scriptSig [] 0).2).stack = a.stack ++ S)
    (hv : Eval.verifyScript params (txContext tx i amt) scriptSig (lockOf f) = .valid) :
    Accepts P .nft (spendOf tx i f a) := by
  obtain ⟨st1, h1, st2, top, rest, hrun, hs2, htop⟩ := run_of_valid hv
  have hS : st1.stack = a.stack ++ S := by rw [h1] at hS1; exact hS1
  have he : EnvOK (phase2Env (txContext tx i amt)) := envOK_phase2 _
  have hmem : inputAt tx i ∈ tx.inputs := by simp [inputAt, List.getElem?_eq_getElem hi]
  obtain ⟨h32, hidx, -, -⟩ := htx.inputs _ hmem
  -- the run of the suffix and what it leaves on top
  have key : ∀ r, run Eval.opExec (phase2Env (txContext tx i amt)) (lockOf f) []
        (St (a.stack ++ S) [] st1.memUsed {} 0 (lockOf f)) = r → r.IsOk →
      (castToBool a.pre = true → Enforced (phase2Env (txContext tx i amt)) f a (lockOf f)) ∧
      (castToBool a.pre = false → EnforcedMelt (phase2Env (txContext tx i amt)) f a) ∧
      ∃ (rest2 alt2 : List Bytes) (m2 k2 : Nat),
        r = .next (St (ownerCheck (phase2Env (txContext tx i amt)) a (lockOf f) :: rest2) alt2 m2 {} k2 (lockOf f)) := by
    intro r hr hok
    obtain ⟨m', k', hr⟩ := lock_pushes he (by decide) hwf hr hok
    rw [← List.append_nil MinSimple.suffix] at hr
    obtain ⟨hA, hB, m2, k2, rest2, alt2, hend⟩ := minSimple_sound he (by decide) hty hr hok
    rw [run.eq_1] at hend
    exact ⟨fun h => (hA h).1, hB, rest2, alt2, m2, k2, hend.symm⟩
  rw [hS] at hrun
  obtain ⟨hA, hB, rest2, alt2, m2, k2, heq⟩ : (castToBool a.pre = true → _) ∧ (castToBool a.pre = false → _) ∧
      ∃ (rest2 alt2 : List Bytes) (m2 k2 : Nat), GOut.next st2 =
        .next (St (ownerCheck (phase2Env (txContext tx i amt)) a (lockOf f) :: rest2) alt2 m2 {} k2 (lockOf f)) := by
    rcases hrun with hrun | hrun
    · exact key _ hrun trivial
    · obtain ⟨-, -, _, _, _, _, h⟩ := key _ hrun trivial
      cases h
  -- the owner's signature verifies
  have htop' : top = ownerCheck (phase2Env (txContext tx i amt)) a (lockOf f) := by
    rw [GOut.next.injEq] at heq
    rw [heq] at hs2
    simp only [List.cons.injEq] at hs2
    exact hs2.1.symm
  have hsig0 : Ops.Crypto.txCheckSig tx i amt a.sig a.pk (cleanupScriptCode (lockOf f) a.sig true) true = true := by
    rw [htop'] at htop
    unfold ownerCheck at htop
    split_ifs at htop with hc
    · exact hc
    · simp at htop
  -- the clauses common to every path
  have hin := hi
  rcases hpre : castToBool a.pre with _ | _
  · -- a melt
    have hm := hB hpre
    have hlast := getLast_eq_of_drop hm.sigType
    have hsig : P.verify a.pk (P.sighash (absTx tx) i) a.sig = true := by
      rw [hres.agrees.verify, ← cleanupScriptCode_forkid (lockOf f) a.sig hlast]; exact hsig0
    have hk : kindOf f a = .melt := kindOf_melt.mpr hpre
    refine accepts_of_facts P tx i f a hty hin (hres.melt hpre).2 (by rw [hres.agrees.h160]; exact hm.owner) hsig
      (by simp [hlast]) hm.issuer (fun h => absurd hk h) (fun _ => ?_) (fun h => absurd (h ▸ hk) (by decide))
    intro o ho
    obtain ⟨o', ho', rfl⟩ := List.mem_map.mp (by simpa [absTx] using ho)
    exact (hres.melt hpre).1 o' ho'
  · -- a commit or a settle
    have henf := hA hpre
    have hlast := getLast_eq_of_drop henf.sigType
    have hsig : P.verify a.pk (P.sighash (absTx tx) i) a.sig = true := by
      rw [hres.agrees.verify, ← cleanupScriptCode_forkid (lockOf f) a.sig hlast]; exact hsig0
    -- the preimage is the real one
    obtain ⟨tail, X, A, m, C, kk, r', hC, hpt, hok'⟩ := henf.pushTx
    have hh : Hash.hash256 a.pre = sighashBIP143 (lockOf f) tx i ⟨0x41⟩ amt :=
      hres.pushTx a.pre tail X A m C kk r' hC hpt hok'
    have hpre_eq : a.pre = preimageBIP143 (lockOf f) tx i ⟨0x41⟩ amt := hres.preimage _ (by rw [hh]; rfl)
    obtain ⟨-, hsc, hver', hprev, hout, hval, hhout, -⟩ :=
      preimage_fields (lockOf f) (by rw [lockOf_length_eq hwf]; decide) tx i amt h32
    rw [← hpre_eq] at hsc hver' hprev hout hval hhout
    have hver : 2 ≤ tx.version :=
      two_le_of_decode_serVersion _ htx.version (by rw [← hver']; exact henf.version)
    have hflat : expectedOuts f a ++ a.chg = (tx.outputs.map serTxOut).flatten :=
      hres.outputs _ (by rw [henf.outputs, hhout]; rfl)
    have hiss : decode f.parent = 0 → f.issuer = a.pk := fun h => henf.issuer (guard_of_genesis h)
    have hnotmelt : kindOf f a ≠ .melt := by
      intro h; rw [kindOf_melt] at h; rw [hpre] at h; cases h
    refine accepts_of_facts P tx i f a hty hin hver (by rw [hres.agrees.h160]; exact henf.owner) hsig
      (by simp [hlast]) henf.issuer (fun _ => ?_) (fun h => absurd h hnotmelt) ?_
    · rcases hty with hty | hty
      · exact outs_commit hwf (ha hpre) htx hamt hty hpre h32 hidx hnz hiss hval hout hsc hflat
          (by have := hres.honest hpre; rwa [ite_eq_left hty] at this)
      · exact outs_settle hwf (ha hpre) htx hamt hty hpre h32 hidx hnz hiss hval hout hsc hflat
          (by have := hres.honest hpre; rwa [ite_eq_right (settle_ne_commit hty)] at this)
    · intro hk gp hgp
      obtain ⟨-, hne⟩ := kindOf_settle.mp hk
      rcases hty with hty | hty
      · exact absurd hty hne
      · exact rebuild_facts htx hty hpre h32 hout hprev henf hres.gp hres.prevouts gp hgp

end BoltProof.Glue.MinSimple
