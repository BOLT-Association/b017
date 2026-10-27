import BoltProof.Model.Assumptions

/-!
# BoltProof.Model.Covenant

**The covenant interface.** `Accepts P fam s` says "the family-`fam` covenant, executed on the
spend `s`, evaluates to true". Its fields are Lemmas 1–7 of `docs/formal-proof.md` §3, stated
as the constraints the covenant imposes on the spending transaction. Every theorem of
Layer 1 is proved from these fields alone.

What this does **not** say: that the shipped bytecode enforces exactly these fields. That is
the bridge Layer 2 provides on concrete transactions, and the residual trust boundary
described in `lean/README.md`.
-/

namespace BoltProof

/-- The covenant accepts the spend. Field names carry the lemma they encode. -/
structure Accepts {Txid : Type} (P : Prims Txid) (fam : Fam) (s : Spend Txid) : Prop where
  /-- The covenant runs on the input that spends the token. -/
  input_is_spent : s.tx.inputs[s.inputIndex]? = some s.spentOutpoint
  /-- The covenant asserts transaction version ≥ 2. -/
  version : 2 ≤ s.tx.version
  /-- **L1 (signature binding)**: `H160(pubKey) = owner`. -/
  l1_owner : P.h160 s.signer = s.spent.owner
  /-- **L1**: `Verify(pubKey, ctx, sig) = 1` over this transaction's `SIGHASH_ALL` digest. -/
  l1_sig : P.verify s.signer (P.sighash s.tx s.inputIndex) s.sig = true
  /-- **L1**: the sighash flag is `SIGHASH_ALL | SIGHASH_FORKID`. -/
  l1_type : s.sigHashType = 0x41
  /-- A commit spends a settle-typed token (§1.4). -/
  commit_type : s.kind = .commit → s.spent.txoType ∈ fam.settleTypes
  /-- A commit's mode is one the family admits (the NFT family only transfers). -/
  commit_mode : s.kind = .commit → s.mode.commitType ∈ fam.commitTypes
  /-- A settle spends a commit-typed token (§1.4). -/
  settle_type : s.kind = .settle → s.spent.txoType ∈ fam.commitTypes
  /-- A settle's mode is the one the spent commit type encodes. -/
  settle_mode : s.kind = .settle → fam.modeOfCommitType s.spent.txoType = some s.mode
  /-- **L5 (issuer enforcement)**: on a genesis spend (and, NFT, a first-commit-output spend)
  the signer is the issuer. -/
  l5_issuer : s.spent.issuerMustSign fam → s.signer = s.spent.issuer
  /-- **L5**: the first commit may not be a merge. -/
  l5_no_merge_at_genesis : s.spent.isGenesis → s.mode ≠ .merge
  /-- **L2 (output determinism)**: the outputs are exactly the reconstructed ones, followed by
  change that carries no token. -/
  l2_outs : s.kind ≠ .melt →
    ∃ change : List (Out Txid), (∀ o ∈ change, o.isToken = false) ∧
      s.tx.outputs = s.expectedOuts fam ++ change
  /-- **L2 (melt)**: a melt produces P2PKH outputs only. -/
  l2_melt : s.kind = .melt → ∀ o ∈ s.tx.outputs, o.isP2pkh = true
  /-- **L6**: the spent balance is in range (fungible). -/
  l6_bound : fam = .fungible → s.spent.balance ≤ Fam.maxBalance
  /-- **L6**: a split commit may not over-take (`balance − piece ≥ 0`; a zero piece is allowed). -/
  l6_split : s.kind = .commit → s.mode = .split → s.piece ≤ s.spent.balance
  /-- **L6**: a merge commit keeps the sum in range. -/
  l6_merge : s.kind = .commit → s.mode = .merge →
    ∃ o, s.other = some o ∧ s.spent.balance + o.1.balance ≤ Fam.maxBalance
  /-- **L6**: the split settle re-asserts `remainder ≥ 0`. -/
  l6_settle_split : s.kind = .settle → s.mode = .split → s.spent.balanceCommit ≤ s.spent.balance
  /-- **L6**: the merge settle re-asserts the sum bound. -/
  l6_settle_merge : s.kind = .settle → s.mode = .merge →
    s.spent.balance + s.spent.balanceCommit ≤ Fam.maxBalance
  /-- A second token input exists exactly on a merge commit. -/
  other_iff_merge : s.other.isSome ↔ (s.kind = .commit ∧ s.mode = .merge)
  /-- The second token input is a distinct input of this transaction. -/
  other_input : ∀ o, s.other = some o → o.2 ∈ s.tx.inputs ∧ o.2 ≠ s.spentOutpoint
  /-- A merge fuses tokens of one issuer (both covenants pin the output issuer to their own). -/
  l_merge_same_issuer : ∀ o, s.other = some o → o.1.issuer = s.spent.issuer
  /-- The second token input is settle-typed: its own covenant also runs on this transaction,
  and only a settle-typed token's covenant accepts a commit-shaped spend. -/
  other_settle_typed : ∀ o, s.other = some o → o.1.txoType ∈ fam.settleTypes
  /-- **L3 (ancestor integrity)**: a settle of a token with a grandparent rebuilds the
  grandparent transaction, matches its id, co-spends the grandparent's proof output, and
  (fungible) anchors the spent balance to the rebuilt ancestor's own balance transition
  (the §8.1 fabricated-hop defence). -/
  l3_rebuild : s.kind = .settle → ∀ gp, s.spent.grandparent = some gp →
    ∃ (A : TxDesc Txid) (t : Token Txid),
      s.anc = some A ∧ P.txid A = gp.txid ∧ A.outputs[gp.vout]? = some (.token t) ∧
      (∃ j pkh, A.outputs[j]? = some (.proof pkh) ∧ (⟨gp.txid, j⟩ : Outpoint Txid) ∈ s.tx.inputs) ∧
      (fam = .fungible → ∀ p, s.spent.parent = some p →
        s.spent.balance = t.settledBalance fam p.vout)
  /-- **L3 (merge)**: the other lineage is bound the same way through `otherGrandparent`. -/
  l3_merge : s.kind = .settle → ∀ ogp, s.spent.otherGrandparent = some ogp →
    ∃ (B : TxDesc Txid) (t : Token Txid),
      s.ancB = some B ∧ P.txid B = ogp.txid ∧ B.outputs[ogp.vout]? = some (.token t) ∧
      (∃ j pkh, B.outputs[j]? = some (.proof pkh) ∧ (⟨ogp.txid, j⟩ : Outpoint Txid) ∈ s.tx.inputs)
  /-- **L4 (null-ancestor enforcement)**: no rebuild on a commit or a grandparent-less spend. -/
  l4_null : (s.kind = .commit ∨ s.spent.grandparent = none) → s.anc = none ∧ s.ancB = none

end BoltProof
