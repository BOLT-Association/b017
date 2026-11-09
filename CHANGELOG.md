# Changelog

All notable changes to **b017** are documented here. The format is based on
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and this project aims to follow
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added
- **`docs/issuer-guard.md`: the issuer guard of each family, decoded from the shipped bytecode.** The NFT
  prologue derives `is2ndTx = (grandparent == 0 && txoType != 0)` and requires the issuer under
  `isGenesis || is2ndTx`; the fungible prologue requires the issuer under `isGenesis || grandparent == 0`, the F3
  fix of 2026-09-07, which is a strict superset. The document tells apart the three things that keep being
  conflated (the fabricated hop and its balance anchor; F3 and its zero-grandparent guard; `is2ndTx`, an NFT-only
  design feature that predates both), gives the timeline with commit ids, explains why the NFT family can tolerate
  the settle-typed zero-grandparent orphan at its commit and that F3 was the commit-typed shape both rules refuse,
  and says why `is2ndTx` must **not** be ported (it would close nothing, and the prologue length is the rebuild's
  `signCtx` slice offset).
- **`test/lib/multiBoltIssuerGuard.test.ts`** pins the issuer guard on the bytes of every contract that carries it.
  Fungible (`SimpleMultiBOLT`, `FixedBOLT`, `OpenBOLT`): a non-issuer's spend of the F3 / `is2ndTx` shape (`21`, no
  grandparent) and of the settle-typed orphan (`20`, no grandparent) that only the fungible rule refuses at its
  commit, each naming the victim issuer and carrying 2^100, is refused at the guard's own `OP_EQUALVERIFY`; the
  honest first settle, and the same bytes under the attacker's own issuer key, are accepted. NFT (`MinSimpleBOLT`,
  `AuthBOLT`, `SerialBOLT`): the `is2ndTx` shape is refused at the guard, the attacker-issuer control is accepted,
  and the resting `00` orphan's lone commit is accepted, pinning the narrower NFT rule. The guard is located from
  its own flag (`OP_BOOLOR`, then `OP_IF`), not by position, since the genesis contracts run an earlier
  `OP_EQUALVERIFY` on `mintData`. No existing test exercised the guard's grandparent branch on any contract but
  MinSimpleBOLT.
- **`docs/ROADMAP.md`** records, as deferred work, aligning the NFT issuer guard with the fungible rule (drop the
  `txoType` term from `is2ndTx`): an optimisation, not a fix, to be folded into the next NFT bytecode rebuild since
  it changes the fingerprint and needs a reissue.
- **A machine-checked proof** (`lean/`, Lean 4). Terms: the *model* is Lemmas 1–7 of `docs/formal-proof.md` written
  in Lean as `Accepts`; the *script* is each covenant's compiled bytecode as shipped. Layer 1 proves Theorems 1–4 of
  the model for both families over arbitrary runs, with Assumptions 1–2 as hypotheses and only Lean's three standard
  axioms; a concrete NFT lifecycle is proved a valid run. Layer 2 runs the script inside Lean, with bsv-script-lean
  v1.2.0 under today's BSV rules (post-Chronicle; the old rules are a control only), on the test suite's real
  transactions: the honest lifecycles, every red-team attack and the historical fabricated-hop chain against its
  pre-fix script. Each verdict is registered with the kernel (`native_decide`) and the scanner's fingerprints are
  recomputed. `npm run lean:vectors` regenerates the vectors deterministically; the CI job `lean-proof` builds the
  proof, runs every vector, audits axioms and fails on vector drift. `docs/formal-proof.md` §1.6 states what is
  still trusted.
- `test/helpers/minSimpleAttacks.ts`: the NFT red-team builders, shared by the suite and the exporter.
- **`test/lib/indexByte.test.ts`**, with `test/helpers/indexByte.ts`: the index-byte shapes of the `smb_probe_idx_*`
  vectors under the fast suite. The builders (a split settle rebuilt with `pkh1` or `i2` set, a commit or settle with
  `inputIndexN` = 1, a token object on any output) are shared with the Lean vector exporter, which imports them, so
  the two judge the same transactions: four tests, every later operation on a token whose index byte is not its
  position accepted by the Spend engine (no dead tokens).
- **`docs/ROADMAP.md`** records, as deferred work, dropping the fungible lock's index byte `outputIndexN`, which
  nothing on chain or off reads, at the next fungible bytecode rebuild (new fingerprints and a reissue, so never on
  its own); `inputIndexN` stays as the merge-role flag.
- **Theorem 1 per hop** (`t1_step`, `t1_genesis_signer`, `lean/BoltProof/Theorems/Authenticity.lean`): every token
  a spend produces is built from the one it spent, same issuer, that token as parent; a genesis moves only under the
  issuer's key. Stated of the script for every valid input by `real_issuer_carried` and `real_genesis_needs_issuer`
  in `Glue/Refine/EndToEnd.lean` (MinSimpleBOLT) and `Glue/SimpleMulti/EndToEnd.lean` (SimpleMultiBOLT).
- **`lean/BoltProof/Theorems/Chain.lean`, the Layer 1 half of the chaining step**: in a valid run a settled token's
  grandparent is output 0 of an earlier commit step whose outputs are its token, the recipient's proof and, for a
  split, the second recipient's proof (`Run.grandparent_commit`), so the index the script forces (1, or 2 for a
  split) names a proof output of the real grandparent. Reading a real transaction's bytes as that step's `TxDesc`
  is what remains of the composition.
- **The chaining step, Bridge half** (`lean/BoltProof/Bridge/Glue/Refine/Chain.lean`, `Glue/SimpleMulti/Chain.lean`,
  `Theorems/Chain.lean`): a chain of real MinSimpleBOLT or SimpleMultiBOLT spends, each read by its refinement, with
  the UTXO model's bookkeeping (a well-formed genesis set, each step spending live tokens, each transaction id new),
  is a valid model run (`valid_of_chain`), so Theorems 1, 3, 4 and 5 hold of real tokens: every live token is rooted
  at a genesis of the run and carries the issuer along its lineage, tokens are neither created nor duplicated and
  value is conserved, every type byte is defined, and each real commit's proof admits one settle carrying the
  committed balance (`chain_authenticity`, `chain_count`, `chain_conservation`, `chain_defined_types`,
  `chain_proof_gating`, `chain_fabricated_hop_excluded`). The grandparent's reality (`GpReal`) is read off the run
  (`Run.grandparent_layout_upto`): outright for the NFT script, and for the fungible one under A1 plus one fact read
  off the ancestors' bytes, that their balance fields are non-negative script numbers (`BalsNonneg`).
- **The second rebuild welded** (`lean/BoltProof/Bridge/Glue/SimpleMulti/RebuiltBParse.lean`, `AnchorB.lean`,
  `GpWeldB.lean`, generated by `lean/scripts/gen_rebuiltB_parse.py` from the first rebuild's files): the bytes a merge
  settle hashes against the other lineage's grandparent txid are parsed as a transaction whose first output is the
  pieces' token, under the widths the run fixes and `HonestPiecesB` of the first piece set, and identified with the
  real other grandparent under no second preimage of its serialisation (`gp_eq_gpTxB`). `GpRealB` is now
  `GpRealF`'s twin (well-formed, the txid, the token at the named index, the proof outputs), the merge-settle
  refinement reads the other grandparent's token type off the bytes (`gpB_token_of_facts`), and the fungible chain
  asserts nothing of a merge settle beyond its spend: `typeB` is gone, and `BalsNonneg` is the one byte-level fact
  the chain still reads off the ancestors. `BalsNonneg` is narrowed to the single grandparent token output the
  anchor reads, the minimal form, and stays a documented decidable assumption discharged on every vector.
- **`lean/BoltProof/Bridge/Glue/SimpleMulti/EndToEnd.lean`**: the fungible end-to-end statement. Each proof stage's
  hypotheses are one structure (`RealSpend`, `RealSettleGp`, `RealMergeCommit`, `RealMergeSettle`); Lemma 1,
  Theorems 2, 3 and 4 per step and Theorem 1 per hop are stated of any `SimpleMultiBOLT` spend the script accepts.
- **Lemma 4 proved over the bytecode** (`lean/BoltProof/Bridge/Gadgets/`): the null-ancestor check's tail
  `OP_SIZE OP_NIP OP_0 OP_EQUALVERIFY` passes exactly when the concatenated ancestor arguments are empty and
  fails with `SCRIPT_ERR_EQUALVERIFY` otherwise, for every input, over bsv-script-lean's own instruction loop and
  with only the three standard axioms; nine per-instruction step lemmas it rests on.
- **Lemma 6's over-take guard proved over the bytecode** (`Gadgets/BalanceGuards.lean`): the split commit's
  `2d OP_PICK 34 OP_PICK OP_SUB OP_0 OP_GREATERTHANOREQUAL OP_VERIFY` passes exactly when `piece ≤ balance` and
  fails with `SCRIPT_ERR_VERIFY` otherwise, for every input. **Its merge sum guard** `2d OP_PICK 34 OP_PICK OP_ADD
  OP_11 OP_PICK OP_LESSTHANOREQUAL OP_VERIFY` likewise passes exactly when `balance + other ≤ bound`.
- **Lemma 7 proved over the bytecode** (`Gadgets/Parity.lean`): the fungible covenant's 29-byte parity check
  (`1a OP_PICK OP_2 OP_MOD OP_DUP OP_IF … OP_ENDIF OP_DUP 27 OP_PICK OP_2 OP_MOD OP_SWAP OP_IF OP_0 OP_ELSE OP_1
  OP_ENDIF OP_EQUALVERIFY`) passes exactly when a commit-typed spent token is followed by its own settle type and a
  settle-typed one by a commit type, and fails with `SCRIPT_ERR_EQUALVERIFY` otherwise, for every input; on the six
  defined type bytes this is the Lean model's `Fam.edge .fungible` relation (`parityCheck_edge_iff`). Step lemmas
  for the conditionals (`OP_IF`, `OP_ELSE`, `OP_ENDIF`, skipped instructions) and the arithmetic added.
- **Lemma 7 for the NFT family proved over the bytecode** (`Gadgets/NftType.lean`): the NFT covenants write the
  produced type rather than check it — the selector `d OP_PICK OP_IF 0100 OP_ELSE 0121 OP_ENDIF OP_CAT` of
  `MinSimpleBOLT`, `AuthBOLT` and `SerialBOLT` appends type `0x00` to a commit-typed token's successor and `0x21` to a settle-typed one's, for every input; on
  the family's type bytes this is the model's `Fam.edge .nft` relation (`nftTypeSel_edge`).
- **Lemma 6's bounds and settle-side re-checks proved over the bytecode** (`Gadgets/BalanceBounds.lean`): the
  balance bound check (`0 ≤ balance ≤ 2¹²⁷−1`, offsets 610 and 621), the merge settle's sum re-check (offset 781)
  and the split settle's remainder re-check (offset 935) each pass exactly when their arithmetic predicate holds
  and fail with `SCRIPT_ERR_VERIFY` otherwise, for every input; with the commit guards this closes Lemma 6 at the
  fragment level.
- **Theorem 5, proof gating** (`lean/BoltProof/Theorems/ProofGating.lean`): the §8.1 fabricated-hop exclusion at the
  ledger level — under the UTXO no-double-spend rule a commit's proof output admits at most one settle, and under
  collision resistance a settle's balance is exactly the settle result of the real commit its grandparent names.
  The run model admits only covenant-created tokens, so the attack's own non-covenant transactions are outside it;
  a recipient's off-chain lineage checks (`docs/verification-scaling.md`) are not formalized.
- **The script proved to enforce the model, per input** (`lean/BoltProof/Bridge/Glue/`, described in
  `lean/README.md`). A symbolic execution of each of the four scripts from the stack the unlocking script leaves,
  built from one inversion lemma per opcode and the `sym_all` driver over the scripts cut into named chunks
  (`lean/vectors/sections.ts` → `Generated/Chunks.lean`). Per script, `*_sound` states what it enforces whenever it
  does not fail, `reaches_*` shows the run reaches every fragment proved in `Gadgets/` with the stack its lemma
  assumes, and `*_refines` (one per NFT script, four stages for `SimpleMultiBOLT`) shows that any spend the network
  accepts is one the model accepts, under assumptions listed once per script: OP_PUSH_TX binds the preimage and
  nothing the spend hashes has a second preimage; the grandparent a token names is the real commit two steps back;
  three model rules the script does not check; and, fungible only, its open questions. Standard axioms only;
  `Regress.lean` applies each theorem to the real honest spends (`native_decide`). The axiom audit now has Lean
  enumerate Layer 2's declarations, and `AxiomCheck.lean` lists the glue's theorems. The generators of the glue's
  regular files are under `lean/scripts/`.

### Changed
- **The model's L2 and L3 clauses admit exactly what the script admits** (`lean/BoltProof/Model/Covenant.lean`,
  `Model/Spend.lean`). A split settle's two tokens may come out in either order (`Spend.OutsOK`), and the anchor
  names the proof a settle co-spends: the balance carried is the settle result at the index one below that proof,
  not at the parent's position, which the script never reads. Safe: the order changes neither recipient nor
  balance, only a proof's recipient can spend it, the script forces the proof to the grandparent's first or, for a
  split, second output (`AnchorOK`), and Theorem 5 lets each proof admit one settle, so each settle result of a
  real commit is claimed at most once. The position-based anchor was wrong in the swapped order. Theorems 1–4 keep
  their statements; Theorem 5's anchor names the proof's index. The script-to-model proofs no longer assume the
  split settle's flags or the anchor argument `i5`: `Residual` loses `splitFlags` and `ResidualGp` loses `i5`;
  `outs_settle_split` proves both orders from the script's flag cases and `AnchorOK.index` reads the anchor's index
  from the script's own check. SimpleMultiBOLT's remaining assumptions are Q4, Q7 and Q8 of `lean/README.md`.
- **The chain stated for AuthBOLT and SerialBOLT** (`lean/BoltProof/Bridge/Glue/AuthBolt/Chain.lean`,
  `SerialBolt/Chain.lean`): each is MinSimpleBOLT's chain file over its own abstraction, so a chain of real
  AuthBOLT or SerialBOLT spends is a valid model run and Theorems 1, 3, 4 and 5 hold of their real tokens too
  (`valid_of_chain`, `chain_authenticity`, `chain_count`, `chain_defined_types`, `chain_proof_gating`,
  `chain_fabricated_hop_excluded`). Their `GpReal` was already settle-only, so the grandparent's reality is read
  off the run as it is for MinSimpleBOLT, with nothing assumed. The chain now covers all four shipped scripts.
- **`lean/README.md` is the one document of the Lean development.** It absorbs the glue plan (`lean/GLUE-PLAN.md`:
  the proof style, the per-script structure, the rebuilds, the chain, the assumptions, the findings, the open
  questions and the build notes) and the checklist `lean-proof-todo.md`, both deleted; the prose is compressed, the
  follow-ups are listed once, and the generators' pitfalls are recorded in `lean/scripts/README.md`. The sources,
  the exporter's vector notes and the other documents now point at the README.
- **The NFT refinements ask `GpReal` of a settle only** (`Residual.gp`): a commit's token can name a settle
  transaction as its grandparent, which has no proof output at index 1, so the unconditional form could not be met
  by the commits of a chain. The theorems are stronger, their proofs unchanged.

### Findings (from the Lean bridge, bsv-script-lean v1.2.0)
- **A merge's carried balance is checked at the settle, not the commit** (`lean/README.md` Q8; vectors
  `smb_probe_q8_melt_other_*`). A merge commit whose partner input takes the melt branch is accepted whatever balance
  it claims for the partner. The settle with the honest balance passes; the settle claiming 1,000,000 for a token of
  balance 1 is refused (`SCRIPT_ERR_EQUALVERIFY`). An inflated merge commit can exist but never settles; no settled
  token carries value nobody minted. The proofs keep the assumption that the partner presents a preimage, and a
  `0x25` token's `balanceCommit` is unchecked until its settle.
- **A merge settle's other-lineage index is pinned to a proof output** (Q9; vectors `smb_probe_q9_i4_change_*`,
  controls `smb_probe_q9_i4_proof_*`). A merge settle whose `i4` names the other grandparent's change output instead
  of its proof, and spends that output in the proof input's place with its owner's key, is refused at the covenant
  input (`SCRIPT_ERR_EQUALVERIFY`), whether the other grandparent is a transfer commit or a split commit; the same
  settle with `i4` on the proof passes. The other lineage's proof cannot be left unspent, so proof gating holds on
  both sides of a merge. The pin is read off the bytes by `anchorB_index` (`RefineMergeSettle.lean`): the second
  rebuild's anchor fixes `i4` to 1, or to 2 under the split type piece, as `AnchorOK.index` fixes `i5`. `GpRealB`
  asks a proof output at 1 and, under the split type piece, at 2, instead of one at `i4`, and the second rebuild's
  weld identifies the pieces with the real other grandparent, so the chain asserts nothing of a merge settle beyond
  its spend.
- **An undefined next type cannot be committed** (Q4; vectors `smb_probe_type_oor_27_commit`,
  `smb_probe_type_oor_29_commit`, with `smb_probe_type27_commit`). The parity check fixes only the next type's
  parity, so off genesis the spender may name any odd byte, and the issuer guard refuses `0x27` only when it fires
  (genesis or no grandparent). But a mid-lineage commit whose spent token has a grandparent (the guard silent) and
  an undefined next type is refused at the covenant's own `OP_EQUALVERIFY`, so the written type is pinned to the six
  even off the guard. This resolves Q4 of `lean/README.md` empirically; the `SmbType a.nty` restriction the
  soundness and refinement theorems carry is the modelling boundary, not a gap, with these probes as the standing
  evidence (a formal derivation would drive a symbolic next type through the output builder, a path-family proof,
  deferred).
- **A split settle's output order is the spender's** (Q3; vectors `smb_probe_q3_*`). With `pkh1` set, the script
  accepts the settle with its two tokens swapped, each index byte off its position; both stay spendable with the
  committed recipients and balances. Harmless to value; the model admits either order (`Spend.OutsOK`) and the proof covers
  both, so no assumption on the flags remains. Followed through every later operation (`smb_probe_idx_*`, 20 vectors): a token whose index byte
  disagrees with its position, by `pkh1`, `i2` or `inputIndexN`, is transferred, split, merged as either input and
  melted by the honest builder with every input accepted. No spend reads the byte: each spend writes it afresh, the
  rebuild hashes it as supplied, and the anchor's index comes from the proof-vout argument. No token dies of it.
- **A cross-issuer merge is refused by the other token's covenant** (input 1 of the merge commit,
  `SCRIPT_ERR_EQUALVERIFY`): both covenants pin the output's `issuerPubKey` to their own, as the interface clause
  `l_merge_same_issuer` states.

### Fixed
- **Docs: `formal-proof.md` Lemma 5 still described the pre-F3 fungible guard** ("the only issuer check ...
  fires when the spent token is parentless"). The lemma now states the shipped rule for both families inline,
  with a two-line provenance note in place of stacked corrections; §8.1 gains the F3 row and §9 the new suite; the
  README links the new document and notes that both families demand the issuer at the first settle too.
- **Docs: `formal-proof.md` §9 and `unforgeability.md` §7 had gone stale.** Both quoted "126 tests across 18
  files", cited suites removed in `ab95827` (`parity.test.ts`, `singleAncestor.test.ts`, `singleCoupon.test.ts`)
  and said the scanner accepts a lone genesis mint, which it has refused as unauthenticated since `110ff77`. The
  rows now cite the suites that carry each property, and the counts point at the README, where
  `npm run coverage:readme` generates them, instead of being copied.
- Documentation corrected by what the Lean glue found: the NFT prologue's `OP_DUP OP_BIN2NUM OP_0NOTEQUAL` runs
  on the grandparent outpoint (`gp ≠ 0`), not the type (`Gadgets/NftType.lean`, `lean/README.md`); `lean/README.md`'s
  issuer-guard note said the fungible family lacks the second-spend guard, which `docs/issuer-guard.md` and the
  glue's `Enforced.issuer` both show it has; and two rejected vectors fail where the exporter's comments now say
  (`smb_wrong_key_commit#0` at the prologue's issuer guard, `smb_extra_output_settle#0` in the unlocking script's
  own OP_PUSH_TX).

## [0.1.0] - 2026-10-11

### Changed
- **Coverage is 100% on every metric and the thresholds enforce it** (`vitest.config.ts`: statements, functions,
  lines and branches 100; was 99 / 100 / 99 / 98), so a new uncovered branch fails the coverage run. Three
  reachable branches gained tests (`coverageEdges`: `p2pkhUnlock` signing from an attached source without a txid,
  and refusing a txid with no source; a merge paid to a public-key recipient keeps the builder's signer). 14
  defensive guards were marked unreachable with their reason (21 `v8 ignore` markers in all; none covers a covenant
  path or a scanner verdict).
- **`verifyTx` is documented as throw-on-failure, and the dead checks behind it are gone.** Every failure already
  threw (a failing script: `Spend.validate()` throws rather than returning false), so `valid` was always `true` when
  it returned. Its type now says so (`valid: true`; the `{ valid, scriptExecutions }` shape is kept, so callers are
  unaffected), and the `if (!valid)` checks in `verifyTx` and the `SimpleMultiBOLT` builder are removed. A builder
  failure now reads `<TX TYPE> not valid: <the script error>` (e.g. `MERGE COMMIT TX not valid: ... OP_EQUALVERIFY ...`);
  the separate `Mint tx not valid` / `... tx not valid [bsv]` messages, which could never fire, are gone.
  `npm run coverage:check` now compares the README's percentages and test counts, not the `(covered/total)`
  fractions: V8 counts a few closure branches on some runs only, so the branch total moves by one or two between
  identical runs while coverage stays 100%.

### Added
- **The genesis family: `FixedBOLT`, `OpenBOLT` and `SerialBOLT`.** Three token types whose lock leads with the
  token's own asset outpoint (null on the mint, the mint outpoint from the first spend on) and the issuer's
  `mintData` (0..255 bytes on the mint only, `OP_0` on every later output), so a token names its asset in O(1).
  - `FixedBOLT` (fungible): one genesis per asset, a fixed supply. Only tokens of one genesis merge; a cross-genesis
    or cross-issuer merge is refused by the covenant at the merge commit, and the class refuses it before building.
  - `OpenBOLT` (fungible): one issuer, many mints. Tokens of different mints merge, and the merge commit re-roots the
    stored outpoint (`lastMergeOrGenesisOutpoint`) to vin0's token outpoint; a cross-issuer merge is refused.
  - `SerialBOLT` (NFT): each token carries its own mint outpoint as a serial; zero-funding like `MinSimpleBOLT` (a
    commit or settle may carry no funding input, change is optional).
  - Classes `FixedBOLT`, `OpenBOLT` (every `SimpleMultiBOLT` operation: mint with `mintData`, transfer, split, merge,
    melt); templates `FixedMultiTemplate`, `OpenMultiTemplate`, `SerialBoltTemplate`; `genesisFieldFor`,
    `mintDataFor`, `outpointOf`, `MINT_DATA_MAX_BYTES`. The fungible engine takes a `MultiLayout`
    (`SIMPLE_MULTI_LAYOUT`, `FIXED_BOLT_LAYOUT`, `OPEN_BOLT_LAYOUT`); `SimpleMultiBOLT` is unchanged.
  - Scanner: the three types are registered with two recognition specs each (`mint`: null outpoint + any mintData;
    `postMint`: set outpoint + empty mintData), so a non-empty mintData after the mint is not a token.
    `recognizeToken` returns the type and its phase (`recognizeType` is unchanged). `verifyEvents` pins the
    **asset**, not only the issuer: every token output's outpoint must follow from its parent token (copied, the
    mint outpoint at the first spend, or `OpenBOLT`'s re-root), and a `FixedBOLT` merge must not mix genesis
    outpoints.
  - Fingerprints: `FixedBOLT` `b07ea12b490c759d172016f71d0026c4894ff7d4eadfae75bd845ce72aa5fd81`, `OpenBOLT`
    `47a41a00e199904ba84e2e0e4890d3d041782fa3ca283d26014218e4286b72b6`, `SerialBOLT`
    `aee7eee8b1254aa765d3f896610d052a2b2da997665e3d9f3d37293ef86d6921`.
  - Tests: every ancestor piece and leading push checked byte for byte against chains built by the reference
    simulator (`genesisLayouts`, 27), Spend-engine lifecycles, mintData and merge rules (`GenesisMultiBOLT`, 10), the whole
    zero-funding suite on `SerialBOLT` plus mintData and melt (`serialBoltZF`, 48), templates (9), scanner (21).

### Changed
- **BREAKING for existing tokens: `SimpleMultiBOLT` drops dead covenant code.** The `ancestorHas2TokenOutputs`
  branch is removed: it rebuilt a commit carrying a second token, and no such commit can exist (a commit with a
  second token output is refused at the commit, by the simulator and by both a Bitcoin SV and a teranode regtest).
  With it go its 22 `Vout2*` ancestor args, plus the 6 issuer-key ancestor args nothing has read since the
  issuer-counterfeit fix spliced the token's own `issuerPubKey`. Unlock args 198 -> 170 (75 ancestor pieces per
  ancestor, was 89; `ARGS2CTX_SMB` 192 -> 164, `SKIP_SMB` 178 -> 150); the locking script is 403 bytes smaller
  (static suffix 5103 -> 4700) in every token output, and every settle's unlocking script is smaller too. Every
  covenant decision is unchanged: each executed pick reads the same stack item as before, on every lifecycle
  fixture. The static bytecode changed, so the fingerprint changed:
  `4a7613d176b46f03f1b06df86d7b96a667c31a277e2b4dbc5d5832d1c225fe34` (was
  `368c45fdf92164e4e0869c9062be84621ea8ef040e8591399bf6ff3b8c819b11`). Tokens minted with the previous bytecode
  keep it (the covenant travels in the token script) and are no longer recognised by `recognizeType`; reissue them.

### Added
- **The anchor, and `verifyAndBroadcast`.** The anchor is the token tx a batch stands on: the settle before its
  first commit (settle N-1), or the mint when the batch starts at genesis. What travels p2p is `[mint, c1, s1]` or
  `[sN-1, cN, sN]`. `verifyEvents` now validates the anchor first, like an event tx (golden fingerprint, issuer,
  arrangement, sources, script execution), pulls it into the batch when it was only attached as a source or inside
  a BEEF, and names it in `ScanResult.anchors`. An anchor settle is the one settle allowed without its commit in the
  batch. `verifyAndBroadcast(txs, broadcastAnchor, opts)` runs `verifyEvents` and then hands every anchor to the
  caller's broadcaster; the batch is accepted only if the network accepted or had already seen each one
  (`AnchorRef`, `AnchorStatus`, `AnchorBroadcastResult`, `AnchorBroadcaster`). This closes a forged history hidden in
  the sources: a stranger-signed `commit1` behind `settle1 -> commit2 -> settle2` used to pass as
  `verifyEvents([commit2, settle2])`; `settle1` now fails execution as the anchor. A lone melt now verifies in `verifyEvents` when the settled token
  it spends is attached (the type is read off that token, which becomes the anchor), and an attached source that is
  not the tx its outpoint names is refused. Offline execution reaches the anchor's own inputs only: a forgery two
  events back passes `verifyEvents` and is caught by the anchor broadcast alone (pinned in the tests).
  Tests: `anchor` (52), `anchorShapes` (40).
- **An unfunded anchor is refused without an SPV proof to a known block header.** An anchor must be a tx the
  network has seen and will therefore mine; an anchor with no funding input pays no fee, so being seen proves
  nothing. It is accepted only when it carries a merkle path whose root the caller confirms as a block header:
  `ScanOpts.isKnownBlockRoot(merkleRoot, height)`, or a `chainTracker` (`HeaderSource`) given to
  `verifyAndBroadcast`. No proof, no headers, an unknown root, a wrong height, a path for another tx, or a
  failing lookup all refuse the batch, and nothing is broadcast. The events standing on an anchor may still be
  unfunded. Tests: `anchorUnfunded` (42).
- **A header-proven anchor is not re-executed and needs no sources.** An anchor (funded or not) whose merkle path
  is confirmed against a known block header was validated by consensus, so its inputs are skipped and their source
  txs need not be supplied. A mined anchor can therefore be delivered as BEEF, which stops at proven txs. The
  header lookup is the trust root; a merkle path without a known header changes nothing. Event txs are always
  executed. With a `chainTracker`, `verifyAndBroadcast` now collects the roots in a first pass, asks the tracker,
  and runs the real scan against the answers.
  Tests: `anchorProven`, including an unfunded `SimpleMultiBOLT` anchor.
- **Value conservation is checked.** An anchor whose outputs exceed its inputs is refused. An event tx that does
  so is reported in `ScanResult.offChainOnly` / `EventResult.offChainOnly` (`OffChainOnlyTx`) and accepted: a
  never-broadcast commit / settle is valid off chain. `ScanOpts.requireBroadcastable` refuses such a batch. A
  header-proven anchor is not re-checked. Tests: `valueConservation` (23).
- **The scanner no longer throws on a broken `Transaction` object.** An input with no source reference or no
  unlocking script, or an output with no locking script, makes the SDK throw when the tx is serialised; that used to
  escape `verifyEvents`, `verifyEvent` and `verifyAndBroadcast`. They now return `unverifiable input: ...`.
  Tests: `scannerEdges`, `builderEdges` (46).
- **A batch element that is not a transaction is refused, not thrown.** `null`, `undefined`, a number or a plain
  object in the array used to surface as `unparseable batch: TypeError ...`; it now returns
  `not a transaction: expected a Transaction, raw tx hex, or BEEF hex / bytes`. Tests: `scannerInputs` (12).
- **Coverage tooling (maintainers).** `npm run coverage:gaps` lists every uncovered branch as `file:line`;
  `npm run coverage:readme` generates the README test counts and coverage table (`coverage:check` fails if they
  are stale); `vitest.config.ts` now has coverage thresholds. `verifyEvents.ts` was refactored with no change in
  verdicts (one helper each for the source lookup, the spent txid and error text).
- **`melt(privateKey)` on `MinSimpleTemplate` and `AuthBoltTemplate`** (`SingleUnlockParams.melt`): the owner burns
  the token with a null CTX and no token output, funded or unfunded. Script-level only (the `@bsv/sdk` Spend
  engine); the b017 melt builder has not been run against a node. Tests: `minSimpleMelt` (40).
- **`verifyEvent` takes its verdict from the same scan as `verifyEvents`.** It used to return
  `{ ok: true, kind: "mint" }` for a lone commit, a lone settle or two unrelated settles, ignored
  `trustedIssuerPubKey`, had no anchor step, and threw on an input pointing past its source's outputs. It now
  refuses all of those, requires exactly one action (its anchor and the mint it authenticates may ride along),
  and returns `anchors`. Tests: `verifyEventSingle` (34).
- **`AuthBOLT`: a new identity-NFT type** (`AuthBoltTemplate`, `AUTH_DATA_MAX_BYTES`, `TokenType` `"AuthBOLT"`).
  `MinSimpleBOLT` (zero-funding) plus an arbitrary data field `authOrMiscData` of up to 75 bytes: the first unlock
  argument, created in a commit and authenticated in the settle, which rebuilds its grandparent commit (whose
  scriptSig leads with the value) and binds it to the grandparent txid. The commit's own owner signature does
  NOT cover it. Same six-push lock layout as `MinSimpleBOLT`; recognised by its suffix fingerprint
  `378932c162a2fb2344ae7357664268608a05efa2fc07be60b6dbf35984dcf669`. `unlock()` refuses a value over 75 bytes
  (the lock refuses it too). Node-verified (contract-level broadcast suite) 16/16 on a Bitcoin SV regtest and a
  teranode regtest; the b017 library tests run on the `@bsv/sdk` Spend engine.
- **Zero-funding spends in `singleSpendUnlock` / `singleAncestorPieces`.** The funding input and the change
  output are detected from the tx (`[token, proof?, funding?]`, `[token, p2pb?, change?]`) instead of assumed
  last, and an unfunded or change-less ancestor commit is passed as empty (OP_0) pieces. `SingleLayout`
  (`MIN_SIMPLE_LAYOUT`, `AUTH_BOLT_LAYOUT`) parameterises the 37-arg and 39-arg unlock layouts.
- Documented (README, template headers): a minted token received by SPV does not prove the sender holds the
  issuer key - the issuer-signed **commit** spending it (funded or not) must accompany it, and a token carrying
  `authOrMiscData` must travel with its signed commit **and** settle as the package.
- Tests: `minSimpleZF` (43, the zero-funding matrix + 11 rebuild-mismatch refusals), `minSimpleAttack` (16, the
  first MinSimple red-team suite), `authBolt` (53 incl. a 27-cell path-coverage gate), AuthBolt template and
  scanner (`nftScan`) tests. `npm run build:nft` regenerates both NFT templates from the compiled contract artifacts.

### Security
- **`SimpleMultiBOLT`: the six red-team fixes now ship in the template.** The published `0.0.0-b2`
- **`SimpleMultiBOLT`: the six red-team fixes now ship in the template.** The published `0.0.0-b2`
  bytecode carried only the original fabricated-hop anchor; a red-team campaign then found and
  closed six further covenant defects - five node-verified on a regtest teranode in both directions
  (B1, S1, S2, S3, F3); C5 confirmed in simulation and a 4M-signature measurement (its check is a
  basic signature-length bound with no node/simulator divergence) - now compiled in:
  B1 (`balanceCommit` unchecked -> split inflation to 2^127-1), S1 (co-spent proof not bound to the
  bolt -> a token doubles itself), S2 (rebuilt ancestor's issuer never checked -> counterfeit),
  S3 (splitter swaps bolt order -> theft + freeze), F3 (a zero grandparent disabled the anchor ->
  a non-issuer settles from nothing, contained to one hop), C5 (a signature-length window bricked
  ~1 in 52,000 tokens).

### Security
- **The scanner now EXECUTES scripts.** `verifyEvents` / `verifyEvent` used to be purely structural: a forged commit
  (a stranger's mint, a commit and settle the stranger signed with their own key, which the covenant's issuer guard
  refuses at the commit) passed with `ok: true`. Reproduced, then fixed: every input whose source tx is supplied is run
  on the `@bsv/sdk` Spend engine, and a failure returns `ok: false` with `script execution failed: tx <id> input <n>`.
  This also closes the redteam2 "misreads" C1-C4 (hand-patched second settle, hidden token input, novel txoType,
  inflated balance), which the structure check alone accepted. For mined txs the node already did this; for off-chain
  (SPV / zero-funding) packages nothing had.

### Changed
- **BREAKING (scanner): every input's source tx must now be supplied.** `verifyEvents` / `verifyEvent` refuse an input
  whose source is missing (`source tx <id> of tx <id> input <n> was not supplied`), including funding inputs and the
  mint's funding parent; previously external funding was waved through. Supply sources by attaching `sourceTransaction`,
  by including the parent in the batch, or by sending BEEF. Results gain `sources: { txid, proven }[]`.
- **Added: BEEF.** Event txs may be given as Atomic BEEF (BRC-95) over BEEF V2 (BRC-96), hex or bytes; new exports
  `toAtomicBeef`, `fromBeef`, `isBeef`. BEEF V1 (BRC-62) and a non-self-contained BEEF are refused. BUMPs are not
  checked against block headers (use a `ChainTracker`).
- **BREAKING (scanner): a lone mint is no longer a valid event.** `verifyEvents` / `verifyEvent` now refuse a mint
  that no commit in the same event/batch spends, returning `{ ok: false, unauthenticated: true, reason: "unauthenticated
  mint ..." }` (all token types). A mint only names an `issuerPubKey`; the issuer guard runs when the genesis is first
  spent, so a mint alone proves nothing about who holds the key. This verdict is not a signature failure.
  A mint with its commit + settle (funded or not) is accepted as before. `ScanResult` / `EventResult` gain
  `unauthenticated?: boolean`. Tests: `test/scanner/unauthenticatedMint.test.ts`.
- **BREAKING for existing tokens: `MinSimpleBOLT` is now the zero-funding contract** (the zero-funding build, lock
  1265 -> 1275 bytes) in place of `MSBolt.opt3`. Its static bytecode changed, so its fingerprint changed:
  `5dc9c1ddd27e2c91f919531ad82a32c9ce8da772ab87e39af05c2c3361970122` (was
  `2892679d85ef021d754036094ecd77e14f0c3934a23a48e09e7da337e50f823d`). `recognizeType` no longer recognises
  `MinSimpleBOLT` tokens minted with the old bytecode; they must be REISSUED (the covenant travels in each
  token's locking script). The lock layout and the 37-arg unlock layout are unchanged.
- **BREAKING for existing tokens.** The `SimpleMultiBOLT` static bytecode changed, so its fingerprint
  changed: `368c45fdf92164e4e0869c9062be84621ea8ef040e8591399bf6ff3b8c819b11` (was
  `76cfa45595bfb866010d8f87b9b88d6e27b79a9ab3007119dd00eb0138810c8f`). `recognizeType` no longer
  recognises tokens minted with `0.0.0-b2`/`-b1` bytecode - they classify as untrusted and are
  invisible to `verifyEvents`, wallet balances and scans. The data-push layout (`LAYOUTS`) is
  unchanged, so all TS-side argument construction is identical.
- **Tokens minted with pre-fix bytecode remain exploitable and must be reissued.** The vulnerable
  covenant travels in each token's own locking script; upgrading this library does not protect coins
  already on chain.

### Removed
- **BREAKING: dropped the `MinSimpleDiscountBOLT` and `MinSimpleBalanceBOLT` templates.** The
  package now ships three token contracts: `SimpleMultiBOLT` (fungible), `MinSimpleBOLT` (identity
  NFT) and `AuthBOLT` (identity NFT + auth data), plus the `pay2Proof` UTXO template. The `MinSimpleDiscountTemplate` and
  `MinSimpleBalanceTemplate` exports, their `TokenType` union members, their `LAYOUTS`/`REGISTRY`
  entries and their fixtures are gone. `recognizeType` / `verifyEvents` no longer classify those
  types; any consumer importing the removed templates or naming those type strings must update.
  The kept contracts are unchanged (same bytecode, same fingerprints).
- Coverage for the kept NFT is preserved: `test/lib/minSimpleLifecycle.test.ts` exercises the
  `MinSimpleBOLT` mint/commit/settle and a 2-hop ancestor reconstruction through `verifyTx`,
  standing in for the removed Discount coupon and ancestor-golden tests.

### Fixed
- **`SimpleMultiBOLT`: the second piece of a split could not be transferred or split again.** A settle
  co-spends its ancestor commit's proof, and a split commit carries two (vout 1 for piece A, vout 2
  for piece B). The builder picked `outputs.length >= 5 ? 2 : 1`, which is always 1 for the 4-output
  split commit, so piece B co-spent piece A's proof and its settle failed. The proof vout is now
  looked up by the owner's pubKeyHash. Builder-only: the covenant and bytecode are unchanged. Piece B
  still has to bring its own funding, because the split settle's change pays piece A.
- **`verifyTx` rejected correctly signed inputs with an nSequence of 0.** It passed
  `sequence || 0xffffffff` to the Spend engine, turning a signed non-final sequence into final and
  breaking the sighash. It now uses `??`.

### Documentation
- README: test and coverage figures refreshed (128 tests across 17 files; 99.5% statements,
  100% functions, 96.3% branches), and the NFT is described as the single `MinSimpleBOLT` identity
  token rather than a template family.
- Restored the scanner suite (`test/scanner/verifyEvents.test.ts`) that was deleted with the Discount
  and Balance goldens, rebuilt over live `SimpleMultiBOLT` chains.

See [`docs/ROADMAP.md`](docs/ROADMAP.md) for planned work.

## [0.0.0-b2] - 2026-09-05

### Security
- **`SimpleMultiBOLT`: fixed a balance-inflation forgery (the "fabricated hop").** A past
  recipient of a token could clone a settled token's bytes into an output they funded
  themselves, give it any balance they liked, and roll it forward, co-spending the real proof
  they legitimately held from the transfer they had received. Every existing check passed:
  the commit paid only themselves, the settle rebuilt a genuine grandparent commit and
  consumed a real predecessor UTXO that they could sign for. Nothing tied the balance to
  anything. **A regtest teranode running GoBDK consensus accepted the whole chain.**

  The settle now reads `balance`, `balanceCommit` and `txoType` off the ancestor it has just
  rebuilt, derives the single balance that ancestor authorised (transfer, merge sum, or
  either split piece), and requires the balance of the token being spent to equal it. Both
  sides of that comparison already existed on chain, so **nothing new is stored**: no new
  token field, no new proof field, and no change to the data-push layout.

  There is no gap between the two halves. The rebuild is assembled from fields the spender
  supplies, so a forger must choose: give the ancestor's real fields and the reconstruction
  hashes correctly but authorises the true balance, not the invented one; or doctor them so
  the balance agrees and the reconstruction stops hashing to `grandparentOutpoint`.

  Verified on a real node, not only in simulation: the same rig that accepted the forgery now
  rejects the forged settle (`TX_INVALID (31)`), with the honest prefix still accepted and a
  byte-tampered control still rejected, reproduced across two independent runs.

### Changed
- **BREAKING for existing tokens: `MinSimpleBOLT` is now the zero-funding contract** (the zero-funding build, lock
  1265 -> 1275 bytes) in place of `MSBolt.opt3`. Its static bytecode changed, so its fingerprint changed:
  `5dc9c1ddd27e2c91f919531ad82a32c9ce8da772ab87e39af05c2c3361970122` (was
  `2892679d85ef021d754036094ecd77e14f0c3934a23a48e09e7da337e50f823d`). `recognizeType` no longer recognises
  `MinSimpleBOLT` tokens minted with the old bytecode; they must be REISSUED (the covenant travels in each
  token's locking script). The lock layout and the 37-arg unlock layout are unchanged.
- **BREAKING for existing tokens.** The `SimpleMultiBOLT` covenant bytecode changed, so its
  static-code fingerprint changed. `recognizeType` will no longer recognise tokens minted
  with `0.0.0-b1` bytecode; they classify as untrusted. The API is unchanged, and the
  data-push layout is unchanged, so `LAYOUTS` and all TS-side argument construction are
  identical to `0.0.0-b1`.

  This is a deliberate clean break, and it has a practical consequence worth stating: an old
  token is not merely distrusted, it is **invisible** to anything built on `recognizeType` /
  `verifyEvents`, including wallet balances and scans. There is no legacy recogniser and none
  is planned. If you hold or index `0.0.0-b1` tokens, identify them before upgrading, because
  afterwards this library will not help you find them.
- **Tokens minted with `0.0.0-b1` bytecode remain inflatable and must be reissued.** Upgrading
  this library does not protect coins already on chain: the vulnerable covenant travels in the
  token's own locking script. Reissue is the only remedy.

### Notes
- The NFT templates (`MinSimple`, `MinSimpleDiscount`, `MinSimpleBalance`) are **unaffected**,
  and not merely untested: their ancestor rebuild splices in the token's own balance field
  rather than accepting the ancestor's as an argument, so the value already sits inside the
  pre-image of the hash that must equal `grandparentOutpoint`. An invented balance fails the
  hash. They also have no split or merge, so there is no transition to check.
- `test/repro-fabricated-hop.test.ts` deliberately still asserts that the pre-fix chain
  verifies. It is the record of what a node accepted, and it recognises its fixture against a
  pinned `0.0.0-b1` fingerprint rather than the live registry.

## [0.0.0-b1] — 2026-06-24

### Fixed
- README title typo: "Bicoin" → "Bitcoin". Docs-only republish (no code changes).

## [0.0.0-b] — 2026-06-23

First public beta. The library is functional and fully tested; the API may still change
before `0.1.0`.

### Added
- `SimpleMultiBOLT` fungible token class — mint / transfer / split / merge / melt, each
  producing a real, script-valid Bitcoin transaction verified by the `@bsv/sdk` Spend engine.
- NFT token templates: `MinSimple`, `MinSimpleDiscount`, `MinSimpleBalance`, plus the
  `pay2Proof` UTXO template.
- Off-chain scanner: `recognizeType` / `REGISTRY` strict fingerprinting, and
  `verifyEvent` / `verifyEvents` for validating BOLT transactional events — one event
  (mint, commit→settle pair, or melt) or a whole batch (issuer-pinned, every commit
  paired with its settle).
- Pre-compiled `.sx` contracts embedded in the templates — **no sx compiler at runtime**.
- `@bsv/sdk` as the single peer dependency (no `@elas_co/ts` runtime dependency).

### Packaging
- Build now cleans `dist/` before `tsc` so the published tarball contains no stale artifacts.
- Added `repository`, `bugs`, `homepage`, and `keywords` metadata.

[Unreleased]: https://github.com/BOLT-Association/b017/compare/v0.1.0...HEAD
[0.1.0]: https://github.com/BOLT-Association/b017/compare/v0.0.0-b2...v0.1.0
[0.0.0-b2]: https://github.com/BOLT-Association/b017/releases/tag/v0.0.0-b2
[0.0.0-b1]: https://github.com/BOLT-Association/b017/releases/tag/v0.0.0-b1
[0.0.0-b]: https://github.com/BOLT-Association/b017/releases/tag/v0.0.0-b
