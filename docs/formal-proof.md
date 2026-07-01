# Formal Proof of BOLT Token Unforgeability

**Bitcoin Original Layer-1 Token (BOLT) Protocol**
**Applies to this library: `SimpleMultiBOLT` (fungible) and the minimal NFT templates
(`MinSimple`, `MinSimpleDiscount`, `MinSimpleBalance`).**
**Patent Pending: GB2318902.0**

> This is the rigorous companion to [`unforgeability.md`](unforgeability.md). The accessible
> document gives the intuition; this one states the model, assumptions, lemmas, and theorems
> precisely. It is adapted to the contracts shipped in **this** package — in particular the
> fungible token carries a **16-byte** balance and there is **no swap** operation (it was
> removed; the only transitions are transfer, split, merge, and melt). Where the proof refers to
> "the covenant", it means the pre-compiled locking script embedded in
> `src/tokens/templates/SimpleMulti.sx.template.ts` (and the NFT analogues) — the compiled
> artifact this package ships and that the tests in §9 execute on a real Script interpreter. §1.6
> states precisely how the proof's prose relates to those deployed bytes.

---

## 1. Formal Definitions

### 1.1 Cryptographic Primitives

Let **H** denote Bitcoin's double-SHA-256: `H(x) = SHA256(SHA256(x))`.
Let **H160** denote `RIPEMD160(SHA256(x))`.
Let **Sign(sk, m)** denote an ECDSA signature of message `m` under secret key `sk` on secp256k1.
Let **Verify(pk, m, sig)** denote ECDSA verification of `sig` against public key `pk` and message `m`.

### 1.2 Hardness Assumptions

**Assumption 1 (Collision Resistance of H).** For all probabilistic polynomial-time (PPT)
adversaries A:

    Pr[A outputs (x, y) : x ≠ y ∧ H(x) = H(y)] ≤ negl(λ)

For SHA-256 the best known attack requires O(2¹²⁸) operations.

**Assumption 2 (Existential Unforgeability of ECDSA).** For all PPT adversaries A given `pk`
but not `sk`:

    Pr[A outputs (m, sig) : Verify(pk, m, sig) = 1 ∧ m was not signed by sk] ≤ negl(λ)

**Assumption 3 (Blockchain Finality).** A transaction confirmed at depth d has probability
≤ (q/p)^d of being reversed, where q/p < 1 is the adversary's fraction of hash power
(Nakamoto, 2008). For d ≥ 6 and q/p ≤ 0.25 this is < 10⁻⁴.

> **This assumption is load-bearing and inherited, not proven here.** The anti-forgery argument
> (Theorem 1, §8.1) ultimately reduces the "forge a genesis / splice an ancestor" attacks to the
> immutability of confirmed txids — which holds only while `q/p < 1`, i.e. while no adversary
> controls a hash-power majority. On a chain with low or concentrated hash power this is exactly
> where real-world risk concentrates; the covenant cannot strengthen it. Network-level security is
> a property of the chain the tokens live on, not of this protocol (see §1.6).

**Assumption 4 (Script Correctness).** The Bitcoin Script virtual machine is a deterministic
state machine that correctly evaluates all opcodes per consensus rules. (In this library the
same scripts are independently re-verified by the `@bsv/sdk` Spend engine — see §9.)

### 1.3 Token State

A **BOLT token state** at step n is a tuple:

    T(n) = (owner(n), parent(n), grandparent(n), issuer, balance(n), contract)

Where:
- `owner(n) ∈ {0,1}¹⁶⁰` — `H160(pubKey)`, the current owner's public-key hash.
- `parent(n) ∈ {0,1}²⁵⁶ × ℕ ∪ {⊥}` — `(txid, vout)` of `T(n−1)`, or `⊥` at the genesis root (n = 0).
- `grandparent(n) ∈ {0,1}²⁵⁶ × ℕ ∪ {⊥}` — `(txid, vout)` of `T(n−2)`, or `⊥` if n < 2.
- `issuer ∈ {0,1}²⁶⁴` — compressed public key of the issuing authority. **Immutable.**
- `balance(n) ∈ [0, 2¹²⁸ − 1]` — **16-byte little-endian** balance (fungible `SimpleMultiBOLT`;
  for the plain NFT this field is absent or fixed; `MinSimpleBalance` carries an immutable
  16-byte balance, `MinSimpleDiscount` an immutable 1-byte discount).
- `contract ∈ {0,1}*` — the BOLT locking-script bytecode (self-referential, immutable).

> **Genesis is not a stored field.** Earlier drafts carried a `genesisOutpoint` field; the shipped
> covenant (after the `M-I` refactor) **removed it**. Genesis identity is derived **structurally**: a
> token is a **genesis** iff it is **parentless** — `parent(n) = ⊥`, i.e. its `parentOutpoint` argument
> is zero-length (`MSBolt.std.sx:93`, `SimpleMultiBolt.sx:297`, builder `SimpleMulti.sx.template.ts:67`).
> The **genesis of a chain** is the unique parentless, issuer-signed root reached by walking `parent`
> links; it is committed cryptographically by proof-of-work on that root transaction's txid, not by a
> copied field. Throughout, `genesis(T(n))` denotes *that derived root*, not a stored value.

A token state `T(n)` is **materialised** as a 1-satoshi Bitcoin UTXO whose locking script
encodes the fields above as push-data arguments followed by the contract bytecode.

### 1.4 Valid Transitions

A **transition** τ: T(n) → T(n+1) is a Bitcoin transaction spending the UTXO encoding `T(n)`
and creating the UTXO(s) encoding `T(n+1)`. This library admits three transition classes
(no swap):

| Transition | Modes | Notation | Required inputs | Produced outputs |
|-----------|------|----------|-----------------|------------------|
| Commit | Transfer / Split / Merge | C(n) | T(n) [+ T_other] + funding | T(n+1) + proof(s) + change |
| Settle | Transfer / Split / Merge | S(n) | T(n) [+ T_other] + proof(s) + funding | T(n+1) [+ T′(n+1)] + change |
| Melt | Terminal | M(n) | T(n) + funding | P2PKH outputs only |

Each τ must satisfy **contract evaluation**: the Script interpreter executes `T(n)`'s locking
script against τ's unlocking script and yields `true`.

**Covenant-executes-on-spend (read this before Lemmas 3–4).** A token's covenant runs when that
token is *spent*, so the checks a token enforces constrain the transaction that spends it. The two
token types alternate (Lemma 7): genesis and every settle produce a **settle-typed** token (even
`txoType`, e.g. `0x20`); every commit produces a **commit-typed** token (odd `txoType`, e.g. `0x21`).
Therefore:

- a **commit** spends a *settle-typed* token, **emits** the proof output(s), and enforces null
  ancestor args — it performs **no** rebuild;
- a **settle** spends a *commit-typed* token; when that token has a grandparent it **consumes** the
  grandparent's proof and **rebuilds** the grandparent (Lemma 3), binding the co-spent proof outpoint
  into `hashPrevouts`. The first settle (no grandparent) consumes no proof and rebuilds nothing.

So the ancestor-integrity check executes **at the settle** — the proof-consuming transition, inside
the commit-typed token's covenant — *not* at the commit. This is consistent with the table above (the
settle is the proof-*consuming* row). The contract flag named `hasBolt` (`SimpleMultiBolt.sx:330`,
`= txoType mod 2` on the *spent* type) gates this rebuild; despite its name it does not mark proof
*emission*, which sits on the complementary branch (`MSBolt.std.sx:130-134` emits the bolt when
spending a settle-typed token; `:182-298` rebuilds when spending a commit-typed token with a
grandparent). That naming is the origin of the historical commit/settle mislabel corrected in this
revision — see §1.6.

### 1.5 Token Chain

A **token chain** of length N is a sequence
`Γ = (T(0), τ₀, T(1), τ₁, …, τ_{N−1}, T(N))` where each `τ_i : T(i) → T(i+1)` is valid.

### 1.6 Scope, methodology, and what is *not* proven

This section states the boundary of the claim precisely, so the theorems below are read for
exactly what they establish — no more.

**Methodology.** What follows is a rigorous *hand* proof, paired with an executable test suite
(§9) that builds real transactions and runs them through the actual `@bsv/sdk` Script
interpreter. It is **not** a machine-checked proof — there is no Coq/Isabelle/Lean development.
The tests are strong evidence over the cases they cover (including raw-byte counterfeits that
*must* be rejected), but a passing suite demonstrates the covered branches; it is not a proof of
the absence of a covenant bug in an uncovered branch.

**Specification vs deployed bytecode.** The lemmas reason about the compiled covenant embedded in
`src/tokens/templates/SimpleMulti.sx.template.ts` (and the NFT analogues). Two facts bridge the
prose to the bytes that actually run:

1. **Enforcement is at layer-1.** On-chain, the exact deployed bytecode is executed and enforced
   by **miner transaction-script validation** as a consensus rule. There is no oracle, indexer,
   or trusted party anywhere in the enforcement path — a spend that does not satisfy the covenant
   is simply not a valid transaction. This is the same trust base as any other Bitcoin Script.
2. **The bytes are pinned in-repo.** The proof reasons about the exact compiled artifact this
   package ships — the ASM suffix embedded in the templates. That artifact is byte-frozen by the
   **template suites**, which assert each compiled lock byte-equals a vendored golden fixture (e.g.
   `test/templates/MinSimple.test.ts`); the scanner's `src/lib/scanner/fingerprints.ts` then derives a
   SHA-256 fingerprint of that frozen suffix for off-chain recognition. Any drift between the artifact
   the lemmas describe and the bytes the package ships fails a template test — so "the covenant" in this
   document and the covenant on the wire are the same bytes, without reference to any external toolchain.

**Out of scope — the two things a stablecoin most needs.** These are deliberately *not* claimed:

- **Supply-honesty.** Theorem 3 conserves balance *within a single genesis lineage*. It says
  **nothing** about how many independent genesis tokens an issuer mints. Unforgeability guarantees
  each unit is internally well-formed and traces to *an* issuer-signed mint; it does **not**
  guarantee the total float matches any reserve or stated cap. That is an issuer-behaviour /
  off-chain-reserve property, outside Bitcoin Script, and this proof cannot deliver it.
- **Network security.** As noted under Assumption 3, the anti-reorg guarantee inherits
  honest-majority hash power. On a low- or concentrated-hash-power chain that assumption is the
  dominant real-world risk, and it is imported, not proven.

In short: this document proves **third-party per-token unforgeability, ownership, per-genesis
balance conservation, and state-machine integrity** — conditional on the four assumptions of
§1.2. It does not prove issuer supply-honesty or network-level security.

**Relationship to the BOLT paper (`research/BOLT-Protocol.pdf`).** This document aligns to the
paper's **appendix code** (§10.1 `BoltNFT.sx`) and to the deployed contract — the objects miners
actually enforce. The paper's **prose** proof (§7.1) instead describes the ancestor rebuild as
happening on the odd/commit transition that *emits* a bolt. That localization is inconsistent with
the paper's own §10.1 code (whose `rebuildAncestor // txType && hasGrandparent` gate fires on the
proof-*consuming* settle) and with the deployed bytes, so this proof follows the **code**, not the
prose. The published paper is left unedited; this note records the discrepancy so the two are not
mistaken for equivalent. Earlier revisions of *this* document inherited the paper's prose localization
**and modelled a `genesisOutpoint` field the shipped covenant no longer carries** (removed in the `M-I`
refactor — genesis is now the derived parentless root, §1.3). Both are corrected here — §§1.3, 1.4, 3
(Lemmas 2–5, 7), 4 (Theorem 1), 6 and 8.1 — and the accessible companion
[`unforgeability.md`](unforgeability.md) is corrected in lockstep.

---

## 2. Security Properties

**Theorem 1 (Authenticity).** Every token `T(n)` in a valid chain Γ has a `parent`-chain that
terminates at a **unique parentless root** `T(0)` — its *genesis* (§1.3) — with
`issuer(T(n)) = issuer(T(0))`; and `T(0)` was created by the holder of `sk` such that
`H160(pk) = owner(T(0))` and `pk = issuer(T(0))`. (Equivalently `genesis(T(n)) = genesis(T(0))` in the
derived-root sense.)

**Theorem 2 (Ownership).** Given `T(n)`, no PPT adversary lacking the secret key `sk_n`
corresponding to `owner(T(n))` can produce a valid transition τ: T(n) → T(n+1).

**Theorem 3 (Balance Conservation, fungible).** For any valid chain Γ of fungible tokens, the
total balance over all live tokens sharing a common genesis is invariant except via melt:

    ∀ n: Σ balance(T_i) over live tokens at step n = balance(T(0))

> **Scope:** this is per-genesis conservation. It does **not** bound how many independent genesis
> tokens the issuer mints — i.e. unforgeability ≠ supply-honesty. See §1.6.

**Theorem 4 (State-Machine Integrity).** Every valid chain alternates commit and settle
transitions; no transition can skip a step or produce an invalid `txoType`.

---

## 3. Contract Invariants (Lemmas)

The covenant enforces the following on every spend.

### Lemma 1 (Signature Binding)
Every non-melt transition τ spending `T(n)` satisfies: (1) `H160(pubKey) = owner(T(n))`;
(2) `Verify(pubKey, ctx, sig) = 1` where `ctx` is the SIGHASH_ALL preimage; (3) the last byte
of `sig` is `0x41` (SIGHASH_ALL | SIGHASH_FORKID).

**Proof.** The covenant evaluates:
```
sig.lastByte == 0x41          // extraction + equalVerify
H160(pubKey) == pubKeyHash    // hash160 + equalVerify
checkSig(sig, pubKey)         // OP_CHECKSIG
```
SIGHASH_ALL commits the signature to all inputs and outputs. By Assumption 2 no adversary can
produce `(sig, pubKey)` satisfying these without `sk_n`. ∎

### Lemma 2 (Output Determinism)
For every non-melt τ: T(n) → T(n+1), the output `T(n+1)` is uniquely determined by contract
evaluation; no field can be chosen freely by the spender.

**Proof.** The covenant constructs the serialised outputs deterministically (`MSBolt.std.sx:141-157`):
- `parentOutpoint(n+1) = ctx.outpoint` (from the sighash preimage; `:147-148`);
- `grandparentOutpoint(n+1) = scriptCode.parentOutpoint` (`:149-150`);
- `issuerPubKey(n+1) = scriptCode.issuerPubKey`, copied verbatim — except at a genesis, where it is set
  to the signer's pubKey (`:152-156`; cf. Lemma 5);
- `balance(n+1) = f(scriptCode.balance, mode)` for a deterministic f (Lemma 6);
- `txoType(n+1)` is the parity-forced successor type (`:145-146`; Lemma 7);
- `owner(n+1)` is taken from unlock args but **locked** by `hashOutputs`;
- `contract(n+1) = scriptCode` (the covenant appends its own bytes; `:157`).

There is **no** `genesisOutpoint` field to copy (removed in `M-I`); lineage is carried entirely by the
`parent`/`grandparent` outpoints above. Then `H(serialised_outputs) == ctx.hashOutputs`. Since
SIGHASH_ALL binds `ctx.hashOutputs` to the actual outputs and H is collision-resistant (Assumption 1),
the outputs must equal the reconstructed bytes; any modification changes H and fails the equality. In
particular `parent(n+1)`/`grandparent(n+1)` are **determined, not spender-chosen** — the determinism
Theorem 1's induction relies on to walk lineage back to the genesis root. ∎

### Lemma 3 (Ancestor Integrity)
Ancestor integrity is enforced **at a settle** — i.e. when a *commit-typed* token that has a
grandparent is spent (§1.4). That spend's covenant (a) reconstructs the grandparent transaction
`TX_anc` from unlock arguments, size-validates every field, and verifies
`H(TX_anc) = grandparent.txid`; **and** (b) derives the grandparent's proof outpoint
`grandparentTxid ‖ voutLE` and binds it into the spend's `hashPrevouts`, forcing that proof UTXO to
be co-spent. Part (a) proves the claimed grandparent has exactly the reconstructed structure; part
(b) forces a **currently-unspent (UTXO)** output of it to be consumed — upgrading (a) from "a
transaction with this txid could exist" to "a real, still-live output of it is spent here, enforced by
miners against the UTXO set."

**Proof.** `TX_anc` is rebuilt byte-by-byte: version (4 B), input count (VarInt), each input
(outpoint 36 B, scriptSig via length-prefixed cat, nSequence 4 B), output count (VarInt), each
output (value 8 B, script reconstructed from individually size-checked fields — **including the
grandparent's own proof output**), nLockTime (4 B). The check
`H(TX_anc).first256 == grandparent.txid` holds only for the genuine ancestor; any `TX_anc' ≠ TX_anc`
satisfying it is a collision (Assumption 1). The co-spend in (b) is enforced because the derived
proof outpoint is concatenated into the reconstructed `prevOuts` whose hash is asserted equal to
`ctx.hashPrevouts`; omitting or substituting that input changes the hash and fails. In the contract
this is the `rebuildAncestor` block gated on `txoType(commit-typed) && hasGrandparent`
(`MSBolt.std.sx:182-298`; proof-outpoint derivation `:294-298`; `hashPrevouts` weld `:308-312`;
fungible `SimpleMultiBolt.sx:493`; driver `MultiBOLT.ts:108-146` sources the proof from
`prevTxs[len-3]`).

Parts (a)+(b) defeat a **spliced** ancestor (substituting a different transaction for the committed
`grandparent.txid`, or omitting the co-spend). They do **not** by themselves defeat a **fabricated**
lineage (a chain an adversary builds from scratch, choosing each txid): that is precluded instead by
Lemma 5 (the parentless root must be issuer-signed) plus the requirement that every hop consume the
*real* predecessor UTXO. For a **merge** settle (two token inputs) the rebuild generalises to **two**
ancestors (`ancestorTxA`, `ancestorTxB`), and the second input's lineage is bound via
`otherGrandparentOutpoint`, so a merge cannot fuse a token from an unrelated or forged lineage. (A split
has a single token input, so it uses the single-ancestor rebuild above.) ∎

> **Localization (corrected 2026-07-01).** Earlier revisions stated this rebuild happened "at the
> commit." That was wrong: a token's covenant runs at its *spend*, and the rebuild lives in the
> *commit-typed* token's covenant, which is spent by the **settle**. This matches the §1.4 transition
> table (the settle is the proof-*consuming* transition) and the deployed bytes. A consequence worth
> stating: the proof co-spend of (b) is **part of** ancestor integrity, not an independent liveness
> marker — so a settle cannot be treated as pure field-propagation. See §1.6.

### Lemma 4 (Null-Ancestor Enforcement)
When the rebuild is not triggered — i.e. on a **commit** (spending a settle-typed token) or on a
grandparent-less spend (the first settle, or n < 2) — all ancestor unlock arguments must be
zero-length.

**Proof.** The covenant concatenates every ancestor field and asserts the total size is `0`
(`… cat … size nip 0 equalVerify`, `MSBolt.std.sx:300-304`). Any non-null field makes the size
positive and fails the check, preventing injection of fabricated ancestor data when no rebuild is
required. (Corrected localization: the non-rebuild case is the **commit** / grandparent-less spend,
not "a settle" — a settle with a grandparent is exactly where the Lemma 3 rebuild fires.) ∎

### Lemma 5 (Issuer Enforcement)
For the genesis transaction (n = 0) and the first transfer commit (n = 1), the signer's public
key must equal the embedded `issuerPubKey`.

**Proof.** The covenant derives `isGenesis = (parentOutpoint == ∅)` — a token is a genesis iff it is
**parentless** (`MSBolt.std.sx:93`, `SimpleMultiBolt.sx:297`) — and a first-commit flag, and under
either asserts `issuerPubKey == pubKey` (`SimpleMultiBolt.sx:298`). This forces the minting key to
authorise both the genesis root and the first commit (whose first commit may not be a merge —
`SimpleMultiBolt.sx:299`); after the first settle the check is lifted, enabling ordinary transfers. ∎

### Lemma 6 (Balance Determinism, fungible)
The output balance is a deterministic function of the input balance(s), computed with 16-byte
little-endian arithmetic:

| Transition | Output balance |
|-----------|----------------|
| Transfer (commit/settle) | `balance(n+1) = balance(n)` |
| Merge settle | `balance(n+1) = balance(n) + otherBalance` |
| Split settle | `balance_A(n+1) = balance(n) − piece`, `balance_B(n+1) = piece` |

**Proof.** Each case is built into the covenant's output construction and locked by `hashOutputs`
(Lemma 2). Merge commit enforces `balance + otherBalance ≤ 2¹²⁸ − 1` (no overflow); split commit
enforces `balance ≥ piece ≥ 0` (no negative/over-take). No other value satisfies
`H(serialised_outputs) == ctx.hashOutputs`. ∎

### Lemma 7 (State Machine)
The `txoType` field enforces strict alternation of token types: a **commit-typed** token (odd) is
followed only by its matching **settle-typed** token (even); a **settle-typed** token (even) is
followed only by some commit-typed token (odd). Evaluated when a token is spent — `txoType` is the
*spent* token's type, `nextTxoType` the *produced* token's type:

```
spentIsCommitTyped = txoType mod 2       // odd ⇒ spending a commit-typed token ⇒ this τ is a settle
if spentIsCommitTyped: assert nextTxoType == txoType − 1   // commit-typed → its matching settle-typed
else:                  assert nextTxoType mod 2 == 1        // settle-typed → some commit-typed
```

This forbids two commit-typed or two settle-typed tokens in a row, i.e. it forbids skipping the
commit→settle cycle. The types in use are `{0x20 transfer-settle/genesis, 0x21 transfer-commit,
0x22 split-settle, 0x23 split-commit, 0x24 merge-settle, 0x25 merge-commit}`. (Naming: spending a
*commit-typed* token **is** the settle transition — §1.4; the parity test classifies the spent
*token type*, not the transition.) ∎

---

## 4. Proof of Theorem 1 (Authenticity)

By strong induction on chain length N. The inductive **invariant** for `T(k)` is: its `parent`-chain is
well-formed (each `parent`/`grandparent` outpoint is the *determined* real predecessor), it terminates at
a unique **parentless** root, and `issuer(T(k))` is that root's issuer.

**Base case (N = 0).** `T(0)` is a **genesis**: it is parentless (`parent(T(0)) = ⊥`, Lemma 5), so it
*is* the root. By Lemma 5 the signer's pubKey equals `issuerPubKey`; by Lemma 1 only the holder of the
matching `sk` can sign. `T(0)`'s identity is its own transaction's txid, bound to a real transaction by
proof-of-work (Assumption 3). Thus `T(0)` is authentic and is its own genesis.

**Base case (N = 1).** `T(1)` is produced by the first commit spending `T(0)`. By Lemma 5 the issuer
must sign; by Lemma 2 the output fields are deterministic (`parent(T(1)) = outpoint(T(0))`,
`issuer(T(1)) = issuer(T(0))`); Lemma 4 forces the ancestor args null (no grandparent). `hashOutputs`
locks `T(1)`. So `T(1)`'s parent is exactly `T(0)` and its chain terminates at the genesis root `T(0)`.
`T(1)` is authentic.

**Inductive step.** Assume `T(0), …, T(n)` authentic; prove `T(n+1)` authentic. `τ_n` spends `T(n)`, so
its class is fixed by `T(n)`'s type (§1.4). In **both** cases Lemma 2 makes the produced fields
deterministic — in particular `parent(T(n+1)) = outpoint(T(n))` and `issuer` copied verbatim — so
`T(n+1)`'s chain extends `T(n)`'s by one real link and inherits the same issuer and root.

*Case 1: τ_n is a commit (`T(n)` settle-typed).* No rebuild runs (Lemma 4 forces null ancestor args).
`T(n+1)`'s `parent`/`grandparent`/`issuer` are the deterministic Lemma-2 outputs of `T(n)`'s scriptCode,
which by hypothesis are well-formed; they propagate. The commit additionally *emits* the proof output
consumed later by its matching settle (§1.4). `T(n+1)` is authentic.

*Case 2: τ_n is a settle (`T(n)` commit-typed) with a grandparent.* By Lemma 2, `grandparent(T(n))` is
the **determined** outpoint `outpoint(T(n−2))` (not spender-chosen); by hypothesis `T(n−2)` is authentic.
By Lemma 3 the rebuild yields `TX_anc` with `H(TX_anc) = grandparent(T(n)).txid`, so `TX_anc` is
`T(n−2)`'s transaction up to collision probability `negl(λ)`, **and** it forces a still-**unspent** output
of that transaction (its proof UTXO) to be co-spent — proving on-chain that the claimed grandparent is a
*real* transaction, not a spliced or omitted one. `T(n+1)`'s fields are the deterministic Lemma-2 outputs.
(The first settle has no grandparent: Lemma 4 applies and authenticity propagates by Lemma 2 as in Case 1.)

In both cases Lemma 1 ensures the transition was authorised. **Where authenticity comes from:** Lemma 2's
`parent`-chain determinism makes the lineage well-defined; **Lemma 5** anchors it — the only parentless
token is issuer-signed, so the chain cannot terminate at a root an adversary chose; and **Lemma 3**
(rebuild + proof co-spend) is what makes each deep ancestor *provably real on-chain* rather than assumed,
defeating a spliced or omitted ancestor and letting a verifier confirm the two deepest links from
**bounded** data — the token UTXO plus the co-spent proof UTXO, each with a merkle proof (the paper's
"two related UTXOs" back-to-genesis argument, §1.6). Genesis-preservation via Lemma 2 alone would
establish the property only over an *already-valid* chain; it is the combination of **Lemma 5** (issuer
root), **Lemma 3** (real-ancestor consumption at each settle) and **Lemma 1** (per-hop authorisation) that
reduces forgery to breaking ECDSA (Assumption 2) or SHA-256 (Assumption 1) — consistent with §8.1 and §10. ∎

---

## 5. Proof of Theorem 2 (Ownership)

Let `owner(T(n)) = H160(pk_n)`. By Lemma 1 any τ: T(n) → T(n+1) requires a `pk` with
`H160(pk) = owner(T(n))`, a valid ECDSA `sig` with `Verify(pk, ctx, sig) = 1`, and sighash byte
`0x41`. By Assumption 2, producing such `(pk, sig)` without `sk_n` is negligible. SIGHASH_ALL
commits the signature to all outputs, so an adversary cannot redirect the token after signing.
The melt path performs the same `H160` + `checkSig` check, so a non-owner cannot melt. ∎

---

## 6. Proof of Theorem 3 (Balance Conservation, fungible)

Define `B(n) = Σ balance(T_i)` over all live tokens sharing a genesis — i.e. whose `parent`-chains
terminate at the same parentless, issuer-signed root (§1.3). By case analysis:

- **Transfer.** Balance unchanged (Lemma 6); one token in, one out. `B(n+1) = B(n)`.
- **Merge.** Two live tokens `T_a, T_b` (both spent as inputs) yield one `T_merged` with
  `balance = balance(T_a) + balance(T_b)` (Lemma 6). Before and after, B contains the same sum;
  both inputs are consumed and cannot be respent (UTXO model). `B(n+1) = B(n)`. The commit
  enforces the sum `≤ 2¹²⁸ − 1`, and the settle binds the two inputs to a **common lineage** via
  `otherGrandparentOutpoint` (Lemma 3), so a merge cannot pull in a token from a different or forged
  genesis to inflate this float.
- **Split.** One token `T` yields `T_a', T_b'` with
  `balance(T_a') + balance(T_b') = (balance(T) − piece) + piece = balance(T)` (Lemma 6). The
  commit enforces `balance(T) ≥ piece ≥ 0`. `B(n+1) = B(n)`.
- **Melt.** The token is destroyed with no token output; B decreases by `balance(T)`. This is the
  only authorised reduction and requires the owner's signature (Theorem 2).

Therefore, excluding melt, `B(n) = B(0)` for all n. ∎

This conserves the float of *one* genesis lineage. It is **not** a statement about the issuer's
total supply: an issuer may mint any number of independent genesis tokens, each with its own
`B(0)`, and this theorem says nothing about their sum. Supply-honesty is an off-chain / issuer
property (§1.6), not a Script invariant.

---

## 7. Proof of Theorem 4 (State-Machine Integrity)

By Lemma 7 each transition enforces: from a commit (odd) the next type is `txoType − 1` (its
matching settle); from a settle (even) the next type is odd (some commit). This yields a strict
alternation C → S → C → S → …. Genesis starts at `0x20` (settle-like), forcing the first
transition to be a commit. Valid edges:

```
0x20 (transfer-settle / genesis) → 0x21 or 0x23 or 0x25   (any commit mode)
0x21 (transfer-commit)           → 0x20
0x22 (split-settle)              → 0x21 or 0x23 or 0x25
0x23 (split-commit)              → 0x22
0x24 (merge-settle)              → 0x21 or 0x23 or 0x25
0x25 (merge-commit)              → 0x24
```

Each commit has exactly one valid settle successor; each settle may enter any commit mode. No
state permits skipping the cycle or an undefined type. ∎

---

## 8. Comprehensive Attack Analysis

### 8.1 Forgery (against Theorem 1)

| Attack | Method | Defence | Reduction |
|--------|--------|---------|-----------|
| Forge genesis | claim lineage to a reputable issuer's root | the unique parentless root must be issuer-signed (`issuerPubKey == signerPubKey`, Lemma 5); without the issuer key no valid root exists | Asm. 2 |
| Forge ancestor | supply `TX_anc' ≠ TX_anc` with same hash | `H(TX_anc') = H(TX_anc)` needs a collision | Asm. 1 |
| Inject ancestor data on a non-rebuild spend | non-null ancestor args on a commit or grandparent-less settle | null-check asserts total size 0 (Lemma 4) | Asm. 4 |
| Modify lineage fields | change parent/grandparent in output | `hashOutputs` locks all output bytes (Lemma 2) | Asm. 1 |
| Modify contract suffix | swap in different bytecode | covenant appends its own bytes to the output; hash mismatch | Asm. 1 |

### 8.2 Ownership (against Theorem 2)

| Attack | Method | Defence | Reduction |
|--------|--------|---------|-----------|
| Wrong-key spend | sign with `sk' ≠ sk_n` | `H160(pk') ≠ owner`; equalVerify fails | Asm. 2 |
| Signature malleability | mangle a valid sig | SIGHASH_ALL + ECDSA canonical form | Asm. 2 |
| Replay signature | reuse `sig` on another tx | SIGHASH_ALL commits to this tx's preimage | Asm. 2 |
| Wrong sighash flag | SIGHASH_NONE / SINGLE / ACP | covenant asserts last byte `== 0x41` | Asm. 4 |
| Melt by non-owner | melt with wrong key | same `H160` + `checkSig` on the melt path | Asm. 2 |

### 8.3 Balance (against Theorem 3, fungible)

| Attack | Method | Defence | Reduction |
|--------|--------|---------|-----------|
| Inflate on merge | claim sum > actual | sum computed in-script; locked by `hashOutputs` | Asm. 1 + 4 |
| Over-take on split | claim piece > whole | covenant asserts `balance ≥ piece ≥ 0` | Asm. 4 |
| Overflow on merge | exceed 2¹²⁸ − 1 | covenant asserts sum within range before settle | Asm. 4 |
| Double-spend | reuse the same UTXO | Bitcoin UTXO consensus | Consensus |
| Balance byte tamper | edit balance in the output script | `hashOutputs` commitment (Lemma 2) | Asm. 1 |

### 8.4 State Machine (against Theorem 4)

| Attack | Method | Defence |
|--------|--------|---------|
| Double commit | commit from a commit output | parity: odd → must produce even |
| Skip settle | settle → settle | parity: even → must produce odd |
| Invalid txoType | undefined type byte | only `0x20–0x25` match the covenant's checks |
| Mode confusion | merge where transfer expected | `nextTxoType` must match the specific commit value |

### 8.5 Output Manipulation

| Attack | Method | Defence | Reduction |
|--------|--------|---------|-----------|
| Extra output | append unauthorised output | changes `serialised_outputs`; hash mismatch | Asm. 1 |
| Missing proof | omit proof output on a commit | changes `serialised_outputs`; hash mismatch | Asm. 1 |
| Reorder outputs | swap token/proof positions | covenant fixes output order; hash mismatch | Asm. 1 |
| Modify output value | change 1 sat → N sat | covenant asserts `ctx.value == 1`; also `hashOutputs` | Asm. 4 + 1 |
| **Off-chain look-alike** | a non-covenant script with the right push shape | `recognizeType` requires the static-code SHA-256 to match too | Asm. 1 |

The last row is the **off-chain recognizer**'s contribution: on-chain the covenant is
self-enforcing, but a scanner inspecting third-party transactions also rejects a script that
copies a token's field layout yet carries different code, because the suffix hash differs.

---

## 9. Empirical Validation

Every property above is exercised by this package's test suite — **126 tests across 18 files**
that build *real* Bitcoin transactions and verify them against the actual `@bsv/sdk` Script
interpreter (no mocks). Run `npm test`.

| Suite (file) | Validates |
|--------------|-----------|
| `test/tokens/MultiBOLT.test.ts`, `test/templates/SimpleMulti.test.ts` | Full `SimpleMultiBOLT` lifecycles (mint → transfer×2 → split; mint×2 → merge → melt) build real txs and verify on the `@bsv/sdk` Spend engine; split/merge conserve balance (Theorem 3, Lemma 6). |
| `test/templates/MinSimple.test.ts`, `MinSimpleBalance.test.ts`, `MinSimpleDiscount.test.ts` | NFT lock/unlock/melt; each lock **byte-equals its golden fixture**; immutable balance/discount fields. |
| `test/lib/singleAncestor.test.ts`, `singleSpend.test.ts`, `singleCoupon.test.ts`, `multiBoltLib.test.ts` | Multi-hop chains: commit→settle verify on the Spend engine and the rebuilt ancestor matches the real grandparent txid (Lemma 3). |
| `test/scanner/verifyEvents.test.ts` | **Negative tests:** rejects a wrong trusted issuer, an orphan settle (chain missing its commit), an unsettled commit, an extra-`OP_RETURN`-tampered output, and a right-shape/wrong-code counterfeit; accepts a lone genesis mint as a single-tx event (Theorem 1, §8.1/§8.5). |
| `test/scanner/parity.test.ts`, `events.test.ts`, `fingerprints.test.ts` | Scanner accept/reject **matches the on-chain contract** (parity); commit/settle event classification; fingerprint registry + p2Proof golden matching against tampered inputs (Theorems 1 & 4, §8.5). |
| `test/lib/boltLib.test.ts`, `branches.test.ts`, `test/tokens/BOLT.test.ts`, `test/templates/pay2Proof.test.ts`, `test/releasable.test.ts` | Shared layout-agnostic primitives (`splitCtx`, outpoint/output serialisers, `verifyTx` guards), default-value/guard branches, the abstract base contract, the `pay2Proof` marker output, and the release gate. |
| `test/helpers/counterfeit.ts` | Constructs counterfeits at the **raw-byte (on-wire)** level — exactly as an attacker would — so rejection is proven independent of SDK behaviour. |

**Negative tests must fail; positive tests must hold.** All 126 pass, 0 skipped.

---

## 10. Conclusion

Under standard assumptions — SHA-256 collision resistance, ECDSA existential unforgeability,
blockchain finality, and script-execution correctness — we have proven for the contracts shipped
in this package:

1. **No token can be forged.** Every token traces an unbroken, hash-verified chain to its
   issuer-signed genesis; inserting a forged transaction requires a SHA-256 collision (Thm 1).
2. **No token can be stolen.** Spending requires a valid owner ECDSA signature; SIGHASH_ALL
   prevents post-signing modification (Thm 2).
3. **No balance can be inflated or stolen.** Transfer preserves, merge sums exactly, split
   conserves — all enforced in-script and locked by `hashOutputs` (Thm 3).
4. **No protocol step can be skipped.** The `txoType` machine enforces strict commit/settle
   alternation (Thm 4).

The proof of authenticity lives entirely within Bitcoin Script, secured by proof-of-work, with
**no oracle, trusted party, or off-chain state** in the trust base. Counterfeiting a BOLT token
is reducible to breaking SHA-256 or ECDSA. ∎

These four results are the whole claim. They establish **third-party per-token unforgeability**;
they do **not** establish issuer supply-honesty or network-level security, and this is a hand
proof validated by tests rather than a machine-checked one — see §1.6 for the exact boundary.

---

*Adapted for the `b017` package (SimpleMultiBOLT, 16-byte balance, no swap; minimal NFT
templates). Validated against the package's 126 automated tests. The covenant is the compiled
artifact embedded in `src/tokens/templates/`, byte-pinned in-repo by the golden fingerprints of
§9; on-chain it is enforced by miner transaction-script validation at layer-1.*
