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
> `src/templates/SimpleMulti.sx.template.ts` (and the NFT analogues); the line-level contract
> source lives in the BOLT protocol repository.

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

**Assumption 4 (Script Correctness).** The Bitcoin Script virtual machine is a deterministic
state machine that correctly evaluates all opcodes per consensus rules. (In this library the
same scripts are independently re-verified by the `@bsv/sdk` Spend engine — see §9.)

### 1.3 Token State

A **BOLT token state** at step n is a tuple:

    T(n) = (owner(n), parent(n), grandparent(n), genesis, issuer, balance(n), contract)

Where:
- `owner(n) ∈ {0,1}¹⁶⁰` — `H160(pubKey)`, the current owner's public-key hash.
- `parent(n) ∈ {0,1}²⁵⁶ × ℕ` — `(txid, vout)` of `T(n−1)`.
- `grandparent(n) ∈ {0,1}²⁵⁶ × ℕ ∪ {⊥}` — `(txid, vout)` of `T(n−2)`, or `⊥` if n < 2.
- `genesis ∈ {0,1}²⁵⁶ × ℕ` — `(txid, vout)` of `T(0)`. **Immutable.**
- `issuer ∈ {0,1}²⁶⁴` — compressed public key of the issuing authority. **Immutable.**
- `balance(n) ∈ [0, 2¹²⁸ − 1]` — **16-byte little-endian** balance (fungible `SimpleMultiBOLT`;
  for the plain NFT this field is absent or fixed; `MinSimpleBalance` carries an immutable
  16-byte balance, `MinSimpleDiscount` an immutable 1-byte discount).
- `contract ∈ {0,1}*` — the BOLT locking-script bytecode (self-referential, immutable).

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

### 1.5 Token Chain

A **token chain** of length N is a sequence
`Γ = (T(0), τ₀, T(1), τ₁, …, τ_{N−1}, T(N))` where each `τ_i : T(i) → T(i+1)` is valid.

---

## 2. Security Properties

**Theorem 1 (Authenticity).** Every token `T(n)` in a valid chain Γ satisfies
`genesis(T(n)) = genesis(T(0))`, and `T(0)` was created by the holder of `sk` such that
`H160(pk) = owner(T(0))` and `pk = issuer(T(0))`.

**Theorem 2 (Ownership).** Given `T(n)`, no PPT adversary lacking the secret key `sk_n`
corresponding to `owner(T(n))` can produce a valid transition τ: T(n) → T(n+1).

**Theorem 3 (Balance Conservation, fungible).** For any valid chain Γ of fungible tokens, the
total balance over all live tokens sharing a common genesis is invariant except via melt:

    ∀ n: Σ balance(T_i) over live tokens at step n = balance(T(0))

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

**Proof.** The covenant constructs the serialised outputs deterministically:
- `parentOutpoint(n+1) = ctx.outpoint` (from the sighash preimage);
- `grandparentOutpoint(n+1) = scriptCode.parentOutpoint`;
- `genesisOutpoint(n+1) = scriptCode.genesisOutpoint` (or `ctx.outpoint` at genesis);
- `issuerPubKey(n+1) = scriptCode.issuerPubKey` (copied verbatim);
- `balance(n+1) = f(scriptCode.balance, mode)` for a deterministic f (Lemma 6);
- `owner(n+1)` is taken from unlock args but **locked** by `hashOutputs`;
- `contract(n+1) = scriptCode` (the covenant appends its own bytes).

Then `H(serialised_outputs) == ctx.hashOutputs`. Since SIGHASH_ALL binds `ctx.hashOutputs` to
the actual outputs and H is collision-resistant (Assumption 1), the outputs must equal the
reconstructed bytes; any modification changes H and fails the equality. ∎

### Lemma 3 (Ancestor Integrity)
For every commit transition at step n ≥ 2, the covenant reconstructs the ancestor transaction
`TX_anc` (the commit two steps back) from unlock arguments, size-validates every field, and
verifies `H(TX_anc) = grandparent(T(n)).txid`.

**Proof.** `TX_anc` is rebuilt byte-by-byte: version (4 B), input count (VarInt), each input
(outpoint 36 B, scriptSig via length-prefixed cat, nSequence 4 B), output count (VarInt), each
output (value 8 B, script reconstructed from individually size-checked fields), nLockTime (4 B).
The final check `H(TX_anc).first256 == grandparent(T(n)).txid` holds only for the genuine
ancestor; any `TX_anc' ≠ TX_anc` satisfying it is a collision (Assumption 1). ∎

### Lemma 4 (Null-Ancestor Enforcement)
When ancestor rebuild is not triggered (n < 2, or a settle), all ancestor unlock arguments
must be zero-length.

**Proof.** The covenant concatenates every ancestor field and asserts the total size is `0`
(`… cat … size nip 0 equalVerify`). Any non-null field makes the size positive and fails the
check, preventing injection of fabricated ancestor data when no rebuild is required. ∎

### Lemma 5 (Issuer Enforcement)
For the genesis transaction (n = 0) and the first transfer commit (n = 1), the signer's public
key must equal the embedded `issuerPubKey`.

**Proof.** The covenant computes `isGenesis = (genesisOutpoint == ∅)` and a first-commit flag,
and under either asserts `issuerPubKey == pubKey`. This forces the minting key to authorise both
genesis and the first commit; after the first settle the check is lifted, enabling ordinary
transfers. ∎

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
The `txoType` field enforces alternation between commit (odd) and settle (even):

```
hasProof = txoType mod 2                 // odd = a commit
if hasProof:  assert nextTxoType == txoType − 1   // commit → matching settle
else:         assert nextTxoType mod 2 == 1        // settle → some commit
```

This forbids commit→commit (odd→odd) and settle→settle (even→even). The types in use are
`{0x20 transfer-settle/genesis, 0x21 transfer-commit, 0x22 split-settle, 0x23 split-commit,
0x24 merge-settle, 0x25 merge-commit}`. ∎

---

## 4. Proof of Theorem 1 (Authenticity)

By strong induction on chain length N.

**Base case (N = 0).** `T(0)` is genesis. By Lemma 5 the signer's pubKey equals `issuerPubKey`;
by Lemma 1 only the holder of the matching `sk` can sign. `genesis(T(0)) = ctx.outpoint` is set
by the covenant from the sighash preimage and bound to the actual transaction by SIGHASH_ALL.
Thus `T(0)` is authentic and its genesis is cryptographically committed.

**Base case (N = 1).** `T(1)` is produced by the first commit. By Lemma 5 the issuer must sign;
by Lemma 2 the output fields are deterministic (`parent(T(1)) = outpoint(T(0))`,
`genesis(T(1)) = genesis(T(0))`); Lemma 4 forces the ancestor args null. `hashOutputs` locks
`T(1)`. Thus `T(1)` is authentic.

**Inductive step.** Assume `T(0), …, T(n)` authentic; prove `T(n+1)` authentic.

*Case 1: τ_n is a settle.* By Lemma 2, `T(n+1)`'s fields are deterministic from `T(n)`'s
scriptCode, which (by hypothesis) carries the correct parent/grandparent/genesis; these
propagate to `T(n+1)`. Lemma 4 prevents ancestor injection.

*Case 2: τ_n is a commit, n ≥ 2.* By Lemma 3 the rebuild yields `TX_anc` with
`H(TX_anc) = grandparent(T(n)).txid`. Since `T(n)` is authentic, `grandparent(T(n))` points to
`T(n−2)`, authentic by hypothesis; hence `TX_anc = T(n−2)` up to collision probability
`negl(λ)`. By Lemma 2, `T(n+1)`'s fields are correctly derived and
`genesis(T(n+1)) = … = genesis(T(0))`.

In both cases Lemma 1 ensures the transition was authorised. ∎

---

## 5. Proof of Theorem 2 (Ownership)

Let `owner(T(n)) = H160(pk_n)`. By Lemma 1 any τ: T(n) → T(n+1) requires a `pk` with
`H160(pk) = owner(T(n))`, a valid ECDSA `sig` with `Verify(pk, ctx, sig) = 1`, and sighash byte
`0x41`. By Assumption 2, producing such `(pk, sig)` without `sk_n` is negligible. SIGHASH_ALL
commits the signature to all outputs, so an adversary cannot redirect the token after signing.
The melt path performs the same `H160` + `checkSig` check, so a non-owner cannot melt. ∎

---

## 6. Proof of Theorem 3 (Balance Conservation, fungible)

Define `B(n) = Σ balance(T_i)` over all live tokens sharing a genesis. By case analysis:

- **Transfer.** Balance unchanged (Lemma 6); one token in, one out. `B(n+1) = B(n)`.
- **Merge.** Two live tokens `T_a, T_b` (both spent as inputs) yield one `T_merged` with
  `balance = balance(T_a) + balance(T_b)` (Lemma 6). Before and after, B contains the same sum;
  both inputs are consumed and cannot be respent (UTXO model). `B(n+1) = B(n)`. The commit
  enforces the sum `≤ 2¹²⁸ − 1`.
- **Split.** One token `T` yields `T_a', T_b'` with
  `balance(T_a') + balance(T_b') = (balance(T) − piece) + piece = balance(T)` (Lemma 6). The
  commit enforces `balance(T) ≥ piece ≥ 0`. `B(n+1) = B(n)`.
- **Melt.** The token is destroyed with no token output; B decreases by `balance(T)`. This is the
  only authorised reduction and requires the owner's signature (Theorem 2).

Therefore, excluding melt, `B(n) = B(0)` for all n. ∎

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
| Forge genesis | fake genesis outpoint | genesis = `ctx.outpoint`, bound by SIGHASH_ALL to the real tx | Asm. 3 |
| Forge ancestor | supply `TX_anc' ≠ TX_anc` with same hash | `H(TX_anc') = H(TX_anc)` needs a collision | Asm. 1 |
| Inject ancestor data on settle | non-null ancestor args | null-check asserts total size 0 (Lemma 4) | Asm. 4 |
| Modify lineage fields | change parent/grandparent/genesis in output | `hashOutputs` locks all output bytes (Lemma 2) | Asm. 1 |
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

Every property above is exercised by this package's test suite — **43 tests** that build *real*
Bitcoin transactions and verify them against the actual `@bsv/sdk` Script interpreter (no mocks).
Run `npm test`.

| Suite (file) | Validates |
|--------------|-----------|
| `test/no-elas.test.ts` | Full `SimpleMultiBOLT` lifecycles (mint → transfer×2 → split; mint×2 → merge → melt) verify on `@bsv/sdk` alone (P1–P4). |
| `test/min-simple-bolt.template.test.ts`, `min-balance-bolt.template.test.ts`, `min-discount-bolt.template.test.ts` | NFT lock/unlock/melt; immutable balance/discount fields. |
| `test/nft-ancestor.test.ts`, `min-nft-coupon.test.ts`, `min-nft-spend.test.ts` | Ancestor reconstruction across multi-hop chains (Lemma 3). |
| `test/scan.test.ts` | **Negative tests:** rejects a wrong trusted issuer, a chain missing its commit, a mint-only chain, an extra-`OP_RETURN`-tampered output, and a right-shape/wrong-code counterfeit (Theorem 1, §8.1/§8.5). |
| `test/scan-parity.test.ts`, `scan-events.test.ts`, `fingerprints.test.ts` | Recognition, commit/settle event classification, fingerprint matching against tampered inputs (Theorem 4, §8.5). |
| `test/counterfeit.helper.ts` | Constructs counterfeits at the **raw-byte (on-wire)** level — exactly as an attacker would — so rejection is proven independent of SDK behaviour. |

**Negative tests must fail; positive tests must hold.** All 43 pass, 0 skipped.

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

---

*Adapted for the `b017` package (SimpleMultiBOLT, 16-byte balance, no swap; minimal NFT
templates). Validated against the package's 43 automated tests. Contract source of truth: the
BOLT protocol repository; compiled artifacts embedded in `src/templates/`.*
