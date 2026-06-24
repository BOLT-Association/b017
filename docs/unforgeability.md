# Why b017 tokens cannot be counterfeited

This document explains the security claim at the heart of the library: a valid BOLT token
chain, from its genesis mint to any later state, **cannot be forged, duplicated, or inflated
without breaking SHA-256 or ECDSA.** No trusted third party, oracle, or off-chain index is
required for the guarantee — it is enforced by the Bitcoin Script covenant the token is locked
under, and secured by the network's proof-of-work.

The argument below is the accessible form. For the rigorous treatment — formal model,
hardness assumptions, 4 theorems, 7 lemmas, and an enumerated attack-vector analysis — see
[`formal-proof.md`](formal-proof.md). This file is written to stand on its own for a reader of
*this* library.

> **Scope.** "Cannot be counterfeited" means: you cannot create a token that *appears* to
> descend from a genuine issuer's mint when it does not, nor change ownership or balance
> outside the rules. It does **not** mean a holder can be stopped from *destroying* their own
> token (that is the melt path), and it is **not** a claim about double-spending — preventing
> two conflicting spends of the same UTXO is the Bitcoin network's job, not the contract's.

---

## 1. Threat model — what a counterfeiter would try

A counterfeiter wants one of:

1. **Forge a genesis** — produce a token that claims a lineage to a reputable issuer it never had.
2. **Splice the chain** — insert a fabricated intermediate transaction so a token's history
   looks valid while hiding an illegitimate jump.
3. **Inflate a balance** (fungible) — make a merge sum to more, or a split take more, than the
   inputs actually held.
4. **Steal a token** — spend a token you do not own.
5. **Break the protocol's state machine** — e.g. skip the commit→settle handshake to confuse
   downstream validators.
6. **Fool the off-chain recognizer** — hand a verifier a script that *looks* like a b017 token
   (right field shape) but runs different code.

Each is blocked. Sections 3–4 show how.

---

## 2. What a token actually is

A b017 token is a 1-satoshi UTXO whose locking script is the BOLT covenant followed by a set
of **data fields** carried in the script itself:

- `issuerPubKey` — the minting key. **Immutable** for the life of the chain.
- `genesisOutpoint` — the outpoint of the mint transaction. **Immutable.**
- `parentOutpoint`, `grandparentOutpoint` — the previous one and two steps of the chain.
- `pubKeyHash` — the current owner.
- `balance` — a 16-byte little-endian value (fungible `SimpleMultiBOLT`; the NFT templates
  carry no balance, or a fixed one).
- the **contract code itself** (the covenant is self-referential — it can read its own bytes).

State advances in a **commit → settle** pair. The contract tags each output with a `txoType`
byte; commits are odd (`0x21` transfer, `0x23` split, `0x25` merge) and settles are even
(`0x20` transfer/genesis, `0x22` split, `0x24` merge). The parity *is* the state machine.

---

## 3. The dual hash-commitment that makes lineage tamper-proof

Every spend of a token must satisfy **two independent hash commitments**, both checked inside
the locking script against the transaction's own sighash preimage:

### Commitment 1 — forward binding (`hashOutputs`)

The covenant *reconstructs* the exact next token output it expects — including the new owner,
the inherited `issuerPubKey`/`genesisOutpoint`, the updated lineage outpoints, and the balance
— serialises it, and asserts:

```
hash256(reconstructed_outputs) == ctx.hashOutputs
```

Because the signature is **SIGHASH_ALL**, the signer is committed to *all* outputs; nothing can
be altered after signing. This nails the **forward** state: you cannot produce a next token
whose fields differ from what the rules dictate.

### Commitment 2 — backward binding (ancestor rebuild)

On every commit, the covenant rebuilds the **ancestor transaction two steps back** from
unlock-time arguments, validates every field's size, hashes it, and asserts:

```
hash256(reconstructed_ancestor) == grandparentOutpoint.txid
```

The only way this passes is if the rebuilt bytes *are* the genuine ancestor transaction —
because its txid was fixed into `grandparentOutpoint` two steps earlier and is secured by
proof-of-work. Substituting a fabricated ancestor would require a **SHA-256 collision**.

**Together:** Commitment 1 locks the chain going forward, Commitment 2 proves the chain going
backward. A token at depth *N* therefore carries an implicit cryptographic proof of every
transaction back to genesis.

---

## 4. The inductive argument

**Base case (mint).** The mint sets `genesisOutpoint = ctx.outpoint` (its own on-chain
outpoint) and enforces `issuerPubKey == signerPubKey`. So genesis is authentic by construction,
and its identity is bound to a real transaction hash that proof-of-work secures.

**Inductive step.** Assume every token up to step *n* is authentic. A spend producing step
*n+1* must satisfy Commitment 1 (so its `issuerPubKey`/`genesisOutpoint` are copied verbatim
from the script code — which is authentic by hypothesis — and its lineage outpoints are set
from the real spending context), and, on a commit, Commitment 2 (so its claimed ancestor is the
*actual* ancestor, not a forgery). Therefore step *n+1* is authentic.

By induction, **authenticity holds at every depth.** ∎

The same `hashOutputs` mechanism enforces **balance conservation** for the fungible token,
using 16-byte little-endian arithmetic inside the script:

- **transfer** copies the balance through unchanged;
- **merge** locks `out = balance + otherBalance` and consumes *both* inputs (no duplication);
- **split** locks `out_A = balance − piece` and `out_B = piece`, so `out_A + out_B = balance`.

There is no swap operation in this library (it was removed), which shrinks the attack surface
further.

---

## 5. Attack-by-attack

| Attack | Why it fails |
| --- | --- |
| **Forge a genesis** | `genesisOutpoint` is the mint's real on-chain outpoint; faking a chosen one needs a chosen txid → proof-of-work / SHA-256. |
| **Splice the chain** | The commit's ancestor rebuild compares `hash256(ancestor)` to `grandparentOutpoint.txid`; any substituted ancestor mismatches → SHA-256 collision needed. |
| **Inflate on merge** | The merged balance is computed in-script from values bound to each input token's own (verified) lineage; you cannot raise either without forging that token's history. |
| **Over-take on split** | The covenant checks `balance ≥ piece` and locks both output balances via `hashOutputs`. |
| **Steal a token** | `hash160(pubKey) == pubKeyHash` + `checkSig` under SIGHASH_ALL: no private key, no valid signature → ECDSA. |
| **Skip commit→settle** | `txoType` parity is enforced; a settle must follow a commit and vice versa. |
| **Fool the recognizer** | `recognizeType` requires **both** the field-push layout **and** `sha256(static contract code)` to match a registered type. A look-alike with the right shape but different code is classified "other" and rejected. |

---

## 6. The off-chain recognizer (the scanner)

On-chain, the covenant is self-enforcing. Off-chain — when an indexer or wallet inspects a
transaction it did not build — the library provides `recognizeType` / `verifyEvent` /
`verifyEvents`. Recognition is deliberately **strict**: a script is accepted as a known token
type only if its leading data-push lengths match the type's layout **and** the SHA-256 of the
remaining static contract bytes matches that type's fingerprint. A counterfeit that copies the
*shape* of a token but carries different (or no) covenant code fails the suffix-hash check and
is classified as untrusted. `verifyEvents` additionally checks the commit→settle event pairing
and the trusted issuer key across a whole batch.

---

## 7. Executable evidence

The claims above are not just prose — the test suite constructs **real, byte-level
counterfeits** (see `test/helpers/counterfeit.ts`, which forges on the wire exactly as an
attacker would, independent of any SDK quirk) and asserts they are rejected:

- `test/scanner/verifyEvents.test.ts` — accepts genuine mint→commit→settle lifecycles (and a lone
  genesis mint as a single-tx event); **rejects** a wrong trusted issuer, an orphan settle (a chain
  missing its commit), an unsettled commit, an output tampered with an extra `OP_RETURN`, and a
  counterfeit token output with the right push-shape but wrong static code.
- `test/scanner/parity.test.ts`, `test/scanner/events.test.ts`, `test/scanner/fingerprints.test.ts`
  — exercise recognition, event classification, and fingerprint matching against tampered inputs.
- The NFT and balance template suites build full lifecycles and verify each transaction against
  the actual `@bsv/sdk` Script interpreter — not a mock.

Run them with `npm test` (126 tests across 18 files, all green).

---

## 8. Security assumptions

The guarantee rests on three standard assumptions and nothing else:

1. **SHA-256 collision resistance** — no feasible way to find two transactions with the same
   hash (best known ≈ 2¹²⁸ work).
2. **ECDSA unforgeability on secp256k1** — no valid signature without the private key.
3. **Proof-of-work immutability** — a confirmed transaction's txid is fixed.

No trusted issuer server, no off-chain database, and no privileged validator is part of the
trust base. The proof lives in Bitcoin Script and is secured by the chain itself.

**What this does *not* cover.** Two things a stablecoin needs are out of scope here, because they
are not properties of the covenant:

- **Supply-honesty.** "Cannot be counterfeited" is a *per-token* statement: every unit is
  internally well-formed and traces to an issuer-signed mint. It does **not** mean the issuer is
  honest about how *much* it mints — an issuer can create any number of independent genesis tokens.
  Trusting the total supply against a reserve is an issuer / off-chain matter, not something the
  contract proves.
- **Network security.** Assumption 3 (proof-of-work immutability) holds only while no adversary
  controls a hash-power majority. On a low- or concentrated-hash-power chain that is the dominant
  real-world risk, and it is inherited from the underlying chain, not established here.

The rigorous companion [`formal-proof.md`](formal-proof.md) §1.6 states this boundary precisely.
