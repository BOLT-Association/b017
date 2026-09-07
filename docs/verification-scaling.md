# Verifying a BOLT token's provenance is 2 transactions - O(1), at any depth

## The claim

To establish a BOLT token's full provenance a peer reads **the two transactions of its most recent
event** - the `commit -> settle` pair - and nothing else, however deep the lineage runs. Not O(N),
not O(log N): **O(1)**, a flat two transactions, whether the token is one hop from its mint or ten
thousand.

Runnable proof: [`test/scanner/verificationScaling.test.ts`](../test/scanner/verificationScaling.test.ts).
Verifying the tip reads exactly 2 transactions at depth 1, 8 and 24 alike.

## Why: the proof is induced by the covenant, not walked

A settle is valid only if it does two things against its **grandparent commit** (the commit two
transactions back): it **reconstructs** that commit from fields the spending token carries and
hash-checks the reconstruction against the token's `grandparentOutpoint`, and it **co-spends the
grandparent's one-shot proof output**. Both are only satisfiable if the grandparent event genuinely
happened and was correct - a proof output exists only because a real commit emitted it, and a
reconstruction hashes to `grandparentOutpoint` only if the grandparent's bytes were exactly those.

That gives an induction, and the covenant supplies the step:

- **Base case.** The first event of a lineage has no grandparent - its token records a zero
  `grandparentOutpoint`. There is nothing to rebuild; instead the first commit directly spends the
  genesis mint, which is issuer-signed. Verifiable in two transactions.
- **Inductive step.** A valid event at depth k is *constructible only if* the event at depth k-1
  happened and was correct - because event k's settle co-spends event k-1's commit proof and
  reconstructs that commit. Consensus enforced this when event k was mined: an event naming a
  grandparent that never happened does not validate, and is not mined (this is exactly what
  [`test/repro-fabricated-hop.test.ts`](../test/repro-fabricated-hop.test.ts) and the node-verified
  fabricated-hop specs demonstrate).
- **Conclusion.** The validity of the tip event therefore mathematically induces the validity of the
  entire chain behind it, back to the issuer's mint. A peer establishes provenance by reading the two
  tip transactions and inherits everything before them; it never reads the history.

Contrast an account ledger or a naive UTXO-lineage scheme, where trusting a token means replaying it
from the mint: O(depth) per token.

## What the peer holds

| Layer | What it establishes | What it reads | Cost |
|---|---|---|---|
| **The tip pair** (`verifyEvent`) | a well-formed commit+settle whose settle links to the commit and, by validity, re-anchors balance/issuer/lineage to a real grandparent | 2 transactions | **O(1)** |
| **Inclusion** (SPV) | the tip pair is mined, so consensus already ran the covenant - which is what makes the induction bind | a merkle path per tx | O(log blocksize) |
| **Issuer trust** (pin) | the token is this issuer's, not a look-alike with a foreign key | the issuer push, compared to the trusted key | O(1) |

The induction rests on consensus: a peer trusts that a *mined* transaction is *valid*. A peer who
refuses even that and re-executes the covenant scripts itself must supply the settle's direct inputs
(parent commit, grandparent commit's proof, funding) - a fixed window of at most four transactions,
still constant in depth and still never reaching genesis. Either way the per-token cost is O(1).

Re-validating an *entire history* from cold - an indexer's job, not a peer verifying one token - is
O(N): two transactions per event, N events, and still no genesis walk within any event. That is the
only place N appears, and it is linear, never the O(N^2) of re-deriving each event from the mint.

## The reader question, settled by the scaling goal

The off-chain readers here - `verifyEvents` and the demo's `verifyPayment` - deliberately do not walk
history, re-derive balances, or dedupe (the red-team suite
[`test/scanner/redteam2.test.ts`](../test/scanner/redteam2.test.ts) records what they therefore do
not catch alone). That is what keeps
verification O(1): the missing checks are supplied by the bounded layers above, not by walking the
past.

- **Balance / lineage** - the covenant and the two-hop rebuild; a scan pass is structural, not a
  balance check.
- **Uniqueness / double-settle** - a consensus property, confirmed by SPV inclusion plus the UTXO
  rule; making the scanner catch it needs an unbounded spend graph and breaks the property.
- **Issuer** - pin it (`trustedIssuerPubKey`), O(1).
- **Replay** - dedupe by outpoint or txid at the application boundary, O(1).

Hardening the reader to close these alone reintroduces the history walk the protocol exists to
avoid. Keep the reader a bounded O(1) inspector and make the caller contract explicit.

## The one-line version for peers

A valid BOLT settle re-proves its grandparent by reconstruction and co-spends its proof, so validity
induces backward: reading the two transactions of a token's latest event establishes its whole
provenance in O(1), and no verifier ever reads back to genesis.
