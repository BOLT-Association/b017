# The issuer guard, by family: `is2ndTx`, F3, and the fabricated hop

**Read this before touching the lock prologue of either family, and before proposing to "port
`is2ndTx` to the fungible contract".** It exists because the three things in the title keep being
conflated, and an old sentence in [`formal-proof.md`](formal-proof.md) once made the confusion easy.

> **TL;DR.** `is2ndTx` is an **NFT-family** flag (`MinSimpleBOLT`, `AuthBOLT`). It is not in
> `SimpleMultiBOLT`, it never was, and it was **not** introduced for the fabricated hop: it is in the
> NFT bytecode at this repository's first commit (2026-06-22), ten weeks before that bug was found.
> The fungible family does not need it, because since the red-team release of 2026-09-07 it enforces
> a **strictly broader** rule: the issuer must sign whenever the grandparent outpoint is zero,
> whatever the `txoType`. That rule is the F3 fix, though F3 itself was the commit-typed shape
> `is2ndTx` already covers; the extra breadth is a margin, not a requirement. The fabricated hop was a different bug with a
> different fix (the balance anchor, 2026-09-05). All of this is executed against the shipped
> bytecode by `test/lib/multiBoltIssuerGuard.test.ts`.

---

## 1. What each prologue derives

Both lock scripts open the same way: derive one boolean, *the issuer must sign this spend*, from the
spent token's own fields, and under it assert `issuerPubKey == pubKey`. The two families derive that
boolean differently.

### NFT family: `MinSimpleBOLT`, `AuthBOLT`

The first opcodes of `LOCK_SCRIPT_SUFFIX` in `src/tokens/templates/MinSimple.sx.template.ts` (and,
byte for byte, `AuthBolt.sx.template.ts`):

```
OP_2 OP_PICK OP_BIN2NUM OP_NOT                      isGenesis      = (parentOutpoint == 0)
OP_SWAP OP_2SWAP
OP_DUP OP_BIN2NUM OP_0NOTEQUAL                      hasGrandparent = (grandparentOutpoint != 0)
OP_DUP OP_NOT OP_6 OP_PICK OP_BIN2NUM OP_BOOLAND    is2ndTx        = !hasGrandparent && (txoType != 0)
OP_5 OP_PICK OP_BOOLOR                              needsIssuer    = isGenesis || is2ndTx
OP_IF OP_3 OP_PICK OP_10 OP_PICK OP_EQUALVERIFY OP_ENDIF     needsIssuer => issuerPubKey == pubKey
```

(The contract source is `MinSimpleBolt.sx:83-88` in the `sx` repository; this package ships only the
compiled bytes.)

### Fungible family: `SimpleMultiBOLT`

The first opcodes of `LOCK_SCRIPT_SUFFIX` in `src/tokens/templates/SimpleMulti.sx.template.ts`:

```
OP_2 OP_PICK OP_BIN2NUM OP_NOT                      isGenesis      = (parentOutpoint == 0)
OP_2 OP_PICK OP_BIN2NUM OP_NOT OP_BOOLOR            needsIssuerKey = isGenesis || (grandparentOutpoint == 0)
OP_TUCK OP_IF OP_13 OP_PICK OP_EQUALVERIFY          needsIssuerKey => issuerPubKey == pubKey
  OP_15 OP_PICK OP_DUP 25 OP_EQUAL OP_NOT OP_VERIFY 27 OP_EQUAL OP_NOT OP_VERIFY   ... and not a merge commit
OP_ELSE OP_DROP OP_ENDIF
```

The second line is the F3 fix: five opcodes, added 2026-09-07. Before it the prologue read
`OP_2 OP_PICK OP_BIN2NUM OP_NOT OP_TUCK OP_IF ...`, i.e. `isGenesis` alone. `FixedBOLT` and
`OpenBOLT` (the genesis family, `FixedMulti.sx.template.ts` and `OpenMulti.sx.template.ts`) carry
the identical guard sequence after the opcodes that handle their two leading pushes.

### Side by side

| | NFT (`is2ndTx`) | Fungible (`needsIssuerKey`) |
|---|---|---|
| Issuer required when | parent is zero, **or** grandparent is zero **and** `txoType != 0` | parent is zero, **or** grandparent is zero |
| Honest spends it covers | the first commit (spends `T(0)`) and the first settle (spends `T(1)`, a `21` token with no grandparent) | the same two |
| Refuses F3 (a commit-typed `21` token, garbage parent, no grandparent) | yes | yes |
| The shape it leaves open | a resting `00` token with a non-zero parent and a zero grandparent: its **commit** is accepted, its **settle** is refused | none: that shape (`20` in this encoding) is refused at its commit |

Every token on which `is2ndTx` is true has a zero grandparent, so the fungible rule is a superset of
the NFT rule. There is no spend the NFT flag refuses that the fungible guard accepts.

---

## 2. Why "grandparent is zero" is an exact test for "the issuer owns it"

Only two tokens in any honest lineage have a zero grandparent:

- `T(0)`, the genesis: parent zero, grandparent zero.
- `T(1)`, the first commit's output: parent `T(0)`, grandparent zero.

`T(2)`, the first settle's output, already carries `grandparent = outpoint(T(0))`, which is non-zero,
and from there on every token's grandparent is a real outpoint. Both `T(0)` and `T(1)` are
issuer-owned: a genesis can only be spent by a key that is both the issuer key (`isGenesis` guard) and
the owner hash, and a commit keeps the token with the sender, so `T(1)` is paid back to the issuer.
Requiring the issuer whenever the grandparent is zero therefore refuses nothing honest. It is the
genesis rule applied one hop later, with no new field and no new argument.

---

## 3. Why each family's rule is enough, and what F3 actually was

**NFT.** A fabricated resting token (`txoType 00`, garbage non-zero parent, zero grandparent, victim's
`issuerPubKey`, attacker's owner hash) dodges both the issuer guard and the ancestor rebuild at its own
spend, so a lone **commit** of it is accepted. But a commit is half an event. The **settle** that would
complete it must rebuild the fabricating transaction as a genuine commit, and it cannot: that
transaction was funded from a P2PKH and has no token input. An NFT carries no balance to inflate in the
meantime, and a value-neutral clone is tolerated by design. The suite documents this as *CLEAN*:
`test/lib/minSimpleAttack.test.ts` B1.0 (the lone commit is accepted), B1.1 (the settle is refused in
the grandparent reconstruction), B1.2 (a genesis shape re-arms the guard), B1.3 and B4.4 (**any**
non-zero `txoType` re-arms the guard, which is `is2ndTx` doing its job).

**Fungible.** Before 2026-09-07 the fungible prologue tested `isGenesis` only, with no grandparent
term at all, and the rebuild is gated on `hasBolt && hasGrandparent`. A `21`-typed token with a
garbage parent and a zero grandparent, the first commit's shape, was therefore neither genesis nor
rebuilt: no issuer check, no ancestor, no balance anchor, no proof co-spend. A non-issuer could
**settle any balance out of nothing**. The red team called this F3 and noted it was *contained to one
hop* (the settle after that must rebuild the fabrication and cannot), but for a balance-bearing token
one hop is enough to pay an SPV recipient with a number nobody minted. The fix is the second line of
the fungible prologue above.

**What F3 required, and what the fix chose.** The F3 token is commit-typed, which is exactly the shape
`is2ndTx` covers: the NFT rule would have closed F3 too. What the fungible family lacked was a
grandparent term, not the absence of a `txoType` term. The fix chose the broader form,
`grandparent == 0` whatever the type, which also refuses the settle-typed orphan (`20` here, the
analogue of the NFT family's tolerated `00` token) at its commit. That is a margin the fix took, not
one F3 imposed. `test/lib/multiBoltIssuerGuard.test.ts` executes both shapes.

### Why the NFT family needed no fabricated-hop fix at all

The question comes up every time: the fungible contract got the balance anchor on 2026-09-05, so where
is the NFT equivalent? There is none, for two reasons that together leave nothing to fix.

1. **There is no balance to inflate.** `MinSimpleBOLT` is an identity token with no value field, and
   `AuthBOLT` adds only `authOrMiscData`, which the next settle authenticates by rebuilding the commit
   that created it. The value-bearing NFT variants (`MinSimpleBalance`, `MinSimpleDiscount`) were
   removed in the `0.1.0` release commit, and even they spliced the token's **own** fields into the
   ancestor rebuild rather than accepting the ancestor's as unlock arguments, so an invented value sat
   inside the pre-image hashed against `grandparentOutpoint` and failed the hash. No split or merge
   exists in the family, so there is no transition whose arithmetic could be gamed.
2. **A clone costs the original, and only the holder can make one.** The proof a commit emits is a
   single P2PKH-shaped UTXO naming the recipient. A cloned settle copies the real token's bytes, so it
   names the same owner and can only be completed by co-spending that one proof, which only that owner
   can sign. Settling the clone therefore strands the original, and settling the original strands the
   clone: one token in, one token out, same holder, holder's choice. The clone's ancestry is genuine
   (its parent is the real commit, the proof it consumes is the real proof), which is exactly why it
   survives and exactly why there is nothing to gain from it. A third party cannot clone at all, because
   they cannot sign the proof, so there is no victim.

Only a cloned **settle** escapes, because nothing ever rebuilds a settle; a cloned or fabricated
commit is caught by the settle that must rebuild it. The fabricated hop was this same clone with one
extra ingredient, a balance field the holder could edit, and that ingredient is what the balance
anchor removed. The identity NFT never had it.

---

## 4. Three things that are not the same thing

| | What it is | Family | When | Fix |
|---|---|---|---|---|
| **The fabricated hop** | A *past recipient* copies a settled token's bytes into an output they fund themselves, gives it any balance, commits it to themselves and settles it, co-spending the real proof they legitimately hold. Every check passed; a regtest teranode running GoBDK consensus accepted a 2<sup>100</sup> token. | Fungible | Found 2026-09-03, closed 2026-09-05 (`0.0.0-b2`) | **The balance anchor.** The settle reads `balance`, `balanceCommit` and `txoType` off the grandparent it has just rebuilt, derives the one balance that ancestor authorised, and requires the spent token's balance to equal it. Nothing new is stored. |
| **F3** | A token with a garbage parent and a zero grandparent escaped the issuer guard and the rebuild together. | Fungible | Found by the red team 2026-09-05 to 09-07, shipped 2026-09-07 (commit `ab95827`) | **The zero-grandparent issuer guard** (`needsIssuerKey = isGenesis || grandparent == 0`). |
| **`is2ndTx`** | The NFT family's re-assertion of the issuer at the first settle. | NFT | In the NFT bytecode at this repository's first commit (`1f7ed97`, 2026-06-22) | Not a fix. A design feature older than both bugs. |

Timeline, for the record:

| Date | Event |
|---|---|
| 2026-06-22 | Repository created; `is2ndTx` already in the three NFT templates' bytecode. The fungible prologue tests `isGenesis` only. |
| 2026-09-03 | The fabricated hop is built and broadcast on a regtest teranode, which accepts it. |
| 2026-09-05 | `0.0.0-b2`: the balance anchor closes the fabricated hop. The NFT templates are unaffected (their rebuild splices in the token's own fields, and they have no split or merge). |
| 2026-09-05 to 09-07 | Red-team campaign against `SimpleMultiBolt.sx`: B1, S1, S2, S3, F3, C5. |
| 2026-09-07 | Commit `ab95827` ships all six fixes. F3 adds the zero-grandparent term to the fungible prologue. The same commit adds the Lemma 5 correction retracting the claim that `is2ndTx` was in `SimpleMultiBolt`. |
| 2026-10-02 | Commit `110ff77` ports the NFT attack suite (`minSimpleAttack.test.ts`), whose B1.3 and B4.4 are the first references to `is2ndTx` in this repository's tests. |
| 2026-11-04 | This document, the Lemma 5 correction for F3, and `multiBoltIssuerGuard.test.ts`. |

---

## 5. Where the confusion came from

Until 2026-09-07, Lemma 5 of `formal-proof.md` said that `SimpleMultiBolt` derived `isGenesis` *"and
a first-commit flag, and under either asserts `issuerPubKey == pubKey`"*. There was no such flag in
the fungible contract. The correction dated 2026-09-02 retracted it, but the lemma's body kept
describing the fungible guard as *"the only issuer check ... fires when the spent token is
parentless"*, which stopped being true in the very same release when F3 added the grandparent term. A
reader of an old copy, or of the `sx`-side name alone, could come away believing that `is2ndTx` is a
fungible flag and that it was the fabricated-hop hardening. Both are wrong. Lemma 5 now states the
shipped rule for both families inline, with a two-line provenance note in place of stacked
corrections, so a reader meets the correct statement first.

---

## 6. Do not port `is2ndTx` to the fungible family

- It would **close nothing**: every token `is2ndTx` catches, `needsIssuerKey` already catches.
- It would **open nothing** either, but it would buy nothing for the cost below.
- **The prologue is load-bearing for the rebuild.** The ancestor reconstruction slices the live
  `scriptCode` at a hard-coded offset (`41n split nip 381n split drop`): the byte length of the lock
  code that precedes the shared `signCtx` macro body. F3's five opcodes moved that offset from 36 to
  41 and **broke every honest chain** until it was recounted (`sx/scripts/recount-signctx-prologue.mjs`).
  Anything added before the `signCtx` call shifts it; anything after does not. Any change to either
  prologue must recount, rebuild both suffixes, and re-run the full lifecycle suites.

If a future reader finds a spend the fungible guard accepts and the NFT flag would refuse, that is a
new finding: write the attack as a test first, in the style of `minSimpleAttack.test.ts` (assert
**which** transaction refuses, ship a positive control), and only then touch the contract.

The alignment worth considering runs the **other** way: simplify the NFT prologue to the fungible
rule by dropping the `txoType` term, so both families read `isGenesis || grandparent == 0`. That is
an optimisation, not a security fix (the NFT settle already refuses the orphan), and it costs a new
fingerprint and a reissue, so it is recorded in [`ROADMAP.md`](ROADMAP.md) as deferred work to be
folded into the next NFT bytecode rebuild.

---

## 7. Evidence

Executed in this repository, on the shipped bytecode, with no mocks:

- `test/lib/multiBoltIssuerGuard.test.ts`, fungible. Fabricated `SimpleMultiBOLT` tokens funded from
  an attacker's P2PKH, owned by the attacker, naming the victim as issuer, with a real non-zero parent,
  a zero grandparent and a balance of 2<sup>100</sup>:
  - control: the issuer's honest first settle (which spends a zero-grandparent commit) is **accepted**;
  - the F3 / `is2ndTx` shape (`txoType 21`): the attacker's settle is **refused** at the issuer
    guard's `OP_EQUALVERIFY`, lock opcode 24;
  - the settle-typed orphan (`txoType 20`), which only the fungible rule refuses at its commit: the
    attacker's commit is **refused** at the same opcode;
  - isolation: the identical `21`-shaped bytes naming the attacker as issuer are **accepted**, so the
    guard is the only thing refusing.
- `test/lib/minSimpleAttack.test.ts` B1.0 to B1.3 and B4.4, NFT: the tolerated orphan, and `is2ndTx`
  re-arming the guard on any non-zero `txoType`.
- `test/repro-fabricated-hop.test.ts`: the pre-fix fabricated-hop chain, frozen as the record of what a
  node accepted. Its assertions are meant to pass; do not flip them.
- `CHANGELOG.md`, the Security entries for `0.0.0-b2` (2026-09-05, the balance anchor) and `0.1.0`
  (the six red-team fixes shipped in the template, F3 among them).

Write-ups published during the campaign, shared by link:

- [Fabricated-Hop Inflation](https://claude.ai/artifact/QwguQpuHLChcqenzr9tZFR), 2026-09-03: the
  discovery, the teranode acceptance, and the first proposed fix.
- [Cloning, and why it is a dead end](https://claude.ai/artifact/DwzWMfx2un7wqC7ypoCU4Z), 2026-09-05:
  the closure, documenting the shipped balance anchor.
- [SimpleMultiBolt Red Team](https://claude.ai/artifact/VZzzbZW8QoCW94wrgw1Tpz), 2026-09-07: the six
  further defects, including the F3 section and the 36 to 41 prologue tripwire.

None of the three mentions `is2ndTx`, which is itself evidence: the flag had nothing to do with that
work.
