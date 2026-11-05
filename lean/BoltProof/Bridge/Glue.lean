import BoltProof.Bridge.Glue.Sections
import BoltProof.Bridge.Glue.Sym.Basic
import BoltProof.Bridge.Glue.Sym.Steps
import BoltProof.Bridge.Glue.Sym.Skip
import BoltProof.Bridge.Glue.Sym.SkipSteps
import BoltProof.Bridge.Glue.Sym.Tactic
import BoltProof.Bridge.Glue.Sym.Examples
import BoltProof.Bridge.Glue.MinSimple.Spec
import BoltProof.Bridge.Glue.MinSimple.PushTx
import BoltProof.Bridge.Glue.MinSimple.Paths
import BoltProof.Bridge.Glue.MinSimple.Sound
import BoltProof.Bridge.Glue.MinSimple.Abs
import BoltProof.Bridge.Glue.Refine.Verify
import BoltProof.Bridge.Glue.Refine.Serial
import BoltProof.Bridge.Glue.Refine.Facts
import BoltProof.Bridge.Glue.Refine.Weld
import BoltProof.Bridge.Glue.Refine.MinSimple
import BoltProof.Bridge.Glue.Refine.EndToEnd
import BoltProof.Bridge.Glue.Regress
import BoltProof.Bridge.Glue.SimpleMulti.Spec
import BoltProof.Bridge.Glue.SimpleMulti.PushTx
import BoltProof.Bridge.Glue.SimpleMulti.Reaches

/-!
# BoltProof.Bridge.Glue

The glue between the fragment proofs of `Gadgets/` and the shipped covenant bytes
(`lean/GLUE-PLAN.md`). Everything under `BoltProof.Glue` is symbolic and held to Layer 1's axiom
rules; the few evaluator-trusted identities live in `BoltProof.Bridge` (`Bridge/Bytes.lean`).

* `Sections.lean`: the fragment literals at their offsets in the chunked suffixes (M1).
* `Sym/`: the inversion step lemmas and the drivers that chain them (M2).
* `MinSimple/`: what the `MinSimpleBOLT` suffix enforces, proved by running it symbolically along
  each of its ten paths (M3): `Spec.lean` states it, `PushTx.lean` abstracts the lock's own
  `OP_PUSH_TX` block, `Paths/` runs the paths, `Sound.lean` assembles `minSimple_sound` and the
  `reaches_*` theorems; `Abs.lean` reads a real spend into the model's `Spend`.
* `Refine/`: the refinement to the covenant interface (M4): `Verify.lean` reads a valid verdict as a
  run of the lock, `Serial.lean` round-trips the node's serialisation, `Weld.lean` and `Facts.lean`
  turn the facts the run leaves into the model's clauses, and `MinSimple.lean` proves
  `minSimple_refines`: the bytes accept only what `Accepts` admits, under the residual assumptions
  it states; `EndToEnd.lean` composes it with Layer 1's per-spend theorems. `Regress.lean` (namespace `BoltProof.Bridge.Glue`, `native_decide`) reads the real
  `MinSimpleBOLT` vectors through the abstraction and applies the theorem to them.
* `SimpleMulti/`: the fungible family (M5): `Spec.lean` names its eleven fields and the unlocking
  arguments, `PushTx.lean` abstracts its `OP_PUSH_TX` block, and `Reaches.lean` proves that the
  run reaches each of the five proved fragments with the stack its lemma assumes.
-/
