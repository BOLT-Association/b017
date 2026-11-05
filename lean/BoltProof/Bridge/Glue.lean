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
  `reaches_*` theorems.
-/
