import BoltProof.Bridge.Glue.SerialBolt.Paths.Commit
import BoltProof.Bridge.Glue.SerialBolt.Paths.SettleNull
import BoltProof.Bridge.Glue.SerialBolt.Paths.SettleRebuild
import BoltProof.Bridge.Glue.SerialBolt.Paths.Melt

/-!
# The twelve paths through the `SerialBOLT` suffix

One module per group of paths, so that `lake` checks them in parallel: the two commits
(`Paths/Commit.lean`), the two settles without a grandparent (`Paths/SettleNull.lean`), the two settles
that rebuild the grandparent (`Paths/SettleRebuild.lean`) and the six melts (`Paths/Melt.lean`).
`SerialBolt/Sound.lean` assembles them.
-/
