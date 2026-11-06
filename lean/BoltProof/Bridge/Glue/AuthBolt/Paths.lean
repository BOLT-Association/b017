import BoltProof.Bridge.Glue.AuthBolt.Paths.Commit
import BoltProof.Bridge.Glue.AuthBolt.Paths.SettleNull
import BoltProof.Bridge.Glue.AuthBolt.Paths.SettleRebuild
import BoltProof.Bridge.Glue.AuthBolt.Paths.Melt

/-!
# The eleven paths through the `AuthBOLT` suffix

One module per group of paths, so that `lake` checks them in parallel: the two commits
(`Paths/Commit.lean`), the two settles without a grandparent (`Paths/SettleNull.lean`), the two settles
that rebuild the grandparent (`Paths/SettleRebuild.lean`) and the five melts (`Paths/Melt.lean`).
`AuthBolt/Sound.lean` assembles them.
-/
