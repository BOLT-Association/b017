import BoltProof.Core
import BoltProof.Bridge

/-!
Axiom audit for Layer 1 and the glue. `lake env lean AxiomCheck.lean` prints the axioms each main theorem
depends on; `scripts/lean-axiom-check.mjs` fails CI if anything beyond `propext`,
`Classical.choice` and `Quot.sound` appears here. The glue's theorems (`BoltProof.Glue.*`, below the protocol
theorems) are symbolic and held to the same rule; the evaluator-trusted guards beside them
(`BoltProof.Bridge.Glue.*`) are audited with the rest of Layer 2.
-/

open BoltProof

#print axioms Fam.fungible_edge_iff
#print axioms Fam.nft_edge_iff
#print axioms t4_step
#print axioms t4_defined_types
#print axioms t4_no_skip
#print axioms Run.t3_conservation
#print axioms Run.t3_no_melt
#print axioms Run.t3_single_genesis
#print axioms Run.t3_nft_count
#print axioms t2_presented
#print axioms t2_ownership
#print axioms t2_no_keyless_spend
#print axioms Run.live_rooted
#print axioms Run.t1_authenticity
#print axioms Run.t1_issuer_invariant
#print axioms Run.t1_rebuild_sound
#print axioms Run.t5_proof_gating
#print axioms Run.t5_balance_anchor
#print axioms Run.t5_fabricated_hop_excluded
#print axioms t1_step
#print axioms Spend.commit_outputs
#print axioms Run.grandparent_commit
#print axioms Run.valid_of_stepwise
#print axioms Run.grandparent_commit_upto
#print axioms Run.grandparent_layout_upto
#print axioms Run.other_grandparent_layout_upto
#print axioms t1_genesis_signer

-- The glue (`lean/GLUE-PLAN.md`): what each shipped suffix enforces on every input (`*_sound`), the proved fragments
-- it reaches (`reaches_*`), and the refinement of a valid spend to `Accepts` (`*_refines`).
#print axioms Glue.MinSimple.minSimple_sound
#print axioms Glue.MinSimple.reaches_nftTypeSel
#print axioms Glue.MinSimple.reaches_nullTail
#print axioms Glue.MinSimple.minSimple_refines
#print axioms Glue.MinSimple.accepts_of_real
#print axioms Glue.MinSimple.real_presented
#print axioms Glue.MinSimple.real_ownership
#print axioms Glue.MinSimple.real_no_keyless_spend
#print axioms Glue.MinSimple.real_state_machine
#print axioms Glue.MinSimple.real_value_conserved
#print axioms Glue.MinSimple.real_issuer_carried
#print axioms Glue.MinSimple.real_genesis_needs_issuer
#print axioms Glue.MinSimple.gpReal_of_chain
#print axioms Glue.MinSimple.valid_of_chain
#print axioms Glue.MinSimple.chain_authenticity
#print axioms Glue.MinSimple.chain_count
#print axioms Glue.MinSimple.chain_proof_gating
#print axioms Glue.MinSimple.chain_fabricated_hop_excluded
#print axioms Glue.SimpleMulti.reaches_parityCheck
#print axioms Glue.SimpleMulti.reaches_boundCheck_610
#print axioms Glue.SimpleMulti.reaches_boundCheck_621
#print axioms Glue.SimpleMulti.reaches_mergeGuard
#print axioms Glue.SimpleMulti.reaches_splitGuard
#print axioms Glue.SimpleMulti.reaches_mergeSettle
#print axioms Glue.SimpleMulti.reaches_splitSettle
#print axioms Glue.SimpleMulti.simpleMulti_sound
#print axioms Glue.SimpleMulti.simpleMulti_refines_basic
#print axioms Glue.SimpleMulti.simpleMulti_refines_settle_gp
#print axioms Glue.SimpleMulti.simpleMulti_refines_merge_commit
#print axioms Glue.SimpleMulti.simpleMulti_refines_merge_settle
#print axioms Glue.SimpleMulti.accepts_of_real
#print axioms Glue.SimpleMulti.accepts_of_real_settle_gp
#print axioms Glue.SimpleMulti.accepts_of_real_merge_commit
#print axioms Glue.SimpleMulti.accepts_of_real_merge_settle
#print axioms Glue.SimpleMulti.real_presented
#print axioms Glue.SimpleMulti.real_ownership
#print axioms Glue.SimpleMulti.real_state_machine
#print axioms Glue.SimpleMulti.real_value_conserved
#print axioms Glue.SimpleMulti.real_value_conserved_merge
#print axioms Glue.SimpleMulti.real_issuer_carried
#print axioms Glue.SimpleMulti.real_genesis_needs_issuer
#print axioms Glue.SimpleMulti.gpRealF_of_chain
#print axioms Glue.SimpleMulti.gpRealB_of_chain
#print axioms Glue.SimpleMulti.valid_of_chain
#print axioms Glue.SimpleMulti.chain_authenticity
#print axioms Glue.SimpleMulti.chain_conservation
#print axioms Glue.SimpleMulti.chain_proof_gating
#print axioms Glue.SimpleMulti.chain_fabricated_hop_excluded
#print axioms Glue.AuthBolt.authBolt_sound
#print axioms Glue.AuthBolt.reaches_nftTypeSel
#print axioms Glue.AuthBolt.reaches_nullTail
#print axioms Glue.AuthBolt.authBolt_refines
#print axioms Glue.SerialBolt.serialBolt_sound
#print axioms Glue.SerialBolt.reaches_nftTypeSel
#print axioms Glue.SerialBolt.reaches_nullTail
#print axioms Glue.SerialBolt.serialBolt_refines
