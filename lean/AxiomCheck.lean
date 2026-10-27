import BoltProof.Core

/-!
Axiom audit for Layer 1. `lake env lean AxiomCheck.lean` prints the axioms each main theorem
depends on; `scripts/lean-axiom-check.mjs` fails CI if anything beyond `propext`,
`Classical.choice` and `Quot.sound` appears here.
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
