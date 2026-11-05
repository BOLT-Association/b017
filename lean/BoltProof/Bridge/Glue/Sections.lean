import BoltProof.Bridge.Generated.Chunks
import BoltProof.Bridge.Gadgets.NullAncestor
import BoltProof.Bridge.Gadgets.BalanceGuards
import BoltProof.Bridge.Gadgets.Parity
import BoltProof.Bridge.Gadgets.NftType
import BoltProof.Bridge.Gadgets.BalanceBounds

/-!
# The fragments at their offsets

`lean/README.md` and the `Gadgets/` docstrings name the suffix offsets at which each proved fragment
sits. Those offsets were prose until now. Here each is a theorem: the chunk the exporter cut at that
offset (`Generated/Chunks.lean`) *is* the fragment literal the Gadgets file reasons about, and the
`drop`/`take` of the whole suffix at the offset is that literal. Everything is `decide` on list
literals, under the three standard axioms; `Bridge/Bytes.lean` ties the suffixes to the shipped hex
by `native_decide`, so the chain hex → chunks → fragment is closed.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BoltProof.Glue

open BoltProof.Bridge.Generated

/-! ## SimpleMultiBOLT (fungible) -/

theorem simpleMulti_length : SimpleMulti.suffix.length = 4700 := by decide +kernel
theorem simpleMulti_parityCheck_chunk : SimpleMulti.c528_parityCheck = Gadgets.parityCheck := by decide
theorem simpleMulti_boundCheck27_chunk : SimpleMulti.c610_boundCheck27 = Gadgets.boundCheck 0x27 := by decide
theorem simpleMulti_boundCheck2d_chunk : SimpleMulti.c621_boundCheck2d = Gadgets.boundCheck 0x2d := by decide
theorem simpleMulti_mergeGuard_chunk : SimpleMulti.c672_mergeGuard = Gadgets.mergeGuard := by decide
theorem simpleMulti_splitGuard_chunk : SimpleMulti.c687_splitGuard = Gadgets.splitGuard := by decide
theorem simpleMulti_mergeSettle_chunk : SimpleMulti.c781_mergeSettle = Gadgets.mergeSettle := by decide
theorem simpleMulti_splitSettle_chunk : SimpleMulti.c935_splitSettle = Gadgets.splitSettle := by decide
theorem simpleMulti_nullTail_chunk : SimpleMulti.c4648_nullTail = Gadgets.nullTail := by decide

theorem parityCheck_at_528 : (SimpleMulti.suffix.drop 528).take 29 = Gadgets.parityCheck := by decide +kernel
theorem boundCheck_at_610 : (SimpleMulti.suffix.drop 610).take 11 = Gadgets.boundCheck 0x27 := by decide +kernel
theorem boundCheck_at_621 : (SimpleMulti.suffix.drop 621).take 11 = Gadgets.boundCheck 0x2d := by decide +kernel
theorem mergeGuard_at_672 : (SimpleMulti.suffix.drop 672).take 11 = Gadgets.mergeGuard := by decide +kernel
theorem splitGuard_at_687 : (SimpleMulti.suffix.drop 687).take 10 = Gadgets.splitGuard := by decide +kernel
theorem mergeSettle_at_781 : (SimpleMulti.suffix.drop 781).take 16 = Gadgets.mergeSettle := by decide +kernel
theorem splitSettle_at_935 : (SimpleMulti.suffix.drop 935).take 15 = Gadgets.splitSettle := by decide +kernel
theorem simpleMulti_nullTail_at_4648 : (SimpleMulti.suffix.drop 4648).take 4 = Gadgets.nullTail := by decide +kernel

/-! ## MinSimpleBOLT -/

theorem minSimple_length : MinSimple.suffix.length = 1123 := by decide +kernel
theorem minSimple_nftFlag_chunk : MinSimple.c6_nftFlag = Gadgets.nftFlag := by decide
theorem minSimple_nftTypeSel_chunk : MinSimple.c534_nftTypeSel17 = Gadgets.nftTypeSel 0x17 := by decide
theorem minSimple_nullTail_chunk : MinSimple.c1072_nullTail = Gadgets.nullTail := by decide
theorem minSimple_nftFlag_at_6 : (MinSimple.suffix.drop 6).take 3 = Gadgets.nftFlag := by decide +kernel
theorem minSimple_nftTypeSel_at_534 : (MinSimple.suffix.drop 534).take 13 = Gadgets.nftTypeSel 0x17 := by decide +kernel
theorem minSimple_nullTail_at_1072 : (MinSimple.suffix.drop 1072).take 4 = Gadgets.nullTail := by decide +kernel

/-! ## AuthBOLT -/

theorem authBolt_length : AuthBolt.suffix.length = 1145 := by decide +kernel
theorem authBolt_nftFlag_chunk : AuthBolt.c6_nftFlag = Gadgets.nftFlag := by decide
theorem authBolt_nftTypeSel_chunk : AuthBolt.c543_nftTypeSel17 = Gadgets.nftTypeSel 0x17 := by decide
theorem authBolt_nullTail_chunk : AuthBolt.c1094_nullTail = Gadgets.nullTail := by decide
theorem authBolt_nftFlag_at_6 : (AuthBolt.suffix.drop 6).take 3 = Gadgets.nftFlag := by decide +kernel
theorem authBolt_nftTypeSel_at_543 : (AuthBolt.suffix.drop 543).take 13 = Gadgets.nftTypeSel 0x17 := by decide +kernel
theorem authBolt_nullTail_at_1094 : (AuthBolt.suffix.drop 1094).take 4 = Gadgets.nullTail := by decide +kernel

/-! ## SerialBOLT -/

theorem serialBolt_length : SerialBolt.suffix.length = 1283 := by decide +kernel
theorem serialBolt_nftFlag_chunk : SerialBolt.c39_nftFlag = Gadgets.nftFlag := by decide
theorem serialBolt_nftTypeSel_chunk : SerialBolt.c589_nftTypeSel18 = Gadgets.nftTypeSel 0x18 := by decide
theorem serialBolt_nullTail_chunk : SerialBolt.c1232_nullTail = Gadgets.nullTail := by decide
theorem serialBolt_nftFlag_at_39 : (SerialBolt.suffix.drop 39).take 3 = Gadgets.nftFlag := by decide +kernel
theorem serialBolt_nftTypeSel_at_589 : (SerialBolt.suffix.drop 589).take 13 = Gadgets.nftTypeSel 0x18 := by decide +kernel
theorem serialBolt_nullTail_at_1232 : (SerialBolt.suffix.drop 1232).take 4 = Gadgets.nullTail := by decide +kernel

end BoltProof.Glue
