import BoltProof.Bridge.Params
import BoltProof.Bridge.Generated.Bytes
import BoltProof.Bridge.Generated.Chunks
import BsvScript.Hash.Sha256

/-!
# The covenant bytes

`Generated/Bytes.lean` carries the static suffix of every shipped covenant (the compiled
locking script after the data pushes) and the SHA-256 fingerprint the off-chain scanner's
`REGISTRY` recognises it by (`src/lib/scanner/fingerprints.ts`). The theorems here establish,
by running bsv-script-lean's SHA-256 in the kernel's trusted evaluator, that the bytes the Lean
development reasons about are the bytes the package ships and recognises.

The `*_suffix_chunks` theorems tie each hex string to the chunk decomposition of
`Generated/Chunks.lean` (`lean/vectors/sections.ts`), the form the glue proof reasons about. They
are the only evaluator-trusted identities of the glue: everything downstream of a `suffix` is
`decide` on list literals or a symbolic run under the three standard axioms.
-/

namespace BoltProof.Bridge

open BsvScript

theorem simpleMulti_fingerprint :
    Hash.sha256 (hexDecode! Generated.simpleMultiSuffixHex) =
      hexDecode! Generated.simpleMultiFingerprintHex := by
  native_decide

theorem minSimple_fingerprint :
    Hash.sha256 (hexDecode! Generated.minSimpleSuffixHex) =
      hexDecode! Generated.minSimpleFingerprintHex := by
  native_decide

theorem authBolt_fingerprint :
    Hash.sha256 (hexDecode! Generated.authBoltSuffixHex) =
      hexDecode! Generated.authBoltFingerprintHex := by
  native_decide

theorem serialBolt_fingerprint :
    Hash.sha256 (hexDecode! Generated.serialBoltSuffixHex) =
      hexDecode! Generated.serialBoltFingerprintHex := by
  native_decide

/-! ## The hex strings are the chunk concatenations -/

theorem simpleMulti_suffix_chunks :
    hexDecode! Generated.simpleMultiSuffixHex = Generated.SimpleMulti.suffix := by
  native_decide

theorem minSimple_suffix_chunks :
    hexDecode! Generated.minSimpleSuffixHex = Generated.MinSimple.suffix := by
  native_decide

theorem authBolt_suffix_chunks :
    hexDecode! Generated.authBoltSuffixHex = Generated.AuthBolt.suffix := by
  native_decide

theorem serialBolt_suffix_chunks :
    hexDecode! Generated.serialBoltSuffixHex = Generated.SerialBolt.suffix := by
  native_decide

end BoltProof.Bridge
