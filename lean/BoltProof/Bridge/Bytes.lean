import BoltProof.Bridge.Params
import BoltProof.Bridge.Generated.Bytes
import BsvScript.Hash.Sha256

/-!
# The covenant bytes

`Generated/Bytes.lean` carries the static suffix of every shipped covenant (the compiled
locking script after the data pushes) and the SHA-256 fingerprint the off-chain scanner's
`REGISTRY` recognises it by (`src/lib/scanner/fingerprints.ts`). The theorems here establish,
by running bsv-script-lean's SHA-256 in the kernel's trusted evaluator, that the bytes the Lean
development reasons about are the bytes the package ships and recognises.
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

end BoltProof.Bridge
