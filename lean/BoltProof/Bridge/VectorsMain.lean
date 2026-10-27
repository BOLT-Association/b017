import BoltProof.Bridge.Params
import BoltProof.Bridge.Generated.Vectors

/-!
# `lake exe boltvectors`

Runs every exported vector through the bsv-script-lean semantics natively and prints one line
per input: the expectation, the post-Chronicle verdict that is judged, and the pre-Chronicle
verdict as an informative control. Exits 1 on any mismatch. This is the fast, authoritative
leg; `Generated/VectorTheorems.lean` registers the same verdicts with the kernel through
`native_decide`.
-/

open BoltProof.Bridge BoltProof.Bridge.Generated

def expectStr : Expect → String
  | .valid => "valid"
  | .invalid c => c
  | .anyInvalid => "invalid(*)"
  | .skip => "skip"

def main : IO UInt32 := do
  let mut bad := 0
  let mut total := 0
  for v in allVectors do
    for i in List.range v.prevouts.length do
      let e := v.expect[i]?.getD .skip
      if e == .skip then continue
      total := total + 1
      let got := v.verdict params i
      let ok := e.matches got
      if !ok then bad := bad + 1
      let pre := (v.verdict paramsPreChronicle i).map Verdict.code |>.getD "undecodable"
      let gotS := got.map Verdict.code |>.getD "undecodable"
      IO.println s!"{if ok then "ok  " else "FAIL"} {v.name}[{i}] expect={expectStr e} got={gotS} preChronicle={pre}"
  IO.println s!"{total} inputs judged, {bad} mismatches, {allVectors.length} vectors"
  return (if bad == 0 then 0 else 1)
