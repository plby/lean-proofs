import Arxiv.Arxiv2407_19026.TangentChecks1

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentRound1Native

open TangentAffine

/-- The forward grid, uniformly bisected to avoid isolated coarse-cell
enclosure losses. -/
def forwardCoordRefined : List ℚ :=
  (List.range 1690).flatMap (fun n =>
    [((2 * n + 2001 : Nat) : ℚ) / 20000,
      ((n + 1001 : Nat) : ℚ) / 10000])

/-- The ordinary `10⁻³` plateau grid, refined to `10⁻⁴` only on
`[0.311, 0.379]`. -/
def plateauBookRefined : List ℚ :=
  mediumBreakpoints 269 42 ++
    (List.range 68).flatMap (fun n =>
      (List.range 10).map
        (fun j => ((10 * (n + 311) + j + 1 : Nat) : ℚ) / 10000)) ++
    mediumBreakpoints 379 8

set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma forward_checks :
    checkLowerAffineCover (forwardLogCoord β0 β1 r1ForwardT) 0
        cfg (1 / 10) forwardCoordRefined = true ∧
      checkLowerAffineCover (forwardBook β0 β1 r1ForwardT)
        (1 / 1000000) cfg (1 / 10) forwardMedium = true := by
  constructor <;> native_decide

set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma plateau_checks :
    checkLowerAffineCover (plateauLogLow β0 β1 plateauT) 0
        cfg (269 / 1000) plateauMedium = true ∧
      checkLowerAffineCover (plateauLogHigh β0 β1 plateauT) 0
        cfg (269 / 1000) plateauMedium = true ∧
      checkLowerAffineCover (plateauBook β0 β1 plateauT)
        (1 / 1000000) cfg (269 / 1000) plateauBookRefined = true := by
  constructor
  · native_decide
  constructor <;> native_decide

end TangentRound1Native
end Arxiv2407_19026
