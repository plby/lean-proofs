import Arxiv.Arxiv2407_19026.TangentChecks2

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentRound2Native

open TangentAffine

/-- The forward grid, uniformly bisected to avoid isolated coarse-cell
enclosure losses. -/
def forwardCoordRefined : List ℚ :=
  (List.range 1680).flatMap (fun n =>
    [((2 * n + 2001 : Nat) : ℚ) / 20000,
      ((n + 1001 : Nat) : ℚ) / 10000])

/-- The plateau book grid, refined to `10⁻⁴` on `[0.326, 0.367]`. -/
def plateauBookRefined : List ℚ :=
  mediumBreakpoints 268 58 ++
    (List.range 41).flatMap (fun n =>
      (List.range 10).map
        (fun j => ((10 * (n + 326) + j + 1 : Nat) : ℚ) / 10000)) ++
    mediumBreakpoints 367 11

/-- The final book grid, refined to `10⁻⁴` on `[0.984, 1]`. -/
def back2BookRefined : List ℚ :=
  mediumBreakpoints 600 384 ++
    (List.range 16).flatMap (fun n =>
      (List.range 10).map
        (fun j => ((10 * (n + 984) + j + 1 : Nat) : ℚ) / 10000))

set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma forward_checks :
    checkLowerAffineCover (forwardLogCoord β1 β2 r2ForwardT) 0
        cfg (1 / 10) forwardCoordRefined = true ∧
      checkLowerAffineCover (forwardBook β1 β2 r2ForwardT)
        (1 / 1000000) cfg (1 / 10) forwardMedium = true := by
  exact ⟨by native_decide, forward_book_check⟩

set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma plateau_checks :
    checkLowerAffineCover (plateauLogLow β1 β2 plateauT) 0
        cfg (67 / 250) plateauMedium = true ∧
      checkLowerAffineCover (plateauLogHigh β1 β2 plateauT) 0
        cfg (67 / 250) plateauMedium = true ∧
      checkLowerAffineCover (plateauBook β1 β2 plateauT)
        (1 / 1000000) cfg (67 / 250) plateauBookRefined = true := by
  exact ⟨plateau_coord_checks.1,
    plateau_coord_checks.2, by native_decide⟩

set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma back2_checks :
    checkLowerAffineCover (backwardLogCoord β1 β2 r2Back2T) 0
        cfg (3 / 5) back2Fine = true ∧
      checkLowerAffineCover (backwardBook β1 β2 r2Back2T)
        (1 / 1000000) cfg (3 / 5) back2BookRefined = true := by
  exact ⟨back2_coord_check, by native_decide⟩

end TangentRound2Native
end Arxiv2407_19026
