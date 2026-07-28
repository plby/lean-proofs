import Arxiv.Arxiv2407_19026.TangentChecks3

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentRound3Native

open TangentAffine

/-- Refine the first derivative cell to `10⁻³`; the remaining cells retain
the original `10⁻²` spacing. -/
def smallCoordRefined : List ℚ :=
  (List.range 10).map (fun n => ((n + 1 : Nat) : ℚ) / 1000) ++
    (List.range 9).map (fun n => ((n + 2 : Nat) : ℚ) / 100)

/-- The forward grid, uniformly bisected to avoid isolated coarse-cell
enclosure losses. -/
def forwardCoordRefined : List ℚ :=
  (List.range 1680).flatMap (fun n =>
    [((2 * n + 2001 : Nat) : ℚ) / 20000,
      ((n + 1001 : Nat) : ℚ) / 10000])

/-- The final book grid, refined to `10⁻⁴` on `[0.946, 0.998]` and to
`10⁻⁵` on the last `0.002`. -/
def back2BookRefined : List ℚ :=
  mediumBreakpoints 600 346 ++
    fineBreakpoints 9460 520 ++
    (List.range 200).map
      (fun n => ((n + 99801 : Nat) : ℚ) / 100000)

set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma small_checks :
    checkLowerAffineCover (smallCoordSlope β2 β3) (1 / 20)
        cfg 0 smallCoordRefined = true ∧
      checkLowerAffineCover (smallBookSlope β2 β3) (1 / 1000)
        cfg 0 bpsBookSlope = true ∧
      checkLowerAffineCover (smallBook β2 β3) (1 / 10000)
        cfg (1 / 50) bpsBook = true := by
  exact ⟨by native_decide, small_book_checks⟩

set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma forward_checks :
    checkLowerAffineCover (forwardLogCoord β2 β3 r3ForwardT) 0
        cfg (1 / 10) forwardCoordRefined = true ∧
      checkLowerAffineCover (forwardBook β2 β3 r3ForwardT)
        (1 / 1000000) cfg (1 / 10) forwardMedium = true := by
  exact ⟨by native_decide, forward_book_check⟩

set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma back2_checks :
    checkLowerAffineCover (backwardLogCoord β2 β3 r3Back2T) 0
        cfg (3 / 5) back2Fine = true ∧
      checkLowerAffineCover (backwardBook β2 β3 r3Back2T)
        (1 / 1000000) cfg (3 / 5) back2BookRefined = true := by
  exact ⟨back2_coord_check, by native_decide⟩

end TangentRound3Native
end Arxiv2407_19026
