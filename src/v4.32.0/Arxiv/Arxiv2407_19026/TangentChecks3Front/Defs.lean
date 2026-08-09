import Arxiv.Arxiv2407_19026.TangentChecks3.Defs

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

end TangentRound3Native
end Arxiv2407_19026
