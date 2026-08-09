import Arxiv.Arxiv2407_19026.TangentChecks1.Defs

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

end TangentRound1Native
end Arxiv2407_19026
