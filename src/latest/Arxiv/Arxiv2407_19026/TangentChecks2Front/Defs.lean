import Arxiv.Arxiv2407_19026.TangentChecks2.Defs

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

end TangentRound2Native
end Arxiv2407_19026
