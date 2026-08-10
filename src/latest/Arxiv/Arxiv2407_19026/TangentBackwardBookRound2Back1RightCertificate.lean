import Arxiv.Arxiv2407_19026.TangentBackwardBookRound2Back1Certificate

/-!
# Reflected certificate for the second-round first backward book interval

The direct Horner enclosure is sharp on the left half of the normalized
interval.  On the right half we use the reflected coordinate `v = 1 - u`;
the same exact evaluator is then sharp on `v ∈ [0, 1 / 2]`.
-/

namespace Arxiv2407_19026
namespace BackwardBookRound2Back1Certificate

noncomputable section

def bookReflectedCoeffs : List ℤ :=
  integerPowerAffine 1 1 (-1) bookPowerCoeffs

lemma book_reflected_eval (v : ℝ) :
    evalIntegerPower bookReflectedCoeffs v =
      evalIntegerPower bookPowerCoeffs (1 - v) := by
  have haffine :=
    evalIntegerPower_affine
      1 1 (-1) bookPowerCoeffs v (by norm_num)
  change
    evalIntegerPower
        (integerPowerAffine 1 1 (-1) bookPowerCoeffs) v =
      evalIntegerPower bookPowerCoeffs (1 - v)
  calc
    _ = evalIntegerPower bookPowerCoeffs
        (((1 : ℝ) + (-1 : ℝ) * v) / 1) := by
      simpa only [Nat.cast_one, Int.cast_one, Int.cast_neg,
        Int.cast_ofNat, mul_one, one_mul, one_pow] using haffine
    _ = _ :=
      congrArg (evalIntegerPower bookPowerCoeffs) (by ring)

set_option maxHeartbeats 0 in
-- Exact Horner evaluation of the reflected degree-110 margin exceeds the default budget.
set_option maxRecDepth 100000 in
-- Constructing and evaluating the reflected coefficient list needs deeper recursion.
lemma book_horner_lower_right_reflected :
    0 <
      (integerHornerInterval bookReflectedCoeffs
        ({ lo := 0, hi := 1 / 2, le := by norm_num } :
          LeanCert.Core.IntervalRat)).lo := by
  norm_num (config := { maxSteps := 10000000 })
    [integerHornerInterval, bookReflectedCoeffs,
    integerPowerAffine, integerPowerAdd,
    integerPowerLinear, integerPowerLinearTail,
    bookPowerCoeffs, bookAffineTail0,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4,
    decimalNat]

end

end BackwardBookRound2Back1Certificate
end Arxiv2407_19026
