import BoundedGaps.Maynard.MaynardS1CrossCorrection

/-!
# General S1 decomposition for supported box weights

The diagonalization is generic in the tuple and in the supported Y-function;
no fixed polynomial candidate is needed. These exact finite identities are
the starting point for transferring the dyadic box mass to the sieve.
-/

namespace Erdos237

open BoundedGaps.Maynard

theorem sieveWeightSum_eq_yDiagonal_sub_cross_add_error
    {H : Finset ℕ} {R W N v : ℕ} {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R W y)
    (hcoverage : CoversShiftDifferencePrimes H W) :
    sieveWeightSum N
        (preSievedSquareDivisorWeight H (maynardDivisorTupleSupport H R W)
          (maynardCoefficientFromY H R W y) v W) =
      (N : ℝ) / W *
        (maynardYDiagonalSum H R W y -
          incompatibleDivisorPairCommonDivisorTupleSum H
            (maynardDivisorTupleSupport H R W) (maynardCoefficientFromY H R W y)) +
        compatibleDivisorPairErrorSum H (maynardDivisorTupleSupport H R W)
          v W N (maynardCoefficientFromY H R W y) := by
  have hD : ∀ d ∈ maynardDivisorTupleSupport H R W, IsMaynardDivisorTuple H R W d :=
    fun _ hd => isMaynardDivisorTuple_of_mem_support hd
  rw [sieveWeightSum_preSieved_eq_compatibleDivisorPairMainSum_add_error hD hcoverage,
    compatibleDivisorPairMainSum_eq_commonDivisorTupleSum hD,
    compatibleCommonDivisorTupleSum_eq_yDiagonal_sub_incompatible hy]

theorem abs_sieveWeightSum_sub_yDiagonal_le
    {H : Finset ℕ} {R W N v : ℕ} {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R W y)
    (hcoverage : CoversShiftDifferencePrimes H W) (hW : 0 < W) :
    |sieveWeightSum N
        (preSievedSquareDivisorWeight H (maynardDivisorTupleSupport H R W)
          (maynardCoefficientFromY H R W y) v W) -
        (N : ℝ) / W * maynardYDiagonalSum H R W y| ≤
      (N : ℝ) / W *
        |incompatibleDivisorPairCommonDivisorTupleSum H
          (maynardDivisorTupleSupport H R W) (maynardCoefficientFromY H R W y)| +
        compatibleDivisorPairCoefficientMass H (maynardDivisorTupleSupport H R W)
          (maynardCoefficientFromY H R W y) := by
  rw [sieveWeightSum_eq_yDiagonal_sub_cross_add_error hy hcoverage]
  have hD : ∀ d ∈ maynardDivisorTupleSupport H R W, IsMaynardDivisorTuple H R W d :=
    fun _ hd => isMaynardDivisorTuple_of_mem_support hd
  have herror := abs_compatibleDivisorPairErrorSum_le_coefficientMass
    (lambda := maynardCoefficientFromY H R W y) (v := v) (N := N) hW hD
  have hfactor : (0 : ℝ) ≤ (N : ℝ) / W := by positivity
  calc
    _ = |-(N : ℝ) / W *
        incompatibleDivisorPairCommonDivisorTupleSum H
          (maynardDivisorTupleSupport H R W) (maynardCoefficientFromY H R W y) +
        compatibleDivisorPairErrorSum H (maynardDivisorTupleSupport H R W)
          v W N (maynardCoefficientFromY H R W y)| := by congr 1; ring
    _ ≤ |-(N : ℝ) / W *
        incompatibleDivisorPairCommonDivisorTupleSum H
          (maynardDivisorTupleSupport H R W) (maynardCoefficientFromY H R W y)| +
        |compatibleDivisorPairErrorSum H (maynardDivisorTupleSupport H R W)
          v W N (maynardCoefficientFromY H R W y)| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul, neg_div, abs_neg, abs_of_nonneg hfactor]
      exact add_le_add le_rfl herror

end Erdos237
