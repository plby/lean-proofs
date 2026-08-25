import ErdosProblems.Erdos237b.PrimeSieveError
import ErdosProblems.Erdos237b.S2ArithmeticLower
import ErdosProblems.Erdos237b.ShiftedPrimeLimit
import BoundedGaps.Maynard.ImprovedGPY.S2RestrictedMainReindex
import BoundedGaps.Maynard.MaynardS2TotientFactorization

/-! Exact generic S2 main/error split and normalization. -/

namespace Erdos237b

open Finset Filter BoundedGaps.Maynard
open scoped BigOperators

theorem restrictedMainCoefficient_eq_s2YArithmetic {H : Finset ℕ} (R W : ℕ)
    (y : (H → ℕ) → ℝ) (m : H) :
    restrictedMainArithmeticCoefficient H (maynardDivisorTupleSupport H R W) W
      (maynardCoefficientFromY H R W y) m =
      (Nat.totient W : ℝ)⁻¹ * s2YArithmeticCoefficient H R W y m := by
  have hD : ∀ d ∈ maynardDivisorTupleSupport H R W, IsMaynardDivisorTuple H R W d :=
    fun _ hd => isMaynardDivisorTuple_of_mem_support hd
  unfold restrictedMainArithmeticCoefficient
  rw [restrictedDivisorPairModulusTotientSum_eq_invTotient_mul m hD]
  congr 1
  rw [compatibleDivisorPairRestrictedTotientKernel_eq_commonDivisorS2TupleSum m hD,
    compatibleRestrictedS2SubtypeSum_eq_membershipSum,
    compatibleRestrictedS2_eq_unrestricted_sub_incompatible,
    unrestrictedRestrictedS2_eq_quadraticTransform m hD,
    maynardS2RestrictedQuadraticTransform_eq_yDiagonal]
  rfl

noncomputable def s2YMain (H : Finset ℕ) (alpha : ℝ)
    (y : ℕ → (H → ℕ) → ℝ) (N : ℕ) : ℝ :=
  ∑ m : H, shiftedPrimeIntervalCount N m.val *
    ((Nat.totient (engelsmaMaynardModulus N) : ℝ)⁻¹ *
      s2YArithmeticCoefficient H (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N) (y N) m)

theorem eventually_sieveS2_eq_main_add_error {H : Finset ℕ} {theta delta : ℝ}
    (hthetaHalf : theta < 1 / 2) (hdelta : 0 < delta) (hdeltaTheta : delta < theta / 2)
    (y : ℕ → (H → ℕ) → ℝ) (v : ℕ → ℕ) :
    ∀ᶠ N : ℕ in atTop, primeWeightedSieveSum H N
      (sieveYWeight H (theta / 2 - delta) y v N) =
      s2YMain H (theta / 2 - delta) y N + s2YError H (theta / 2 - delta) y v N := by
  filter_upwards [eventually_coversShiftDifferencePrimes H,
    eventually_engelsmaMaynardRadius_le hthetaHalf hdelta hdeltaTheta] with N hcoverage hRN
  have hD : ∀ d ∈ maynardDivisorTupleSupport H (engelsmaMaynardRadius (theta / 2 - delta) N)
      (engelsmaMaynardModulus N), IsMaynardDivisorTuple H
        (engelsmaMaynardRadius (theta / 2 - delta) N) (engelsmaMaynardModulus N) d :=
    fun _ hd => isMaynardDivisorTuple_of_mem_support hd
  rw [sieveYWeight, primeWeightedSieveSum_preSieved_eq_compatiblePrimeWeightedPairSum hD hcoverage,
    compatiblePrimeWeightedPairSum_eq_restrictedOuterMain_addError hD hRN,
    compatiblePairRestrictedMainOuter_eq_shift_sum]
  congr 1
  unfold s2YMain
  apply sum_congr rfl
  intro m _
  rw [restrictedMainCoefficient_eq_s2YArithmetic]
  rfl

theorem s2YMain_normalized {H : Finset ℕ} {alpha : ℝ} (y : ℕ → (H → ℕ) → ℝ)
    {N : ℕ} (hN : 0 < N) (hA : 0 < sieveCoordinateScale alpha N) :
    s2YMain H alpha y N / sieveScale H alpha N =
      ∑ m : H, (shiftedPrimeIntervalCount N m.val / N *
        Real.log (engelsmaMaynardRadius alpha N)) *
        (s2YArithmeticCoefficient H (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N)
          (y N) m / sieveCoordinateScale alpha N ^ (Fintype.card H + 1)) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hw : (engelsmaMaynardModulus N : ℝ) ≠ 0 := by exact_mod_cast (primorial_pos _).ne'
  have hphi : (Nat.totient (engelsmaMaynardModulus N) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (primorial_pos _)).ne'
  unfold s2YMain
  rw [sum_div]
  apply sum_congr rfl
  intro m _
  rw [pow_succ, sieveScale]
  have hrel : sieveCoordinateScale alpha N * (Nat.totient (engelsmaMaynardModulus N) : ℝ)⁻¹ =
      Real.log (engelsmaMaynardRadius alpha N) / engelsmaMaynardModulus N := by
    unfold sieveCoordinateScale
    rw [preSieveSingularSeries_eq_totient_div]
    change ((Nat.totient (engelsmaMaynardModulus N) : ℝ) / engelsmaMaynardModulus N * _) * _ = _
    field_simp
  field_simp at hrel ⊢
  linear_combination (shiftedPrimeIntervalCount N m.val *
    s2YArithmeticCoefficient H (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N)
      (y N) m) * hrel

end Erdos237b
