import ErdosProblems.Erdos237.SieveScaleBounds
import ErdosProblems.Erdos237.SieveDecomposition
import ErdosProblems.Erdos237.DyadicDiagonal

/-!
# The S1 limit for arbitrary supported weights and for the dyadic candidate

All tuple dimensions and shifts are arbitrary. No admissibility is needed
for S1; it enters the prime-weighted S2 calculation through the residue.
-/

namespace Erdos237

open Finset Filter BoundedGaps.Maynard
open scoped BigOperators

theorem eventually_coversShiftDifferencePrimes (H : Finset ℕ) :
    ∀ᶠ N : ℕ in atTop, CoversShiftDifferencePrimes H (engelsmaMaynardModulus N) := by
  filter_upwards [tendsto_shifted_tripleLogCutoff.eventually_ge_atTop (H.sup id)]
    with N hN
  apply coversShiftDifferencePrimes_of_diameter
  intro a b _
  have ha : a.val ≤ H.sup id := le_sup (f := id) a.property
  have hb : b.val ≤ H.sup id := le_sup (f := id) b.property
  unfold Nat.dist
  omega

noncomputable def sieveYWeight (H : Finset ℕ) (alpha : ℝ)
    (y : ℕ → (H → ℕ) → ℝ) (v : ℕ → ℕ) (N : ℕ) : ℕ → ℝ :=
  preSievedSquareDivisorWeight H
    (maynardDivisorTupleSupport H (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N))
    (maynardCoefficientFromY H (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N) (y N))
    (v N) (engelsmaMaynardModulus N)

theorem sieveYWeight_nonneg (H : Finset ℕ) (alpha : ℝ)
    (y : ℕ → (H → ℕ) → ℝ) (v : ℕ → ℕ) (N n : ℕ) :
    0 ≤ sieveYWeight H alpha y v N n := preSievedSquareDivisorWeight_nonneg _ _ _ _ _ _

theorem tendsto_normalized_s1_rounding_error {H : Finset ℕ} {alpha B : ℝ}
    (halpha : 0 < alpha) (halpha' : alpha < 1 / 4) (hB : 0 ≤ B)
    (y : ℕ → (H → ℕ) → ℝ) (v : ℕ → ℕ)
    (hy : ∀ N, IsSupportedMaynardY H (engelsmaMaynardRadius alpha N)
      (engelsmaMaynardModulus N) (y N))
    (hbound : ∀ N r, |y N r| ≤ B) :
    Tendsto (fun N : ℕ =>
      compatibleDivisorPairErrorSum H
        (maynardDivisorTupleSupport H (engelsmaMaynardRadius alpha N)
          (engelsmaMaynardModulus N)) (v N) (engelsmaMaynardModulus N) N
        (maynardCoefficientFromY H (engelsmaMaynardRadius alpha N)
          (engelsmaMaynardModulus N) (y N)) / sieveScale H alpha N)
      atTop (nhds 0) := by
  apply squeeze_zero_norm' ?_ (tendsto_normalized_coefficient_mass halpha halpha' hB y hy hbound)
  filter_upwards [eventually_sieveScale_pos H halpha] with N hS
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hS]
  apply div_le_div_of_nonneg_right ?_ hS.le
  exact abs_compatibleDivisorPairErrorSum_le_coefficientMass
    (primorial_pos _) (fun _ hd => isMaynardDivisorTuple_of_mem_support hd)

theorem tendsto_sieveWeightSum_of_yDiagonal {H : Finset ℕ} {alpha B I : ℝ}
    (halpha : 0 < alpha) (halpha' : alpha < 1 / 4) (hB : 0 ≤ B)
    (y : ℕ → (H → ℕ) → ℝ) (v : ℕ → ℕ)
    (hy : ∀ N, IsSupportedMaynardY H (engelsmaMaynardRadius alpha N)
      (engelsmaMaynardModulus N) (y N))
    (hbound : ∀ N r, |y N r| ≤ B)
    (hdiag : Tendsto (fun N : ℕ => maynardYDiagonalSum H (engelsmaMaynardRadius alpha N)
      (engelsmaMaynardModulus N) (y N) / sieveCoordinateScale alpha N ^ Fintype.card H)
      atTop (nhds I)) :
    Tendsto (fun N : ℕ => sieveWeightSum N (sieveYWeight H alpha y v N) /
      sieveScale H alpha N) atTop (nhds I) := by
  have hcross := tendsto_normalized_s1_cross halpha hB y hy hbound
  have herror := tendsto_normalized_s1_rounding_error halpha halpha' hB y v hy hbound
  have hlim := (hdiag.sub hcross).add herror
  simp only [sub_zero, add_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_coversShiftDifferencePrimes H,
    eventually_sieveCoordinateScale_pos halpha, eventually_gt_atTop 0] with N hc hA hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hw : (engelsmaMaynardModulus N : ℝ) ≠ 0 := by
    exact_mod_cast (primorial_pos _).ne'
  rw [sieveYWeight, sieveWeightSum_eq_yDiagonal_sub_cross_add_error (hy N) hc]
  unfold sieveScale
  field_simp

theorem tendsto_dyadic_sieveWeightSum {H : Finset ℕ} {L k : ℕ}
    (hL : 0 < L) (hk : 2 ^ L ≤ k) (e : H ≃ Fin k)
    {alpha : ℝ} (halpha : 0 < alpha) (halpha' : alpha < 1 / 4) (v : ℕ → ℕ) :
    Tendsto (fun N : ℕ =>
      sieveWeightSum N (sieveYWeight H alpha (dyadicY (L := L) e alpha) v N) /
        sieveScale H alpha N)
      atTop (nhds (boxDenominator (dyadicSquareMass L k) (dyadicUpper L k) k *
        (1 / 2 : ℝ) ^ k)) :=
  tendsto_sieveWeightSum_of_yDiagonal halpha halpha' (dyadicWeightBound_nonneg L k)
    (dyadicY e alpha) v (dyadicY_supported e alpha) (abs_dyadicY_le e alpha)
    (tendsto_dyadicY_diagonal hL hk e halpha)

end Erdos237
