import ErdosProblems.Erdos1038.ResidualWidthStrictReference

/-!
# Uniform geometric comparison for scaled Lagrange coefficients

A uniform fraction of the positive inverse boundary gives an explicit
geometric majorant for every scaled inverse-series coefficient.
-/

set_option warningAsError false

open scoped BigOperators Real
open Finset Set

namespace Erdos1038

noncomputable section

/-- A uniform comparison strictly inside the positive inverse boundary gives
an explicit pointwise geometric majorant for every scaled coefficient. -/
theorem scaledLagrangeCoefficient_le_uniform_geometric_of_comparison
    {iota : Type*} [Fintype iota]
    (a d : iota → ℝ) (ha : ∀ i, 0 < a i)
    (hd : d ∈ positiveCoordinates iota)
    {s q : ℝ} (hs : 0 < s) (hsd : ∀ i, s < d i)
    (hq : q ∈ Ioo (0 : ℝ) 1)
    (hcomparison : inverseMonomial a d ≤
      q * (s / lagrangePhiValue a d s))
    (n : ℕ) :
    scaledLagrangeCoefficient a n d ≤
      s * (2 * q / (1 + q)) ^ n := by
  let z : ℝ := inverseMonomial a d
  let boundary : ℝ := s / lagrangePhiValue a d s
  let zLarge : ℝ := ((1 + q) / 2) * boundary
  let ratio : ℝ := 2 * q / (1 + q)
  have hz : 0 < z := by
    simpa only [z] using! inverseMonomial_pos a d
  have hphi : 0 < lagrangePhiValue a d s :=
    lagrangePhiValue_pos a d hd hsd
  have hboundary : 0 < boundary := by
    dsimp only [boundary]
    exact div_pos hs hphi
  have hzLe : z ≤ q * boundary := by
    simpa only [z, boundary] using! hcomparison
  have hqMid : q < (1 + q) / 2 := by linarith [hq.2]
  have hmidOne : (1 + q) / 2 < 1 := by linarith [hq.2]
  have hzLargePos : 0 < zLarge := by
    dsimp only [zLarge]
    exact mul_pos (div_pos (by linarith [hq.1]) (by norm_num)) hboundary
  have hzLargeLt : zLarge < boundary := by
    dsimp only [zLarge]
    exact mul_lt_of_lt_one_left hboundary hmidOne
  have hzLtLarge : z < zLarge := by
    exact hzLe.trans_lt (by
      dsimp only [zLarge]
      exact mul_lt_mul_of_pos_right hqMid hboundary)
  have hlarge : Summable (fun k : ℕ ↦
      PowerSeries.coeff k
          (PowerSeries.lagrangeInversePowerSeries a d) * zLarge ^ k) := by
    apply summable_lagrangeInversePowerSeries_of_lt
      a d ha hd hs hsd hzLargePos.le
    simpa only [boundary] using! hzLargeLt
  let total : ℝ := ∑' k : ℕ,
    PowerSeries.coeff k
        (PowerSeries.lagrangeInversePowerSeries a d) * zLarge ^ k
  have hlargeNonneg (k : ℕ) :
      0 ≤ PowerSeries.coeff k
          (PowerSeries.lagrangeInversePowerSeries a d) * zLarge ^ k :=
    mul_nonneg
      (coeff_lagrangeInversePowerSeries_nonneg a d ha hd k)
      (pow_nonneg hzLargePos.le k)
  have htotalNonneg : 0 ≤ total := by
    exact tsum_nonneg hlargeNonneg
  have htermLe (k : ℕ) :
      PowerSeries.coeff k
          (PowerSeries.lagrangeInversePowerSeries a d) * zLarge ^ k ≤
        total := by
    exact hlarge.le_tsum k (fun m _hm ↦ hlargeNonneg m)
  have htotalLe : total ≤ s := by
    have hvalue := lagrangeInverseValue_lt_comparison
      a d ha hd hs hsd hzLargePos.le
      (by simpa only [boundary] using! hzLargeLt)
    exact (by simpa only [total, lagrangeInverseValue] using! hvalue.le)
  have hqden : 1 + q ≠ 0 := by linarith [hq.1]
  have hratioNonneg : 0 ≤ ratio := by
    dsimp only [ratio]
    exact div_nonneg (mul_nonneg (by norm_num) hq.1.le) (by linarith [hq.1])
  have hzRatioNonneg : 0 ≤ z / zLarge :=
    div_nonneg hz.le hzLargePos.le
  have hzRatioLe : z / zLarge ≤ ratio := by
    apply (div_le_iff₀ hzLargePos).2
    calc
      z ≤ q * boundary := hzLe
      _ = ratio * zLarge := by
        dsimp only [ratio, zLarge]
        field_simp [hqden]
  have hscaled :
      scaledLagrangeCoefficient a n d =
        (PowerSeries.coeff n
            (PowerSeries.lagrangeInversePowerSeries a d) * zLarge ^ n) *
          (z / zLarge) ^ n := by
    rw [scaledLagrangeCoefficient_eq_inverseCoeff_mul_pow a d hd n]
    have hzFactor : zLarge * (z / zLarge) = z := by
      field_simp [hzLargePos.ne']
    change PowerSeries.coeff n
          (PowerSeries.lagrangeInversePowerSeries a d) * z ^ n = _
    calc
      PowerSeries.coeff n
            (PowerSeries.lagrangeInversePowerSeries a d) * z ^ n =
          PowerSeries.coeff n
            (PowerSeries.lagrangeInversePowerSeries a d) *
              (zLarge * (z / zLarge)) ^ n := by rw [hzFactor]
      _ = _ := by rw [mul_pow]; ring
  rw [hscaled]
  calc
    (PowerSeries.coeff n
          (PowerSeries.lagrangeInversePowerSeries a d) * zLarge ^ n) *
        (z / zLarge) ^ n ≤
      total * (z / zLarge) ^ n :=
        mul_le_mul_of_nonneg_right (htermLe n)
          (pow_nonneg hzRatioNonneg n)
    _ ≤ total * ratio ^ n :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hzRatioNonneg hzRatioLe n) htotalNonneg
    _ ≤ s * ratio ^ n :=
      mul_le_mul_of_nonneg_right htotalLe (pow_nonneg hratioNonneg n)

/-- The uniform geometric majorant immediately gives absolute summability of
the scaled coefficient sequence. -/
theorem summable_scaledLagrangeCoefficient_of_uniform_comparison
    {iota : Type*} [Fintype iota]
    (a d : iota → ℝ) (ha : ∀ i, 0 < a i)
    (hd : d ∈ positiveCoordinates iota)
    {s q : ℝ} (hs : 0 < s) (hsd : ∀ i, s < d i)
    (hq : q ∈ Ioo (0 : ℝ) 1)
    (hcomparison : inverseMonomial a d ≤
      q * (s / lagrangePhiValue a d s)) :
    Summable (fun n : ℕ ↦ scaledLagrangeCoefficient a n d) := by
  let ratio : ℝ := 2 * q / (1 + q)
  have hratioNonneg : 0 ≤ ratio := by
    dsimp only [ratio]
    exact div_nonneg (mul_nonneg (by norm_num) hq.1.le) (by linarith [hq.1])
  have hratioOne : ratio < 1 := by
    dsimp only [ratio]
    exact (div_lt_one (by linarith [hq.1] : 0 < 1 + q)).2 (by linarith [hq.2])
  have hratioNorm : ‖ratio‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hratioNonneg]
    exact hratioOne
  have hmajor : Summable (fun n : ℕ ↦ s * ratio ^ n) :=
    (summable_geometric_of_norm_lt_one hratioNorm).mul_left s
  apply hmajor.of_nonneg_of_le
  · intro n
    exact scaledLagrangeCoefficient_nonneg a d ha hd n
  · intro n
    exact scaledLagrangeCoefficient_le_uniform_geometric_of_comparison
      a d ha hd hs hsd hq hcomparison n

end

end Erdos1038
