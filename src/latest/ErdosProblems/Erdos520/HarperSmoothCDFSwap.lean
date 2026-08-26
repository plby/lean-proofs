import ErdosProblems.Erdos520.HarperEsseen
import Mathlib.MeasureTheory.Integral.Prod

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open MeasureTheory ProbabilityTheory Set

namespace Erdos
namespace Problem520

/-! # Fubini formula for smoothed distribution functions -/

/-- Smoothing the CDF of `mu` by `kappa` is equivalently the `mu`-average
of translated values of the CDF of `kappa`. -/
theorem harperSmooth_cdf_eq_integral_cdf_sub
    (mu kappa : Measure ℝ)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure kappa]
    (x : ℝ) :
    harperSmooth kappa (cdf mu) x =
      ∫ z, cdf kappa (x - z) ∂mu := by
  let H : ℝ → ℝ → ℝ := fun y z ↦
    if z + y ≤ x then 1 else 0
  have hHmeas : Measurable (Function.uncurry H) := by
    dsimp [H, Function.uncurry]
    exact Measurable.ite
      (measurableSet_le (measurable_snd.add measurable_fst) measurable_const)
      measurable_const measurable_const
  have hHint : Integrable (Function.uncurry H) (kappa.prod mu) := by
    refine (integrable_const (μ := kappa.prod mu) (1 : ℝ)).mono'
      hHmeas.aestronglyMeasurable ?_
    filter_upwards with p
    dsimp [H, Function.uncurry]
    split_ifs <;> simp
  have hleft (y : ℝ) : (∫ z, H y z ∂mu) = cdf mu (x - y) := by
    rw [cdf_eq_real, ← integral_indicator_one measurableSet_Iic]
    apply integral_congr_ae
    filter_upwards with z
    dsimp [H]
    by_cases hz : z ∈ Iic (x - y)
    · have hz' : z + y ≤ x := by
        have : z ≤ x - y := hz
        linarith
      rw [Set.indicator_of_mem hz, if_pos hz']
      simp
    · have hz' : ¬ z + y ≤ x := by
        have : x - y < z := by simpa only [mem_Iic, not_le] using! hz
        linarith
      rw [Set.indicator_of_notMem hz, if_neg hz']
  have hright (z : ℝ) : (∫ y, H y z ∂kappa) = cdf kappa (x - z) := by
    rw [cdf_eq_real, ← integral_indicator_one measurableSet_Iic]
    apply integral_congr_ae
    filter_upwards with y
    dsimp [H]
    by_cases hy : y ∈ Iic (x - z)
    · have hy' : z + y ≤ x := by
        have : y ≤ x - z := hy
        linarith
      rw [Set.indicator_of_mem hy, if_pos hy']
      simp
    · have hy' : ¬ z + y ≤ x := by
        have : x - z < y := by simpa only [mem_Iic, not_le] using! hy
        linarith
      rw [Set.indicator_of_notMem hy, if_neg hy']
  unfold harperSmooth
  calc
    (∫ y, cdf mu (x - y) ∂kappa) =
        ∫ y, ∫ z, H y z ∂mu ∂kappa := by
      apply integral_congr_ae
      filter_upwards with y
      exact (hleft y).symm
    _ = ∫ z, ∫ y, H y z ∂kappa ∂mu :=
      integral_integral_swap hHint
    _ = ∫ z, cdf kappa (x - z) ∂mu := by
      apply integral_congr_ae
      filter_upwards with z
      exact hright z

end Problem520
end Erdos
