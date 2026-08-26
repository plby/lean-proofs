import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.Countable
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# A short vector in a three-dimensional lattice of covolume `m * sqrt m`
-/

namespace Erdos941

open MeasureTheory Module

private theorem ball_volume_comparison {m : ℝ} (hm : 0 < m) :
    8 * (m * Real.sqrt m) < (Real.sqrt (2 * m)) ^ 3 * (Real.pi * 4 / 3) := by
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have ht : 1 < Real.sqrt (2 : ℝ) := by
    have hh := Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))
    have hp := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  have hm32 : 0 < m * Real.sqrt m := mul_pos hm hs
  have hc : 8 < 2 * Real.sqrt (2 : ℝ) * (Real.pi * 4 / 3) := by
    have hpi : 4 < Real.pi * 4 / 3 := by linarith [Real.pi_gt_three]
    nlinarith
  have hcomp := mul_lt_mul_of_pos_left hc hm32
  rw [Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ))]
  have hs2 := Real.sq_sqrt hm.le
  have ht2 := Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))
  have heq : (Real.sqrt (2 : ℝ) * Real.sqrt m) ^ 3 * (Real.pi * 4 / 3) =
      (m * Real.sqrt m) * (2 * Real.sqrt (2 : ℝ) * (Real.pi * 4 / 3)) := by
    calc
      _ = Real.sqrt (2 : ℝ) ^ 2 * Real.sqrt m ^ 2 *
          Real.sqrt (2 : ℝ) * Real.sqrt m * (Real.pi * 4 / 3) := by ring
      _ = _ := by rw [hs2, ht2]; ring
  rw [heq]
  linarith

theorem exists_short_lattice_vector
    (b : Basis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))) {m : ℝ} (hm : 0 < m)
    (hvol : volume (ZSpan.fundamentalDomain b) = ENNReal.ofReal (m * Real.sqrt m)) :
    ∃ c : Fin 3 → ℤ, (∃ i, c i ≠ 0) ∧
      ‖∑ i, (c i : ℝ) • b i‖ ^ 2 < 2 * m := by
  let L := (Submodule.span ℤ (Set.range b)).toAddSubgroup
  let : Countable L := inferInstanceAs (Countable (Submodule.span ℤ (Set.range b)))
  have hvolume : volume (ZSpan.fundamentalDomain b) *
      2 ^ finrank ℝ (EuclideanSpace ℝ (Fin 3)) <
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (Real.sqrt (2 * m))) := by
    rw [hvol, EuclideanSpace.volume_ball_fin_three]
    simp only [finrank_euclideanSpace, Fintype.card_fin]
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), ← ENNReal.ofReal_mul]
    · have hleft : ENNReal.ofReal (m * Real.sqrt m) * 2 ^ 3 =
          ENNReal.ofReal (8 * (m * Real.sqrt m)) := by
        rw [show (2 : ENNReal) ^ 3 = ENNReal.ofReal (8 : ℝ) by norm_num,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
      rw [hleft]
      exact ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr (ball_volume_comparison hm)
    · positivity
  obtain ⟨v, hv, hvball⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      (L := L) (ZSpan.isAddFundamentalDomain' b volume)
      (s := Metric.ball 0 (Real.sqrt (2 * m)))
      (by intro x hx; simpa only [Metric.mem_ball, dist_zero_right, norm_neg] using hx)
      (convex_ball _ _) hvolume
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp v.property
  have hc' : ∑ i, (c i : ℝ) • b i = (v : EuclideanSpace ℝ (Fin 3)) := by
    simpa only [Int.cast_smul_eq_zsmul] using hc
  refine ⟨c, ?_, ?_⟩
  · by_contra hzero
    push Not at hzero
    have hval : (v : EuclideanSpace ℝ (Fin 3)) = 0 := by
      rw [← hc']
      simp only [hzero, Int.cast_zero, zero_smul, Finset.sum_const_zero]
    exact hv (Subtype.ext hval)
  · rw [hc']
    have hnorm : ‖(v : EuclideanSpace ℝ (Fin 3))‖ < Real.sqrt (2 * m) := by
      simpa only [Metric.mem_ball, dist_zero_right] using hvball
    have hsq := mul_self_lt_mul_self (norm_nonneg _) hnorm
    rw [← pow_two, ← pow_two, Real.sq_sqrt (by positivity)] at hsq
    exact hsq

end Erdos941
