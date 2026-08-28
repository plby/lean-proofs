import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupCoverSets
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Topology.Path
import Mathlib.Tactic.NormNum

/-!
# Explicit semicircles for the two positive planar meridians

The four paths join the common base point `1/2` to `-1/2` or `3/2`.
Their complete images, including endpoints, lie in the indicated upper
or lower slit domains and hence avoid both punctures.  This file uses
only the concrete planar domains; no fundamental-group presentation is
assumed.
-/

noncomputable section

open Set Complex
open scoped Topology ComplexConjugate

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

/-- The counterclockwise upper semicircle of radius `1/2` about zero. -/
def meridianHalfCircle (t : ℝ) : ℂ := circleMap 0 (1 / 2) (Real.pi * t)

@[fun_prop] theorem continuous_meridianHalfCircle : Continuous meridianHalfCircle := by
  unfold meridianHalfCircle circleMap
  fun_prop

@[simp] theorem meridianHalfCircle_zero : meridianHalfCircle 0 = (1 / 2 : ℂ) := by
  simp [meridianHalfCircle, circleMap]

@[simp] theorem meridianHalfCircle_one : meridianHalfCircle 1 = (-1 / 2 : ℂ) := by
  simp [meridianHalfCircle, circleMap, exp_pi_mul_I]
  ring

theorem meridianHalfCircle_im_pos {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    0 < (meridianHalfCircle t).im := by
  rw [meridianHalfCircle, circleMap_zero_im]
  apply mul_pos (by norm_num)
  exact Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos ht0)
    (by nlinarith [Real.pi_pos])

theorem meridianHalfCircle_mem_upperSlitPlane (t : unitInterval) :
    meridianHalfCircle t ∈ upperSlitPlane := by
  by_cases ht0 : (t : ℝ) = 0
  · rw [ht0, meridianHalfCircle_zero]
    norm_num [upperSlitPlane]
  by_cases ht1 : (t : ℝ) = 1
  · rw [ht1, meridianHalfCircle_one]
    norm_num [upperSlitPlane]
  apply Or.inl
  apply meridianHalfCircle_im_pos
  · have := t.property.1
    exact lt_of_le_of_ne this (Ne.symm ht0)
  · have := t.property.2
    exact lt_of_le_of_ne this ht1

private theorem conj_mem_lowerSlitPlane_iff (z : ℂ) :
    conj z ∈ lowerSlitPlane ↔ z ∈ upperSlitPlane := by
  simp [lowerSlitPlane, upperSlitPlane]

private theorem one_sub_mem_upperSlitPlane_iff (z : ℂ) :
    1 - z ∈ upperSlitPlane ↔ z ∈ lowerSlitPlane := by
  simp [upperSlitPlane, lowerSlitPlane, ne_comm, and_comm, eq_sub_iff_add_eq]

private theorem one_sub_mem_lowerSlitPlane_iff (z : ℂ) :
    1 - z ∈ lowerSlitPlane ↔ z ∈ upperSlitPlane := by
  simp [upperSlitPlane, lowerSlitPlane, ne_comm, and_comm, eq_sub_iff_add_eq]

def upperZeroArc : Path (1 / 2 : ℂ) (-1 / 2) :=
  Path.ofLine continuous_meridianHalfCircle.continuousOn
    meridianHalfCircle_zero meridianHalfCircle_one

def lowerZeroArc : Path (1 / 2 : ℂ) (-1 / 2) :=
  Path.ofLine (f := fun t : ℝ => conj (meridianHalfCircle t)) (by fun_prop)
    (by simp [map_ofNat]) (by simp [map_ofNat])

def upperOneArc : Path (1 / 2 : ℂ) (3 / 2) :=
  Path.ofLine (f := fun t : ℝ => 1 - conj (meridianHalfCircle t)) (by fun_prop)
    (by norm_num [map_ofNat]) (by norm_num [map_ofNat])

def lowerOneArc : Path (1 / 2 : ℂ) (3 / 2) :=
  Path.ofLine (f := fun t : ℝ => 1 - meridianHalfCircle t) (by fun_prop)
    (by norm_num) (by norm_num)

@[simp] theorem upperZeroArc_apply (t : unitInterval) :
    upperZeroArc t = (1 / 2 : ℂ) * exp ((Real.pi : ℂ) * I * (t : ℝ)) := by
  change meridianHalfCircle t = _
  unfold meridianHalfCircle
  rw [circleMap_zero]
  push_cast
  congr 1
  congr 1
  ring

@[simp] theorem lowerZeroArc_apply (t : unitInterval) :
    lowerZeroArc t = (1 / 2 : ℂ) * exp (-((Real.pi : ℂ) * I * (t : ℝ))) := by
  change conj (upperZeroArc t) = _
  rw [upperZeroArc_apply]
  simp only [map_mul, map_div₀, map_one, map_ofNat, ← exp_conj, conj_ofReal, conj_I]
  congr 1
  congr 1
  ring

@[simp] theorem upperOneArc_apply (t : unitInterval) :
    upperOneArc t = 1 - (1 / 2 : ℂ) * exp (-((Real.pi : ℂ) * I * (t : ℝ))) := by
  change 1 - lowerZeroArc t = _
  rw [lowerZeroArc_apply]

@[simp] theorem lowerOneArc_apply (t : unitInterval) :
    lowerOneArc t = 1 - (1 / 2 : ℂ) * exp ((Real.pi : ℂ) * I * (t : ℝ)) := by
  change 1 - upperZeroArc t = _
  rw [upperZeroArc_apply]

theorem upperZeroArc_mem_upperSlitPlane (t : unitInterval) :
    upperZeroArc t ∈ upperSlitPlane := meridianHalfCircle_mem_upperSlitPlane t

theorem lowerZeroArc_mem_lowerSlitPlane (t : unitInterval) :
    lowerZeroArc t ∈ lowerSlitPlane :=
  (conj_mem_lowerSlitPlane_iff _).mpr (meridianHalfCircle_mem_upperSlitPlane t)

theorem upperOneArc_mem_upperSlitPlane (t : unitInterval) :
    upperOneArc t ∈ upperSlitPlane :=
  (one_sub_mem_upperSlitPlane_iff _).mpr (lowerZeroArc_mem_lowerSlitPlane t)

theorem lowerOneArc_mem_lowerSlitPlane (t : unitInterval) :
    lowerOneArc t ∈ lowerSlitPlane :=
  (one_sub_mem_lowerSlitPlane_iff _).mpr (upperZeroArc_mem_upperSlitPlane t)

theorem upperZeroArc_avoids_punctures (t : unitInterval) :
    upperZeroArc t ≠ 0 ∧ upperZeroArc t ≠ 1 :=
  upperSlitPlane_subset_punctured (upperZeroArc_mem_upperSlitPlane t)

theorem lowerZeroArc_avoids_punctures (t : unitInterval) :
    lowerZeroArc t ≠ 0 ∧ lowerZeroArc t ≠ 1 :=
  lowerSlitPlane_subset_punctured (lowerZeroArc_mem_lowerSlitPlane t)

theorem upperOneArc_avoids_punctures (t : unitInterval) :
    upperOneArc t ≠ 0 ∧ upperOneArc t ≠ 1 :=
  upperSlitPlane_subset_punctured (upperOneArc_mem_upperSlitPlane t)

theorem lowerOneArc_avoids_punctures (t : unitInterval) :
    lowerOneArc t ≠ 0 ∧ lowerOneArc t ≠ 1 :=
  lowerSlitPlane_subset_punctured (lowerOneArc_mem_lowerSlitPlane t)

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
