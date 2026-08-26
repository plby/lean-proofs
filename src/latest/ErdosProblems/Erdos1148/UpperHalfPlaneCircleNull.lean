import ErdosProblems.Erdos1148.UpperHalfPlaneVerticalNull
import Mathlib.NumberTheory.Modular

/-! # Invariant measures give zero mass to the boundary of the modular domain -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Measure
open scoped MatrixGroups

noncomputable def unitCircleToVerticalFrame : SL(2, ℝ) :=
  ⟨!![1, -1; 1 / 2, 1 / 2], by norm_num [Matrix.det_fin_two]⟩

lemma unitCircleToVerticalFrame_re_eq_zero (z : UpperHalfPlane)
    (hz : Complex.normSq (z : ℂ) = 1) : (unitCircleToVerticalFrame • z).re = 0 := by
  change ((unitCircleToVerticalFrame • z : UpperHalfPlane) : ℂ).re = 0
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [unitCircleToVerticalFrame, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Algebra.algebraMap_self, RingHom.id_apply]
  have hnorm : (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = 1 := by
    simpa only [Complex.normSq_apply, pow_two] using hz
  simp only [Complex.div_re, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, one_mul, zero_mul, mul_zero, sub_zero, add_zero,
    zero_add]
  have hnum : ((z : ℂ).re + -1) * ((1 / 2 : ℝ) * (z : ℂ).re + 1 / 2) +
      (z : ℂ).im * ((1 / 2 : ℝ) * (z : ℂ).im) = 0 := by nlinarith
  rw [← add_div, hnum, zero_div]

theorem invariant_upperHalfPlane_unitCircle_eq_zero (ν : Measure UpperHalfPlane) [SFinite ν]
    [SMulInvariantMeasure SL(2, ℝ) UpperHalfPlane ν] :
    ν {z | Complex.normSq (z : ℂ) = 1} = 0 := by
  apply measure_mono_null _ (measure_preimage_smul_null
    (invariant_upperHalfPlane_vertical_eq_zero ν 0) unitCircleToVerticalFrame)
  intro z hz
  exact unitCircleToVerticalFrame_re_eq_zero z hz

theorem invariant_upperHalfPlane_fd_boundary_eq_zero (ν : Measure UpperHalfPlane) [SFinite ν]
    [SMulInvariantMeasure SL(2, ℝ) UpperHalfPlane ν] :
    ν (ModularGroup.fd \ ModularGroup.fdo) = 0 := by
  have hsub : ModularGroup.fd \ ModularGroup.fdo ⊆
      {z | Complex.normSq (z : ℂ) = 1} ∪
        ({z | z.re = 1 / 2} ∪ {z | z.re = -(1 / 2)}) := by
    rintro z ⟨hz, hnot⟩
    by_cases hnorm : 1 < Complex.normSq (z : ℂ)
    · have habs : |z.re| = 1 / 2 := le_antisymm hz.2 (by
        by_contra h
        exact hnot ⟨hnorm, lt_of_not_ge h⟩)
      right
      exact (abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 2)).mp habs
    · left
      exact le_antisymm (le_of_not_gt hnorm) hz.1
  exact measure_mono_null hsub (measure_union_null
    (invariant_upperHalfPlane_unitCircle_eq_zero ν)
    (measure_union_null (invariant_upperHalfPlane_vertical_eq_zero ν (1 / 2))
      (invariant_upperHalfPlane_vertical_eq_zero ν (-(1 / 2)))))

end Erdos1148.DukeArithmetic
