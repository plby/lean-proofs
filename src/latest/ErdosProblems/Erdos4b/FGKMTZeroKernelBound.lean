/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import BoundedGaps.BombieriVinogradov.Analytic.DirichletNonexceptionalZeroKernel
import BoundedGaps.BombieriVinogradov.Analytic.DirichletZeroReciprocalSum

/-!
# Complete zero-kernel sums under a supplied real-part bound

The removable kernel is controlled without any exceptional-zero partition.
The extra logarithm is harmless at the exponential-saving scale. All zeros
and their multiplicities in the existing explicit formula are retained.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators
open BoundedGaps.Maynard

theorem norm_explicitFormulaKernel_le_of_re_le {x alpha : ℝ} {rho : ℂ}
    (hx : 1 ≤ x) (hlog : 1 ≤ Real.log x)
    (hrho : 0 ≤ rho.re) (halpha : rho.re ≤ alpha) :
    ‖dirichletExplicitFormulaKernel x rho‖ ≤
      4 * x ^ alpha * Real.log x / (1 + |rho.im|) := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hlog0 : 0 ≤ Real.log x := zero_le_one.trans hlog
  have hpow : x ^ rho.re ≤ x ^ alpha :=
    Real.rpow_le_rpow_of_exponent_le hx halpha
  have hpow1 : 1 ≤ x ^ rho.re := Real.one_le_rpow hx hrho
  have hpow0 : 0 ≤ x ^ alpha := Real.rpow_nonneg hxpos.le _
  have hden : 0 < 1 + |rho.im| := by positivity
  apply (le_div_iff₀ hden).mpr
  by_cases hsmall : |rho.im| ≤ 1
  · have hkernel := norm_dirichletExplicitFormulaKernel_le_rpow_mul_log hx hrho
    calc
      _ ≤ (x ^ rho.re * Real.log x) * (1 + |rho.im|) :=
        mul_le_mul_of_nonneg_right hkernel hden.le
      _ ≤ (x ^ alpha * Real.log x) * 2 := by gcongr; linarith
      _ ≤ _ := by nlinarith [mul_nonneg hpow0 hlog0]
  · have hlarge : 1 < |rho.im| := lt_of_not_ge hsmall
    have hrhone : rho ≠ 0 := by
      intro hz
      subst rho
      norm_num at hlarge
    have hnorm : 0 < ‖rho‖ := norm_pos_iff.mpr hrhone
    have hdennorm : 1 + |rho.im| ≤ 2 * ‖rho‖ := by
      nlinarith [Complex.abs_im_le_norm rho]
    have hquot : ‖dirichletExplicitFormulaKernel x rho‖ ≤
        (x ^ rho.re + 1) / ‖rho‖ := by
      rw [dirichletExplicitFormulaKernel_eq_cpow_sub_one_div hxpos hrhone, norm_div]
      apply div_le_div_of_nonneg_right _ hnorm.le
      calc
        ‖(x : ℂ) ^ rho - 1‖ ≤ ‖(x : ℂ) ^ rho‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = _ := by rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos, norm_one]
    calc
      _ ≤ ((x ^ rho.re + 1) / ‖rho‖) * (1 + |rho.im|) :=
        mul_le_mul_of_nonneg_right hquot hden.le
      _ ≤ ((x ^ rho.re + 1) / ‖rho‖) * (2 * ‖rho‖) :=
        mul_le_mul_of_nonneg_left hdennorm (by positivity)
      _ = 2 * (x ^ rho.re + 1) := by field_simp
      _ ≤ 4 * x ^ alpha := by linarith
      _ ≤ _ := by nlinarith

theorem norm_completeZeroKernelSum_le_of_re_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x T alpha : ℝ} (hx : 1 ≤ x) (hlog : 1 ≤ Real.log x)
    (hzeros : ∀ rho ∈ dirichletNontrivialLFunctionZerosFinset chi T, rho.re ≤ alpha) :
    ‖dirichletNontrivialZeroKernelSum chi x T‖ ≤
      (4 * x ^ alpha * Real.log x) *
        dirichletNontrivialZeroReciprocalMultiplicitySum chi T := by
  have hterm (rho : ℂ) (hrho : rho ∈ dirichletNontrivialLFunctionZerosFinset chi T) :
      ‖(analyticOrderNatAt (DirichletCharacter.LFunction chi) rho : ℂ) *
          dirichletExplicitFormulaKernel x rho‖ ≤
        (4 * x ^ alpha * Real.log x) *
          ((analyticOrderNatAt (DirichletCharacter.LFunction chi) rho : ℝ) /
            (1 + |rho.im|)) := by
    have hzero := (mem_dirichletNontrivialLFunctionZerosFinset_iff.mp hrho).1
    have hkernel := norm_explicitFormulaKernel_le_of_re_le hx hlog hzero.2.1.le
      (hzeros rho hrho)
    rw [norm_mul, Complex.norm_natCast]
    calc
      _ ≤ (analyticOrderNatAt (DirichletCharacter.LFunction chi) rho : ℝ) *
          (4 * x ^ alpha * Real.log x / (1 + |rho.im|)) :=
        mul_le_mul_of_nonneg_left hkernel (Nat.cast_nonneg _)
      _ = _ := by ring
  rw [dirichletNontrivialZeroKernelSum]
  calc
    _ ≤ ∑ rho ∈ dirichletNontrivialLFunctionZerosFinset chi T,
        ‖(analyticOrderNatAt (DirichletCharacter.LFunction chi) rho : ℂ) *
          dirichletExplicitFormulaKernel x rho‖ := norm_sum_le _ _
    _ ≤ ∑ rho ∈ dirichletNontrivialLFunctionZerosFinset chi T,
        (4 * x ^ alpha * Real.log x) *
          ((analyticOrderNatAt (DirichletCharacter.LFunction chi) rho : ℝ) /
            (1 + |rho.im|)) := Finset.sum_le_sum hterm
    _ = _ := by rw [← Finset.mul_sum, dirichletNontrivialZeroReciprocalMultiplicitySum]

theorem exists_completeZeroKernelSum_bound :
    ∃ N : ℕ, 37 ≤ N ∧ ∀ (q : ℕ) [NeZero q]
      (chi : DirichletCharacter ℂ q) (x T alpha : ℝ),
      1 ≤ x → 1 ≤ Real.log x → 2 ≤ T →
      (∀ rho ∈ dirichletNontrivialLFunctionZerosFinset chi T, rho.re ≤ alpha) →
      ‖dirichletNontrivialZeroKernelSum chi x T‖ ≤
        32 * (N : ℝ) * x ^ alpha * Real.log x *
          Real.log ((q : ℝ) * (T + 2)) ^ 2 := by
  obtain ⟨N, hN, hsum⟩ := exists_nat_dirichletNontrivialZeroReciprocalMultiplicitySum_le
  refine ⟨N, hN, ?_⟩
  intro q _ chi x T alpha hx hlog hT hzeros
  calc
    _ ≤ (4 * x ^ alpha * Real.log x) *
        dirichletNontrivialZeroReciprocalMultiplicitySum chi T :=
      norm_completeZeroKernelSum_le_of_re_le chi hx hlog hzeros
    _ ≤ (4 * x ^ alpha * Real.log x) *
        (8 * (N : ℝ) * Real.log ((q : ℝ) * (T + 2)) ^ 2) :=
      mul_le_mul_of_nonneg_left (hsum q chi T hT)
        (mul_nonneg (by positivity) (zero_le_one.trans hlog))
    _ = _ := by ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.norm_explicitFormulaKernel_le_of_re_le
#print axioms Erdos4b.FGKMT.exists_completeZeroKernelSum_bound
