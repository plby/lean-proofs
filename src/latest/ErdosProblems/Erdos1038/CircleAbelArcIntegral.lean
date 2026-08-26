import ErdosProblems.Erdos1038.CircleAbelKernel
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Integrating the Abel circle kernel on centered arcs

The regularized logarithmic kernel has an absolutely and uniformly
convergent cosine series.  We integrate that series first in the inner arc
variable and then in the outer one, retaining every normalization factor.
-/

set_option warningAsError false

open MeasureTheory Set

namespace Erdos1038

noncomputable section

private def circleAbelKernelTerm
    (rho theta : ℝ) (n : ℕ) : C(ℝ, ℝ) where
  toFun phi :=
    -(rho ^ (n + 1) *
      Real.cos (((n + 1 : ℕ) : ℝ) * (theta - phi)) /
        ((n + 1 : ℕ) : ℝ))
  continuous_toFun := by fun_prop

private lemma summable_abs_pow_succ {rho : ℝ} (hrho : |rho| < 1) :
    Summable (fun n : ℕ ↦ |rho| ^ (n + 1)) := by
  have hgeom := summable_geometric_of_lt_one (abs_nonneg rho) hrho
  exact (hgeom.mul_left |rho|).congr fun n ↦ by
    rw [pow_succ]
    ring

private lemma circleAbelKernelTerm_norm_restrict_le
    {rho theta left right : ℝ} (n : ℕ) :
    ‖(circleAbelKernelTerm rho theta n).restrict
        (⟨uIcc left right, isCompact_uIcc⟩ :
          TopologicalSpace.Compacts ℝ)‖ ≤
      |rho| ^ (n + 1) := by
  apply (ContinuousMap.norm_le _ (pow_nonneg (abs_nonneg rho) _)).2
  intro phi
  change
    |-(rho ^ (n + 1) *
        Real.cos (((n + 1 : ℕ) : ℝ) * (theta - phi.1)) /
          ((n + 1 : ℕ) : ℝ))| ≤ |rho| ^ (n + 1)
  rw [abs_neg, abs_div, abs_mul, abs_pow,
    abs_of_pos (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ))]
  have hcos : |Real.cos
      (((n + 1 : ℕ) : ℝ) * (theta - phi.1))| ≤ 1 :=
    Real.abs_cos_le_one _
  have hfreq : 1 ≤ ((n + 1 : ℕ) : ℝ) := by norm_num
  calc
    |rho| ^ (n + 1) *
          |Real.cos (((n + 1 : ℕ) : ℝ) * (theta - phi.1))| /
        ((n + 1 : ℕ) : ℝ) ≤
        |rho| ^ (n + 1) * 1 / 1 := by
      gcongr
    _ = |rho| ^ (n + 1) := by ring

private lemma summable_circleAbelKernelTerm_restrict_norm
    {rho theta left right : ℝ} (hrho : |rho| < 1) :
    Summable (fun n : ℕ ↦
      ‖(circleAbelKernelTerm rho theta n).restrict
        (⟨uIcc left right, isCompact_uIcc⟩ :
          TopologicalSpace.Compacts ℝ)‖) := by
  apply Summable.of_norm_bounded (summable_abs_pow_succ hrho)
  intro n
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact circleAbelKernelTerm_norm_restrict_le n

theorem integral_circleAbelLogKernel_sub_eq_tsum
    {rho : ℝ} (hrho : |rho| < 1) (theta left right : ℝ) :
    (∫ phi : ℝ in left..right,
      circleAbelLogKernel rho (theta - phi)) =
      ∑' n : ℕ, ∫ phi : ℝ in left..right,
        circleAbelKernelTerm rho theta n phi := by
  calc
    (∫ phi : ℝ in left..right,
        circleAbelLogKernel rho (theta - phi)) =
        ∫ phi : ℝ in left..right,
          ∑' n : ℕ, circleAbelKernelTerm rho theta n phi := by
      apply intervalIntegral.integral_congr
      intro phi _hphi
      exact circleAbelLogKernel_eq_tsum hrho (theta - phi)
    _ = ∑' n : ℕ, ∫ phi : ℝ in left..right,
          circleAbelKernelTerm rho theta n phi := by
      have hswap :=
        intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm
          (a := left) (b := right)
          (f := fun n : ℕ ↦ circleAbelKernelTerm rho theta n)
          (summable_circleAbelKernelTerm_restrict_norm
            (theta := theta) (left := left) (right := right) hrho)
      exact hswap.symm

theorem integral_circleAbelKernelTerm_centered
    (rho theta R : ℝ) (n : ℕ) :
    (∫ phi : ℝ in -R..R, circleAbelKernelTerm rho theta n phi) =
      -(rho ^ (n + 1) / ((n + 1 : ℕ) : ℝ)) *
        (Real.cos (((n + 1 : ℕ) : ℝ) * theta) *
          (2 * Real.sin (((n + 1 : ℕ) : ℝ) * R) /
            ((n + 1 : ℕ) : ℝ))) := by
  have hm : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  change (∫ phi : ℝ in -R..R,
    -(rho ^ (n + 1) *
      Real.cos (((n + 1 : ℕ) : ℝ) * (theta - phi)) /
        ((n + 1 : ℕ) : ℝ))) = _
  rw [show (fun phi : ℝ ↦
      -(rho ^ (n + 1) *
        Real.cos (((n + 1 : ℕ) : ℝ) * (theta - phi)) /
          ((n + 1 : ℕ) : ℝ))) =
      fun phi ↦ -(rho ^ (n + 1) / ((n + 1 : ℕ) : ℝ)) *
        Real.cos (((n + 1 : ℕ) : ℝ) * (theta - phi)) by
    funext phi
    ring]
  rw [intervalIntegral.integral_const_mul,
    integral_cos_frequency_sub_centered hm]

private def circleAbelIntegratedKernelTerm
    (rho R : ℝ) (n : ℕ) : C(ℝ, ℝ) where
  toFun theta :=
    -(rho ^ (n + 1) / ((n + 1 : ℕ) : ℝ)) *
      (Real.cos (((n + 1 : ℕ) : ℝ) * theta) *
        (2 * Real.sin (((n + 1 : ℕ) : ℝ) * R) /
          ((n + 1 : ℕ) : ℝ)))
  continuous_toFun := by fun_prop

private lemma circleAbelIntegratedKernelTerm_norm_restrict_le
    {rho R left right : ℝ} (n : ℕ) :
    ‖(circleAbelIntegratedKernelTerm rho R n).restrict
        (⟨uIcc left right, isCompact_uIcc⟩ :
          TopologicalSpace.Compacts ℝ)‖ ≤
      2 * |rho| ^ (n + 1) := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (by norm_num)
    (pow_nonneg (abs_nonneg rho) _))).2
  intro theta
  change
    |-(rho ^ (n + 1) / ((n + 1 : ℕ) : ℝ)) *
      (Real.cos (((n + 1 : ℕ) : ℝ) * theta.1) *
        (2 * Real.sin (((n + 1 : ℕ) : ℝ) * R) /
          ((n + 1 : ℕ) : ℝ)))| ≤ 2 * |rho| ^ (n + 1)
  have hfreq : 1 ≤ ((n + 1 : ℕ) : ℝ) := by norm_num
  have hfreq0 : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hcos : |Real.cos (((n + 1 : ℕ) : ℝ) * theta.1)| ≤ 1 :=
    Real.abs_cos_le_one _
  have hsin : |Real.sin (((n + 1 : ℕ) : ℝ) * R)| ≤ 1 :=
    Real.abs_sin_le_one _
  rw [abs_mul, abs_neg, abs_div, abs_pow, abs_mul, abs_div,
    abs_mul, abs_of_pos hfreq0, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    |rho| ^ (n + 1) / ((n + 1 : ℕ) : ℝ) *
        (|Real.cos (((n + 1 : ℕ) : ℝ) * theta.1)| *
          (2 * |Real.sin (((n + 1 : ℕ) : ℝ) * R)| /
            ((n + 1 : ℕ) : ℝ))) ≤
      |rho| ^ (n + 1) / 1 * (1 * (2 * 1 / 1)) := by
        gcongr
    _ = 2 * |rho| ^ (n + 1) := by ring

private lemma summable_circleAbelIntegratedKernelTerm_restrict_norm
    {rho R left right : ℝ} (hrho : |rho| < 1) :
    Summable (fun n : ℕ ↦
      ‖(circleAbelIntegratedKernelTerm rho R n).restrict
        (⟨uIcc left right, isCompact_uIcc⟩ :
          TopologicalSpace.Compacts ℝ)‖) := by
  have hmajor : Summable (fun n : ℕ ↦ 2 * |rho| ^ (n + 1)) :=
    (summable_abs_pow_succ hrho).mul_left 2
  apply Summable.of_norm_bounded hmajor
  intro n
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact circleAbelIntegratedKernelTerm_norm_restrict_le n

theorem integral_circleAbelLogKernel_sub_centered_eq_integrated_tsum
    {rho : ℝ} (hrho : |rho| < 1) (theta R : ℝ) :
    (∫ phi : ℝ in -R..R,
      circleAbelLogKernel rho (theta - phi)) =
      ∑' n : ℕ, circleAbelIntegratedKernelTerm rho R n theta := by
  rw [integral_circleAbelLogKernel_sub_eq_tsum hrho theta (-R) R]
  apply tsum_congr
  intro n
  exact integral_circleAbelKernelTerm_centered rho theta R n

theorem iteratedIntegral_circleAbelLogKernel_eq_tsum
    {rho : ℝ} (hrho : |rho| < 1) (Q R : ℝ) :
    (∫ theta : ℝ in -Q..Q,
      ∫ phi : ℝ in -R..R,
        circleAbelLogKernel rho (theta - phi)) =
      ∑' n : ℕ, ∫ theta : ℝ in -Q..Q,
        circleAbelIntegratedKernelTerm rho R n theta := by
  calc
    (∫ theta : ℝ in -Q..Q,
        ∫ phi : ℝ in -R..R,
          circleAbelLogKernel rho (theta - phi)) =
        ∫ theta : ℝ in -Q..Q,
          ∑' n : ℕ, circleAbelIntegratedKernelTerm rho R n theta := by
      apply intervalIntegral.integral_congr
      intro theta _htheta
      exact integral_circleAbelLogKernel_sub_centered_eq_integrated_tsum
        hrho theta R
    _ = ∑' n : ℕ, ∫ theta : ℝ in -Q..Q,
          circleAbelIntegratedKernelTerm rho R n theta := by
      have hswap :=
        intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm
          (a := -Q) (b := Q)
          (f := fun n : ℕ ↦ circleAbelIntegratedKernelTerm rho R n)
          (summable_circleAbelIntegratedKernelTerm_restrict_norm
            (R := R) (left := -Q) (right := Q) hrho)
      exact hswap.symm

theorem integral_circleAbelIntegratedKernelTerm_centered
    (rho Q R : ℝ) (n : ℕ) :
    (∫ theta : ℝ in -Q..Q,
      circleAbelIntegratedKernelTerm rho R n theta) =
      -(rho ^ (n + 1) / ((n + 1 : ℕ) : ℝ)) *
        ((2 * Real.sin (((n + 1 : ℕ) : ℝ) * Q) /
            ((n + 1 : ℕ) : ℝ)) *
          (2 * Real.sin (((n + 1 : ℕ) : ℝ) * R) /
            ((n + 1 : ℕ) : ℝ))) := by
  have hm : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  change (∫ theta : ℝ in -Q..Q,
    -(rho ^ (n + 1) / ((n + 1 : ℕ) : ℝ)) *
      (Real.cos (((n + 1 : ℕ) : ℝ) * theta) *
        (2 * Real.sin (((n + 1 : ℕ) : ℝ) * R) /
          ((n + 1 : ℕ) : ℝ)))) = _
  rw [show (fun theta : ℝ ↦
      -(rho ^ (n + 1) / ((n + 1 : ℕ) : ℝ)) *
        (Real.cos (((n + 1 : ℕ) : ℝ) * theta) *
          (2 * Real.sin (((n + 1 : ℕ) : ℝ) * R) /
            ((n + 1 : ℕ) : ℝ)))) =
      fun theta ↦
        (-(rho ^ (n + 1) / ((n + 1 : ℕ) : ℝ)) *
          (2 * Real.sin (((n + 1 : ℕ) : ℝ) * R) /
            ((n + 1 : ℕ) : ℝ))) *
          Real.cos (((n + 1 : ℕ) : ℝ) * theta) by
    funext theta
    ring]
  rw [intervalIntegral.integral_const_mul,
    integral_cos_mul_centered hm]
  ring

theorem integral_circleAbelIntegratedKernelTerm_eq_arcTerm
    (rho : ℝ) {Q R : ℝ} (hQ : Q ≠ 0) (hR : R ≠ 0) (n : ℕ) :
    (∫ theta : ℝ in -Q..Q,
      circleAbelIntegratedKernelTerm rho R n theta) =
      4 * Q * R * (-(rho ^ (n + 1) * circleSincTerm Q R n)) := by
  have hm : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [integral_circleAbelIntegratedKernelTerm_centered]
  unfold circleSincTerm
  rw [Real.sinc_of_ne_zero (mul_ne_zero hm hQ),
    Real.sinc_of_ne_zero (mul_ne_zero hm hR)]
  field_simp [hm, hQ, hR]
  ring

/-- Exact integrated Abel identity on two centered arcs. -/
theorem iteratedIntegral_circleAbelLogKernel_eq_arcEnergy
    {rho : ℝ} (hrho : |rho| < 1) {Q R : ℝ}
    (hQ : Q ≠ 0) (hR : R ≠ 0) :
    (∫ theta : ℝ in -Q..Q,
      ∫ phi : ℝ in -R..R,
        circleAbelLogKernel rho (theta - phi)) =
      4 * Q * R * circleAbelArcEnergy rho Q R := by
  rw [iteratedIntegral_circleAbelLogKernel_eq_tsum hrho Q R]
  simp_rw [integral_circleAbelIntegratedKernelTerm_eq_arcTerm
    rho hQ hR]
  rw [tsum_mul_left, tsum_neg]
  rfl

end

end Erdos1038
