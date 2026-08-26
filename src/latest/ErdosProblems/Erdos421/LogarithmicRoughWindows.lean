import ErdosProblems.Erdos421.FiniteKernelComparison
import ErdosProblems.Erdos421.SmoothSieveWindows

/-! # The actual rough-number count in logarithmic coordinates -/

namespace Erdos421

noncomputable def logarithmicRoughWindow (B z : ℕ) (δ y : ℝ) : ℝ :=
  (∑ n ∈ Finset.Icc 1 B, (roughIndicator n z : ℂ) * logarithmicIntegerWeight δ y n).re

theorem logarithmicIntegerWeight_dirichlet (S : Finset ℕ) (a : ℕ → ℂ)
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    schwartzDirichletWindow S a 1 (normalizedSchwartzScale δ hδ oneSidedSchwartzWindow) y =
      ∑ n ∈ S, a n * logarithmicIntegerWeight δ y n := by
  simp only [schwartzDirichletWindow_apply, normalizedSchwartzScale_apply,
    logarithmicIntegerWeight, Real.rpow_neg_one, Complex.real_smul, mul_assoc]

theorem logarithmicRoughWindow_dirichlet (B z : ℕ) {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    logarithmicRoughWindow B z δ y =
      (schwartzDirichletWindow (Finset.Icc 1 B) (fun n ↦ (roughIndicator n z : ℂ)) 1
        (normalizedSchwartzScale δ hδ oneSidedSchwartzWindow) y).re := by
  rw [logarithmicIntegerWeight_dirichlet]
  rfl

theorem additiveRoughWindow_complex (B z : ℕ) (Y x : ℝ) :
    (∑ n ∈ Finset.Icc 1 B, (roughIndicator n z : ℂ) * additiveIntegerWeight Y x n).re =
      additiveRoughWindow B z Y x := by
  rw [Complex.re_sum]
  unfold additiveRoughWindow
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

theorem exists_logarithmicRoughWindow_additive_comparison :
    ∃ K : ℝ, 0 < K ∧ ∀ B z : ℕ, ∀ δ x : ℝ, 0 < δ → δ ≤ 1 / 2 → 0 < x →
      |logarithmicRoughWindow B z δ (Real.log x) - additiveRoughWindow B z (δ * x) x| ≤
        K * (δ + x⁻¹) := by
  obtain ⟨K, hK, hb⟩ := exists_finite_integer_kernel_comparison
  refine ⟨K, hK, ?_⟩
  intro B z δ x hδ hδ1 hx
  have hcoef : ∀ n ∈ Finset.Icc 1 B, ‖(roughIndicator n z : ℂ)‖ ≤ 1 := by
    intro n hn
    rw [Complex.norm_real, Real.norm_eq_abs, roughIndicator]
    split_ifs <;> norm_num
  have h := hb (Finset.Icc 1 B) (fun n ↦ (roughIndicator n z : ℂ))
    (fun n hn ↦ (Finset.mem_Icc.mp hn).1) 1 (by norm_num) hcoef δ x hδ hδ1 hx
  simp only [mul_one] at h
  have hre := Complex.abs_re_le_norm
    ((∑ n ∈ Finset.Icc 1 B, (roughIndicator n z : ℂ) * logarithmicIntegerWeight δ (Real.log x) n) -
      ∑ n ∈ Finset.Icc 1 B, (roughIndicator n z : ℂ) * additiveIntegerWeight (δ * x) x n)
  rw [Complex.sub_re, additiveRoughWindow_complex] at hre
  exact hre.trans h

end Erdos421
