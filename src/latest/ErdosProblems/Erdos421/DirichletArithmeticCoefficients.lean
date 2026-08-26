import ErdosProblems.Erdos421.WeightedDirichletMeanSquare
import ErdosProblems.Erdos421.FiniteCoefficients

/-! # Finite arithmetic coefficients for vertical Dirichlet polynomials -/

namespace Erdos421

noncomputable def dirichletArithmeticCoefficients (S : Finset ℕ) (a : ℕ → ℂ) (σ : ℝ) :
    ArithmeticFunction ℂ :=
  ⟨fun n ↦ if n ∈ S ∧ n ≠ 0 then a n * ((n : ℝ) ^ (-σ) : ℝ) else 0, by simp⟩

theorem dirichletArithmeticCoefficients_supported (S : Finset ℕ) (a : ℕ → ℂ) (σ : ℝ)
    {U : ℕ} (hS : ∀ n ∈ S, n ≤ U) : SupportedThrough (dirichletArithmeticCoefficients S a σ) U := by
  intro n hn
  have hnot : n ∉ S := fun h ↦ (hS n h).not_gt hn
  simp only [dirichletArithmeticCoefficients, ArithmeticFunction.coe_mk, hnot,
    false_and, if_false]

theorem dirichletArithmeticCoefficients_norm_le (S : Finset ℕ) (a : ℕ → ℂ)
    {M : ℕ} (hM : 1 ≤ M) (hS : ∀ n ∈ S, M ≤ n) (ha : ∀ n ∈ S, ‖a n‖ ≤ 1)
    {σ : ℝ} (hσ : 1 ≤ σ) (n : ℕ) :
    ‖dirichletArithmeticCoefficients S a σ n‖ ≤ (M : ℝ)⁻¹ := by
  simp only [dirichletArithmeticCoefficients, ArithmeticFunction.coe_mk]
  split_ifs with h
  · exact dirichletCoefficient_norm_le hM (hS n h.1) (ha n h.1) hσ
  · simp only [norm_zero]
    positivity

theorem dirichletPolynomial_eq_arithmetic_exponential (S : Finset ℕ) (a : ℕ → ℂ)
    {U : ℕ} (hS : ∀ n ∈ S, 0 < n ∧ n ≤ U) (σ t : ℝ) :
    dirichletPolynomial S a (σ + (t : ℂ) * Complex.I) =
      exponentialSum (Finset.Icc 1 U) (dirichletArithmeticCoefficients S a σ)
        (fun n ↦ Real.log n) (-t) := by
  classical
  rw [dirichletPolynomial_eq_exponentialSum S a (fun n hn ↦ (hS n hn).1) σ t]
  have hsub : S ⊆ Finset.Icc 1 U := fun n hn ↦ Finset.mem_Icc.mpr (hS n hn)
  have he : exponentialSum S (fun n ↦ a n * ((n : ℝ) ^ (-σ) : ℝ))
      (fun n ↦ Real.log n) (-t) =
      exponentialSum S (dirichletArithmeticCoefficients S a σ) (fun n ↦ Real.log n) (-t) := by
    apply Finset.sum_congr rfl
    intro n hn
    simp only [dirichletArithmeticCoefficients, ArithmeticFunction.coe_mk,
      if_pos (show n ∈ S ∧ n ≠ 0 from ⟨hn, (hS n hn).1.ne'⟩)]
  rw [he]
  apply Finset.sum_subset hsub
  intro n _ hn
  simp only [dirichletArithmeticCoefficients, ArithmeticFunction.coe_mk, hn,
    false_and, if_false, zero_mul]

end Erdos421
