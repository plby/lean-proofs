import ErdosProblems.Erdos421.AdditivePrimeCofactors
import ErdosProblems.Erdos421.LogarithmicPrimeCofactors
import ErdosProblems.Erdos421.AdditiveWindowScale

/-! # Uniform kernel comparisons for the bounded large-prime cofactor weights -/

namespace Erdos421

theorem additivePrimeCofactorWindow_complex (P : Finset ℕ) (B z : ℕ) (Y x : ℝ) :
    (∑ n ∈ Finset.Icc 1 B, (primeCofactorWeight P z n : ℂ) * additiveIntegerWeight Y x n).re =
      additivePrimeCofactorWindow P B z Y x := by
  rw [Complex.re_sum]
  unfold additivePrimeCofactorWindow
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

theorem logarithmicPrimeCofactorWindow_complex (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p)
    (B z : ℕ) (δ y : ℝ) :
    (∑ n ∈ Finset.Icc 1 B, (primeCofactorWeight P z n : ℂ) * logarithmicIntegerWeight δ y n).re =
      logarithmicPrimeCofactorWindow P B z δ y := by
  rw [Complex.re_sum, logarithmicPrimeCofactorWindow_merge P hP]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem primeCofactorWeight_norm_bound (P : Finset ℕ) {B w k : ℕ} (hw : 0 < w)
    (hB : B < w ^ k) (hP : ∀ p ∈ P, p.Prime ∧ w ≤ p) (z : ℕ) :
    ∀ n ∈ Finset.Icc 1 B, ‖(primeCofactorWeight P z n : ℂ)‖ ≤ (k : ℝ) := by
  intro n hn
  obtain ⟨hnpos, hnB⟩ := Finset.mem_Icc.mp hn
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (primeCofactorWeight_nonneg P z n)]
  exact primeCofactorWeight_le P hw hnpos (hnB.trans_lt hB) hP z

theorem exists_logarithmicCofactorWindow_additive_comparison :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : Finset ℕ) (B z w k : ℕ), 0 < w → B < w ^ k →
      (∀ p ∈ P, p.Prime ∧ w ≤ p) → ∀ δ x : ℝ, 0 < δ → δ ≤ 1 / 2 → 0 < x →
      |logarithmicPrimeCofactorWindow P B z δ (Real.log x) -
        additivePrimeCofactorWindow P B z (δ * x) x| ≤ K * k * (δ + x⁻¹) := by
  obtain ⟨K, hK, hb⟩ := exists_finite_integer_kernel_comparison
  refine ⟨K, hK, ?_⟩
  intro P B z w k hw hB hP δ x hδ hδ1 hx
  have hcoef := primeCofactorWeight_norm_bound P hw hB hP z
  have h := hb (Finset.Icc 1 B) (fun n ↦ (primeCofactorWeight P z n : ℂ))
    (fun n hn ↦ (Finset.mem_Icc.mp hn).1) k (Nat.cast_nonneg k) hcoef δ x hδ hδ1 hx
  have hre := Complex.abs_re_le_norm
    ((∑ n ∈ Finset.Icc 1 B, (primeCofactorWeight P z n : ℂ) *
      logarithmicIntegerWeight δ (Real.log x) n) -
        ∑ n ∈ Finset.Icc 1 B, (primeCofactorWeight P z n : ℂ) * additiveIntegerWeight (δ * x) x n)
  rw [Complex.sub_re, logarithmicPrimeCofactorWindow_complex P (fun p hp ↦ (hP p hp).1.pos),
    additivePrimeCofactorWindow_complex] at hre
  exact hre.trans h

theorem exists_additiveCofactorWindow_scale_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : Finset ℕ) (B z w k : ℕ), 0 < w → B < w ^ k →
      (∀ p ∈ P, p.Prime ∧ w ≤ p) → ∀ Y Z η x : ℝ,
      0 < Y → Y ≤ Z → Z ≤ (1 + η) * Y → 0 ≤ η → 1 ≤ Z → 0 ≤ x →
      |additivePrimeCofactorWindow P B z Y x - additivePrimeCofactorWindow P B z Z x| ≤
        K * k * η := by
  obtain ⟨C, hC, hnorm, hlip⟩ := exists_schwartz_uniform_lipschitz oneSidedSchwartzWindow
  refine ⟨4 * C, by positivity, ?_⟩
  intro P B z w k hw hB hP Y Z η x hY hYZ hZη hη hZ1 hx
  have hcoef := primeCofactorWeight_norm_bound P hw hB hP z
  have hb := finite_additive_window_scale (Finset.Icc 1 B)
    (fun n ↦ (primeCofactorWeight P z n : ℂ))
    (Nat.cast_nonneg k) hC.le hcoef hnorm hlip hY hYZ hZη hη hZ1 hx
  have hre := Complex.abs_re_le_norm
    ((∑ n ∈ Finset.Icc 1 B, (primeCofactorWeight P z n : ℂ) * additiveIntegerWeight Y x n) -
      ∑ n ∈ Finset.Icc 1 B, (primeCofactorWeight P z n : ℂ) * additiveIntegerWeight Z x n)
  rw [Complex.sub_re, additivePrimeCofactorWindow_complex,
    additivePrimeCofactorWindow_complex] at hre
  exact hre.trans hb

end Erdos421
