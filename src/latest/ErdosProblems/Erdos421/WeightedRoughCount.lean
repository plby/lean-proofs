import ErdosProblems.Erdos421.ArithmeticWeightedError
import ErdosProblems.Erdos421.FrozenRoughCount
import ErdosProblems.Erdos421.SievePrimeProducts

/-! # Uniform weighted rough counts with a frozen local density -/

namespace Erdos421

open MeasureTheory

theorem roughIndicator_interval_sum (a b : ℝ) (z : ℕ) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, roughIndicator n z) =
      ((roughInRealInterval a b z).card : ℝ) := by
  classical
  simp only [roughIndicator, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
    roughInRealInterval, sifted]

theorem roughIndicator_weighted_interval_sum (g : ℝ → ℝ) (a b : ℝ) (z : ℕ) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, g n * roughIndicator n z) =
      ∑ n ∈ roughInRealInterval a b z, g n := by
  classical
  simp only [roughInRealInterval, sifted, Finset.sum_filter, roughIndicator,
    mul_ite, mul_one, mul_zero]

theorem rough_weighted_sum_asymptotic (n : ℕ) {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ B > 1, ∀ x : ℝ, B ≤ x → ∀ Y : ℝ, 0 ≤ Y → Y ≤ x → ∀ z : ℕ,
      2 ≤ z → (z : ℝ) ^ 2 ≤ x → x + Y ≤ (z : ℝ) ^ (n + 3) →
      ∀ g : ℝ → ℝ, (∀ t ∈ Set.Icc x (x + Y), DifferentiableAt ℝ g t) →
      ContinuousOn (deriv g) (Set.Icc x (x + Y)) →
      |(∑ m ∈ roughInRealInterval x (x + Y) z, g m) -
        (finiteBuchstab (n + 1) (Real.log x / Real.log z) / Real.log z) *
          (∫ t in x..x + Y, g t)| ≤
        (ε * x / (Real.log x) ^ A +
          (roughCountErrorConstant (n + 1) + ((n : ℝ) + 3) ^ 2) *
            Y ^ 2 / (x * (Real.log x) ^ 2)) *
          (|g (x + Y)| + ∫ t in x..x + Y, |deriv g t|) := by
  obtain ⟨B, hB, hcount⟩ := rough_count_frozen_asymptotic n hA hε
  refine ⟨B, hB, ?_⟩
  intro x hx Y hY hYx z hz hzsq hpow g hg hg'
  have hx1 := hB.trans_le hx
  have hxp : 0 < x := by linarith
  have hLx := Real.log_pos hx1
  have hxy : x ≤ x + Y := by linarith
  let d : ℝ := finiteBuchstab (n + 1) (Real.log x / Real.log z) / Real.log z
  have hC : 0 ≤ roughCountErrorConstant (n + 1) + ((n : ℝ) + 3) ^ 2 :=
    add_nonneg (roughCountErrorConstant_nonneg _) (sq_nonneg _)
  have herr : ∀ t ∈ Set.Icc x (x + Y),
      |(∑ m ∈ Finset.Ioc ⌊x⌋₊ ⌊t⌋₊, roughIndicator m z) - d * (t - x)| ≤
        ε * x / (Real.log x) ^ A +
          (roughCountErrorConstant (n + 1) + ((n : ℝ) + 3) ^ 2) *
            Y ^ 2 / (x * (Real.log x) ^ 2) := by
    intro t ht
    have hc := hcount x hx t ht.1 (by linarith [ht.2]) z hz hzsq (ht.2.trans hpow)
    calc
      _ = |((roughInRealInterval x t z).card : ℝ) -
          (t - x) * finiteBuchstab (n + 1) (Real.log x / Real.log z) / Real.log z| := by
        rw [roughIndicator_interval_sum]
        congr 1
        dsimp only [d]
        ring
      _ ≤ _ := hc
      _ ≤ _ := by gcongr <;> linarith [ht.1, ht.2]
  have h := arithmetic_weighted_error_le (fun m ↦ roughIndicator m z) d hxp.le hxy hg hg' herr
  rw [roughIndicator_weighted_interval_sum] at h
  exact h

end Erdos421
