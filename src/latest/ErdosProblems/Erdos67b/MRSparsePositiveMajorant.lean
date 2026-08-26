import ErdosProblems.Erdos67b.MRSparseDuality

/-! # Sparse duality with nonnegative majorants, allowing zero weights -/

open scoped BigOperators

namespace Erdos67b

noncomputable section

theorem mrFinite_energy_le_of_majorant_gram_rows
    {ι κ : Type*} (A B : Finset ι) (S : Finset κ) (x : κ → ι → ℂ) (w : ι → ℝ)
    (hAB : A ⊆ B) (hw : ∀ n ∈ B, 0 ≤ w n) (hmajor : ∀ n ∈ A, 1 ≤ w n)
    {D : ℝ} (hD : 0 ≤ D)
    (hrow : ∀ s ∈ S,
      (∑ t ∈ S, ‖mrFiniteGramKernel B (fun u n ↦ (Real.sqrt (w n) : ℂ) * x u n) s t‖) ≤ D)
    (a : ι → ℂ) :
    (∑ s ∈ S, ‖∑ n ∈ A, a n * x s n‖ ^ 2) ≤ D * ∑ n ∈ A, ‖a n‖ ^ 2 := by
  apply mrFinite_duality A S x hD
  intro b
  have hweighted := mrFinite_dual_energy_le_of_gram_rows B S
    (fun u n ↦ (Real.sqrt (w n) : ℂ) * x u n) hrow b
  have hsum (n : ι) :
      (∑ s ∈ S, b s * ((Real.sqrt (w n) : ℂ) * x s n)) =
        (Real.sqrt (w n) : ℂ) * ∑ s ∈ S, b s * x s n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    ring
  calc
    _ ≤ ∑ n ∈ A, w n * ‖∑ s ∈ S, b s * x s n‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hmajor n hn)
        (sq_nonneg ‖∑ s ∈ S, b s * x s n‖)
    _ ≤ ∑ n ∈ B, w n * ‖∑ s ∈ S, b s * x s n‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hAB (fun n hn _ ↦ mul_nonneg (hw n hn) (sq_nonneg _))
    _ = ∑ n ∈ B, ‖∑ s ∈ S, b s * ((Real.sqrt (w n) : ℂ) * x s n)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [hsum, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hw n hn)]
    _ ≤ _ := hweighted

theorem mrSparse_logarithmic_energy_le_of_majorant_rows
    (A B : Finset ℕ) (S : Finset ℝ) (w : ℕ → ℝ)
    (hAB : A ⊆ B) (hw : ∀ n ∈ B, 0 ≤ w n) (hmajor : ∀ n ∈ A, 1 ≤ w n)
    {D : ℝ} (hD : 0 ≤ D)
    (hrow : ∀ s ∈ S,
      (∑ t ∈ S, ‖logarithmicDirichletPolynomial B (fun n ↦ (w n : ℂ)) (t - s)‖) ≤ D)
    (a : ℕ → ℂ) :
    (∑ t ∈ S, ‖logarithmicDirichletPolynomial A a t‖ ^ 2) ≤
      D * ∑ n ∈ A, ‖a n‖ ^ 2 := by
  apply mrFinite_energy_le_of_majorant_gram_rows A B S (fun t n ↦ logarithmicPhase n t)
    w hAB hw hmajor hD
  intro s hs
  simpa only [mrWeighted_logarithmic_gram_eq B w hw] using hrow s hs

end

end Erdos67b
