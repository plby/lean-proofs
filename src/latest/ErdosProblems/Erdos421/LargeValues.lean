import ErdosProblems.Erdos421.Sampling

/-! # The elementary separated large-value bound for Dirichlet polynomials -/

namespace Erdos421

open Complex MeasureTheory

theorem oscillatoryPhase_hasDerivAt (ω t : ℝ) :
    HasDerivAt (oscillatoryPhase ω)
      ((Complex.I * (ω : ℂ)) * oscillatoryPhase ω t) t := by
  unfold oscillatoryPhase
  have h := ((Complex.hasDerivAt_exp (Complex.I * (ω : ℂ) * (t : ℂ))).comp (t : ℂ)
    ((hasDerivAt_id (t : ℂ)).const_mul (Complex.I * (ω : ℂ)))).comp_ofReal
  simpa only [Function.comp_apply, mul_one, mul_comm] using! h

theorem exponentialSum_hasDerivAt (S : Finset ℕ) (c : ℕ → ℂ) (ω : ℕ → ℝ) (t : ℝ) :
    HasDerivAt (exponentialSum S c ω)
      (exponentialSum S (fun n ↦ c n * (Complex.I * (ω n : ℂ))) ω t) t := by
  have h := HasDerivAt.fun_sum (u := S)
    (fun n _ ↦ (oscillatoryPhase_hasDerivAt (ω n) t).const_mul (c n))
  simpa only [exponentialSum, mul_assoc] using! h

theorem derivative_coefficients_sq_sum_le (S : Finset ℕ) (c : ℕ → ℂ) {N : ℕ}
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) :
    (∑ n ∈ S, ‖c n * (Complex.I * (Real.log n : ℂ))‖ ^ 2) ≤
      (Real.log N) ^ 2 * (∑ n ∈ S, ‖c n‖ ^ 2) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hlog : Real.log (n : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by exact_mod_cast (hS n hn).1) (by exact_mod_cast (hS n hn).2)
  have hsq : (Real.log (n : ℝ)) ^ 2 ≤ (Real.log (N : ℝ)) ^ 2 := by
    nlinarith [Real.log_natCast_nonneg n, Real.log_natCast_nonneg N]
  simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul,
    mul_pow, sq_abs]
  exact (mul_le_mul_of_nonneg_left hsq (sq_nonneg _)).trans_eq (mul_comm _ _)

theorem dirichlet_separated_square_sum_le (S J : Finset ℕ) (c : ℕ → ℂ) (t : ℕ → ℝ)
    {N : ℕ} (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) {A B : ℝ}
    (hAB : A ≤ B) (ht : ∀ j ∈ J, A ≤ t j ∧ t j ≤ B)
    (hsep : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → 1 ≤ |t i - t j|) :
    (∑ j ∈ J, ‖exponentialSum S c (fun n ↦ Real.log n) (t j)‖ ^ 2) ≤
      (2 + (Real.log N) ^ 2) * (B + 1 - A + 4 * N * (1 + Real.log N)) *
        (∑ n ∈ S, ‖c n‖ ^ 2) := by
  let c' : ℕ → ℂ := fun n ↦ c n * (Complex.I * (Real.log n : ℂ))
  let D := exponentialSum S c (fun n ↦ Real.log n)
  let D' := exponentialSum S c' (fun n ↦ Real.log n)
  have hd : ∀ x, HasDerivAt D (D' x) x := fun x ↦ exponentialSum_hasDerivAt S c _ x
  have hsample := separated_norm_square_sum_le J t hAB ht hsep hd
    (exponentialSum_continuous S c' _)
  have hmean := dirichlet_mean_square_bound S c hS A (B + 1)
  have hmean' := dirichlet_mean_square_bound S c' hS A (B + 1)
  let K := B + 1 - A + 4 * (N : ℝ) * (1 + Real.log N)
  have hK : 0 ≤ K := by
    have hlog := Real.log_natCast_nonneg N
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    dsimp only [K]
    nlinarith
  have hc' : (∑ n ∈ S, ‖c' n‖ ^ 2) ≤ (Real.log N) ^ 2 * (∑ n ∈ S, ‖c n‖ ^ 2) :=
    derivative_coefficients_sq_sum_le S c hS
  have hmul := mul_le_mul_of_nonneg_left hc' hK
  change (∑ j ∈ J, ‖D (t j)‖ ^ 2) ≤ _
  change (∫ x in A..B + 1, ‖D x‖ ^ 2) ≤ K * (∑ n ∈ S, ‖c n‖ ^ 2) at hmean
  change (∫ x in A..B + 1, ‖D' x‖ ^ 2) ≤ K * (∑ n ∈ S, ‖c' n‖ ^ 2) at hmean'
  change _ ≤ (2 + (Real.log N) ^ 2) * K * (∑ n ∈ S, ‖c n‖ ^ 2)
  nlinarith

/-- A fully explicit elementary large-value estimate, allowing arbitrary
complex coefficients and arbitrary one-separated real sampling points. -/
theorem dirichlet_large_values_card_bound (S J : Finset ℕ) (c : ℕ → ℂ) (t : ℕ → ℝ)
    {N : ℕ} (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) {A B V : ℝ}
    (hAB : A ≤ B) (ht : ∀ j ∈ J, A ≤ t j ∧ t j ≤ B)
    (hsep : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → 1 ≤ |t i - t j|)
    (hV : 0 ≤ V)
    (hlarge : ∀ j ∈ J, V ≤ ‖exponentialSum S c (fun n ↦ Real.log n) (t j)‖) :
    J.card * V ^ 2 ≤
      (2 + (Real.log N) ^ 2) * (B + 1 - A + 4 * N * (1 + Real.log N)) *
        (∑ n ∈ S, ‖c n‖ ^ 2) := by
  calc
    J.card * V ^ 2 = ∑ _j ∈ J, V ^ 2 := by simp
    _ ≤ ∑ j ∈ J, ‖exponentialSum S c (fun n ↦ Real.log n) (t j)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      have h := hlarge j hj
      nlinarith [norm_nonneg (exponentialSum S c (fun n ↦ Real.log n) (t j))]
    _ ≤ _ := dirichlet_separated_square_sum_le S J c t hS hAB ht hsep

end Erdos421
