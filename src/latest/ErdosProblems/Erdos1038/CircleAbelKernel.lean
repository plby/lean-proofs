import ErdosProblems.Erdos1038.CircleCosineIntegral
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Abel regularization of the logarithmic circle kernel

For `0 ≤ rho < 1`, the boundary logarithmic kernel is regularized by

`log ‖1 - rho * exp(i u)‖`.

Its cosine series converges absolutely.  This is the first analytic step
in identifying the centered two-arc integral with `circleArcEnergy`.
-/

set_option warningAsError false

namespace Erdos1038

noncomputable section

/-- Abel regularization of `log |exp(iu) - 1|`. -/
def circleAbelLogKernel (rho u : ℝ) : ℝ :=
  Real.log ‖(1 : ℂ) - (rho : ℂ) * Complex.exp (u * Complex.I)‖

lemma norm_rho_mul_exp_mul_I (rho u : ℝ) :
    ‖(rho : ℂ) * Complex.exp (u * Complex.I)‖ = |rho| := by
  rw [norm_mul, Complex.norm_exp]
  simp

/-- The absolutely convergent cosine series of the regularized kernel. -/
theorem hasSum_circleAbelLogKernel
    {rho : ℝ} (hrho : |rho| < 1) (u : ℝ) :
    HasSum
        (fun n : ℕ ↦
          -(rho ^ (n + 1) * Real.cos (((n + 1 : ℕ) : ℝ) * u) /
            ((n + 1 : ℕ) : ℝ)))
        (circleAbelLogKernel rho u) := by
  let z : ℂ := (rho : ℂ) * Complex.exp (u * Complex.I)
  have hz : ‖z‖ < 1 := by
    simpa only [z, norm_rho_mul_exp_mul_I] using! hrho
  have hcomplex : HasSum (fun n : ℕ ↦ z ^ n / n) (-Complex.log (1 - z)) :=
    Complex.hasSum_taylorSeries_neg_log hz
  have hreal : HasSum (fun n : ℕ ↦ -((z ^ n / n).re))
      (Real.log ‖1 - z‖) := by
    have hmapped := Complex.reCLM.hasSum hcomplex
    have hneg := hmapped.neg
    simpa only [Complex.reCLM_apply, map_neg, Complex.log_re, neg_neg] using! hneg
  have hshift : HasSum (fun n : ℕ ↦ -((z ^ (n + 1) / (n + 1)).re))
      (Real.log ‖1 - z‖) := by
    simpa using! (hasSum_nat_add_iff' 1).mpr hreal
  convert! hshift using 1 with n
  · funext n
    dsimp only [z]
    rw [mul_pow, ← Complex.exp_nat_mul]
    rw [show ((n + 1 : ℕ) : ℂ) * ((u : ℂ) * Complex.I) =
        ((((n + 1 : ℕ) : ℝ) * u : ℝ) : ℂ) * Complex.I by
      push_cast
      ring]
    rw [show ((rho : ℂ) ^ (n + 1)) =
        ((rho ^ (n + 1) : ℝ) : ℂ) by norm_cast]
    rw [show ((n : ℂ) + 1) = ((((n + 1 : ℕ) : ℝ) : ℂ)) by
      push_cast
      ring]
    rw [Complex.div_ofReal_re]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, zero_mul, sub_zero]

lemma summable_circleAbelLogKernel_series
    {rho : ℝ} (hrho : |rho| < 1) (u : ℝ) :
    Summable
      (fun n : ℕ ↦
        -(rho ^ (n + 1) * Real.cos (((n + 1 : ℕ) : ℝ) * u) /
          ((n + 1 : ℕ) : ℝ))) :=
  (hasSum_circleAbelLogKernel hrho u).summable

theorem circleAbelLogKernel_eq_tsum
    {rho : ℝ} (hrho : |rho| < 1) (u : ℝ) :
    circleAbelLogKernel rho u =
      ∑' n : ℕ,
        -(rho ^ (n + 1) * Real.cos (((n + 1 : ℕ) : ℝ) * u) /
          ((n + 1 : ℕ) : ℝ)) :=
  (hasSum_circleAbelLogKernel hrho u).tsum_eq.symm

/-! ## Abel-weighted centered-arc series -/

/-- Centered-arc energy with every positive Fourier mode multiplied by
`rho^n`.  At `rho = 1` this is `circleArcEnergy`. -/
def circleAbelArcEnergy (rho Q R : ℝ) : ℝ :=
  -∑' n : ℕ, rho ^ (n + 1) * circleSincTerm Q R n

/-- Abel-weighted square-completion gap. -/
def circleAbelSincSquareGap (rho Q R : ℝ) : ℝ :=
  ∑' n : ℕ, rho ^ (n + 1) * circleSincSquareGapTerm Q R n

lemma summable_rpow_mul_circleSincTerm
    {rho Q R : ℝ} (hrho : |rho| ≤ 1) (hQ : 0 < Q) (hR : 0 < R) :
    Summable (fun n : ℕ ↦ rho ^ (n + 1) * circleSincTerm Q R n) := by
  have hbase := (summable_circleSincTerm hQ hR).norm
  apply Summable.of_norm_bounded hbase
  intro n
  rw [norm_mul, Real.norm_eq_abs, abs_pow]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (pow_le_one₀ (abs_nonneg rho) hrho)

lemma summable_rpow_mul_circleSincSquareGapTerm
    {rho Q R : ℝ} (hrho : |rho| ≤ 1) (hQ : 0 < Q) (hR : 0 < R) :
    Summable
      (fun n : ℕ ↦ rho ^ (n + 1) * circleSincSquareGapTerm Q R n) := by
  have hbase := (summable_circleSincSquareGapTerm hQ hR).norm
  apply Summable.of_norm_bounded hbase
  intro n
  rw [norm_mul, Real.norm_eq_abs, abs_pow]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (pow_le_one₀ (abs_nonneg rho) hrho)

@[simp] theorem circleAbelArcEnergy_one (Q R : ℝ) :
    circleAbelArcEnergy 1 Q R = circleArcEnergy Q R := by
  simp [circleAbelArcEnergy, circleArcEnergy]

@[simp] theorem circleAbelSincSquareGap_one (Q R : ℝ) :
    circleAbelSincSquareGap 1 Q R = circleSincSquareGap Q R := by
  simp [circleAbelSincSquareGap, circleSincSquareGap]

lemma circleAbelSincSquareGapTerm_eq
    (rho Q R : ℝ) (n : ℕ) :
    rho ^ (n + 1) * circleSincSquareGapTerm Q R n =
      rho ^ (n + 1) * circleSincTerm Q Q n +
        rho ^ (n + 1) * circleSincTerm R R n -
          2 * (rho ^ (n + 1) * circleSincTerm Q R n) := by
  rw [circleSincSquareGapTerm_eq]
  ring

theorem circleAbelArcEnergy_square_completion
    {rho Q R : ℝ} (hrho : |rho| ≤ 1) (hQ : 0 < Q) (hR : 0 < R) :
    2 * circleAbelArcEnergy rho Q R -
        circleAbelArcEnergy rho Q Q - circleAbelArcEnergy rho R R =
      circleAbelSincSquareGap rho Q R := by
  have hQQ := summable_rpow_mul_circleSincTerm hrho hQ hQ
  have hRR := summable_rpow_mul_circleSincTerm hrho hR hR
  have hQR := summable_rpow_mul_circleSincTerm hrho hQ hR
  rw [circleAbelSincSquareGap]
  calc
    2 * circleAbelArcEnergy rho Q R -
          circleAbelArcEnergy rho Q Q - circleAbelArcEnergy rho R R =
        (∑' n, rho ^ (n + 1) * circleSincTerm Q Q n) +
          (∑' n, rho ^ (n + 1) * circleSincTerm R R n) -
            2 * (∑' n, rho ^ (n + 1) * circleSincTerm Q R n) := by
      simp only [circleAbelArcEnergy]
      ring
    _ = ∑' n : ℕ,
        (rho ^ (n + 1) * circleSincTerm Q Q n +
          rho ^ (n + 1) * circleSincTerm R R n -
            2 * (rho ^ (n + 1) * circleSincTerm Q R n)) := by
      rw [(hQQ.add hRR).tsum_sub (hQR.mul_left 2),
        hQQ.tsum_add hRR, tsum_mul_left]
    _ = ∑' n, rho ^ (n + 1) * circleSincSquareGapTerm Q R n := by
      apply tsum_congr
      intro n
      exact (circleAbelSincSquareGapTerm_eq rho Q R n).symm

theorem circleAbelSincSquareGap_nonneg
    {rho Q R : ℝ} (hrho : 0 ≤ rho) :
    0 ≤ circleAbelSincSquareGap rho Q R := by
  unfold circleAbelSincSquareGap circleSincSquareGapTerm
  exact tsum_nonneg fun n ↦ mul_nonneg (pow_nonneg hrho _)
    (div_nonneg (sq_nonneg _) (by positivity))

lemma circleAbelArcEnergy_eq_neg_mul_tsum
    (rho Q R : ℝ) :
    circleAbelArcEnergy rho Q R =
      -(rho * ∑' n : ℕ, circleSincTerm Q R n * rho ^ n) := by
  unfold circleAbelArcEnergy
  rw [show (fun n : ℕ ↦ rho ^ (n + 1) * circleSincTerm Q R n) =
      fun n ↦ rho * (circleSincTerm Q R n * rho ^ n) by
    funext n
    rw [pow_succ]
    ring]
  rw [tsum_mul_left]

/-- Abel convergence of the regularized centered-arc series to the
boundary centered-arc energy. -/
theorem tendsto_circleAbelArcEnergy_one
    {Q R : ℝ} (hQ : 0 < Q) (hR : 0 < R) :
    Filter.Tendsto (fun rho : ℝ ↦ circleAbelArcEnergy rho Q R)
      (nhdsWithin 1 (Set.Iio 1)) (nhds (circleArcEnergy Q R)) := by
  have hseries := summable_circleSincTerm hQ hR
  have hAbel : Filter.Tendsto
      (fun rho : ℝ ↦
        ∑' n : ℕ, circleSincTerm Q R n * rho ^ n)
      (nhdsWithin 1 (Set.Iio 1))
      (nhds (∑' n : ℕ, circleSincTerm Q R n)) :=
    Real.tendsto_tsum_powerSeries_nhdsWithin_lt
      hseries.hasSum.tendsto_sum_nat
  have hrho : Filter.Tendsto (fun rho : ℝ ↦ rho)
      (nhdsWithin 1 (Set.Iio 1)) (nhds 1) :=
    tendsto_nhdsWithin_of_tendsto_nhds Filter.tendsto_id
  have hproduct := (hrho.mul hAbel).neg
  simpa only [circleArcEnergy, one_mul] using! hproduct.congr' (by
    filter_upwards with rho
    rw [circleAbelArcEnergy_eq_neg_mul_tsum])

/-- The Abel square-completion gap converges to the full nonnegative sinc
square gap at the boundary. -/
theorem tendsto_circleAbelSincSquareGap_one
    {Q R : ℝ} (hQ : 0 < Q) (hR : 0 < R) :
    Filter.Tendsto (fun rho : ℝ ↦ circleAbelSincSquareGap rho Q R)
      (nhdsWithin 1 (Set.Iio 1)) (nhds (circleSincSquareGap Q R)) := by
  have hQQ := tendsto_circleAbelArcEnergy_one hQ hQ
  have hRR := tendsto_circleAbelArcEnergy_one hR hR
  have hQR := tendsto_circleAbelArcEnergy_one hQ hR
  have hcombination := ((hQR.const_mul 2).sub hQQ).sub hRR
  rw [← circleArcEnergy_square_completion hQ hR]
  apply hcombination.congr'
  have hnear : Set.Ioi (-1 : ℝ) ∈ nhdsWithin 1 (Set.Iio 1) :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num))
  filter_upwards [self_mem_nhdsWithin, hnear] with rho hrho hrhoLower
  have habs : |rho| ≤ 1 := by
    have hrhoLt : rho < 1 := hrho
    rw [abs_le]
    exact ⟨hrhoLower.le, hrhoLt.le⟩
  rw [circleAbelArcEnergy_square_completion habs hQ hR]

end

end Erdos1038
