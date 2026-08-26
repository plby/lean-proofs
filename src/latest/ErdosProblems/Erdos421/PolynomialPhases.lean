import ErdosProblems.Erdos421.TorusMoments
import ErdosProblems.Erdos421.VariationWeights

/-! # Polynomial phases and perturbations of their coefficients -/

namespace Erdos421

noncomputable def powerPhase {k : ℕ} (b : Fin k → ℝ) (w : ℝ) : ℝ :=
  ∑ j : Fin k, b j * w ^ ((j : ℕ) + 1)

noncomputable def powerPhaseDerivative {k : ℕ} (b : Fin k → ℝ) (w : ℝ) : ℝ :=
  ∑ j : Fin k, b j * (((j : ℕ) + 1 : ℕ) : ℝ) * w ^ (j : ℕ)

theorem hasDerivAt_powerPhase {k : ℕ} (b : Fin k → ℝ) (w : ℝ) :
    HasDerivAt (powerPhase b) (powerPhaseDerivative b w) w := by
  apply HasDerivAt.fun_sum
  intro j _
  simpa only [Nat.add_sub_cancel, mul_assoc] using!
    (hasDerivAt_pow ((j : ℕ) + 1) w).const_mul (b j)

theorem powerPhase_sub {k : ℕ} (b c : Fin k → ℝ) (w : ℝ) :
    powerPhase (b - c) w = powerPhase b w - powerPhase c w := by
  simp only [powerPhase, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem powerPhaseDerivative_sub {k : ℕ} (b c : Fin k → ℝ) (w : ℝ) :
    powerPhaseDerivative (b - c) w = powerPhaseDerivative b w - powerPhaseDerivative c w := by
  simp only [powerPhaseDerivative, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

noncomputable def polynomialBoxRadius (k : ℕ) (M : ℝ) (j : Fin k) : ℝ :=
  1 / (2 * Real.pi * k * (((j : ℕ) + 1 : ℕ) : ℝ) * M ^ ((j : ℕ) + 1))

theorem polynomialBoxRadius_pos {k : ℕ} (hk : 0 < k) {M : ℝ} (hM : 0 < M) (j : Fin k) :
    0 < polynomialBoxRadius k M j := by
  unfold polynomialBoxRadius
  positivity

theorem powerPhaseDerivative_perturbation_le {k : ℕ} (hk : 0 < k) {M w : ℝ}
    (hM : 0 < M) (hw : 0 ≤ w) (hwM : w ≤ M) (b c : Fin k → ℝ)
    (hbc : ∀ j, |b j - c j| ≤ polynomialBoxRadius k M j) :
    2 * Real.pi * |powerPhaseDerivative b w - powerPhaseDerivative c w| ≤ 1 / M := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  rw [← powerPhaseDerivative_sub]
  calc
    _ ≤ 2 * Real.pi * ∑ j : Fin k,
        |(b j - c j) * (((j : ℕ) + 1 : ℕ) : ℝ) * w ^ (j : ℕ)| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ = ∑ j : Fin k, 2 * Real.pi *
        (|(b j - c j) * (((j : ℕ) + 1 : ℕ) : ℝ) * w ^ (j : ℕ)|) := Finset.mul_sum _ _ _
    _ ≤ ∑ _j : Fin k, 1 / ((k : ℝ) * M) := by
      apply Finset.sum_le_sum
      intro j _
      have hj : (0 : ℝ) < ((j : ℕ) + 1 : ℕ) := by positivity
      rw [abs_mul, abs_mul, abs_of_pos hj, abs_of_nonneg (pow_nonneg hw _)]
      calc
        _ ≤ 2 * Real.pi *
            (polynomialBoxRadius k M j * (((j : ℕ) + 1 : ℕ) : ℝ) * M ^ (j : ℕ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul (mul_le_mul_of_nonneg_right (hbc j) hj.le)
            (pow_le_pow_left₀ hw hwM _) (pow_nonneg hw _)
            (mul_nonneg (polynomialBoxRadius_pos hk hM j).le hj.le)
        _ = _ := by
          unfold polynomialBoxRadius
          rw [pow_succ]
          field_simp
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp

theorem realVinogradovWeylSum_eq_phase_sum {k : ℕ} (b : Fin k → ℝ) (N : ℕ) :
    realVinogradovWeylSum k N b =
      ∑ n ∈ Finset.range N, oscillatoryPhase 1 (2 * Real.pi * powerPhase b ((n : ℝ) + 1)) := by
  unfold realVinogradovWeylSum
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro n _
  unfold oscillatoryPhase powerPhase vinogradovIntegerPoint
  simp only [Complex.ofReal_one, mul_one, Complex.ofReal_mul, Complex.ofReal_sum,
    Complex.ofReal_pow, Complex.ofReal_add, Int.cast_pow, Int.cast_add, Int.cast_one,
    Int.cast_natCast, Complex.ofReal_natCast, Complex.ofReal_ofNat]
  congr 1
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end Erdos421
