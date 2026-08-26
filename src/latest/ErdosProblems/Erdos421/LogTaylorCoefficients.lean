import ErdosProblems.Erdos421.PolynomialPhases
import ErdosProblems.Erdos421.LogTaylorRemainder

/-! # Logarithmic phases localized near their Taylor coefficients -/

namespace Erdos421

noncomputable def logTaylorCoefficients (k : ℕ) (t z : ℝ) (j : Fin k) : ℝ :=
  (-1 : ℝ) ^ (j : ℕ) * t /
    (2 * Real.pi * (((j : ℕ) + 1 : ℕ) : ℝ) * z ^ ((j : ℕ) + 1))

theorem logTaylorCoefficients_phase (k : ℕ) (t z w : ℝ) (hz : z ≠ 0) :
    2 * Real.pi * powerPhase (logTaylorCoefficients k t z) w =
      t * logTaylorPolynomial k z w := by
  unfold powerPhase logTaylorPolynomial
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hj : (((j : ℕ) + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  unfold logTaylorCoefficients
  field_simp

noncomputable def logPhaseRemainder {k : ℕ} (t z : ℝ) (b : Fin k → ℝ) (w : ℝ) : ℝ :=
  t * (Real.log (z + w) - Real.log z) - 2 * Real.pi * powerPhase b w

theorem hasDerivAt_logPhaseRemainder {k : ℕ} (t z w : ℝ) (b : Fin k → ℝ)
    (hz : z ≠ 0) (hzw : z + w ≠ 0) :
    HasDerivAt (logPhaseRemainder t z b)
      (t * ((-w) ^ k / (z ^ k * (z + w))) + 2 * Real.pi *
        (powerPhaseDerivative (logTaylorCoefficients k t z) w - powerPhaseDerivative b w)) w := by
  have h₁ := (hasDerivAt_logTaylorRemainder k hz hzw).const_mul t
  have h₂ := ((hasDerivAt_powerPhase (logTaylorCoefficients k t z) w).sub
    (hasDerivAt_powerPhase b w)).const_mul (2 * Real.pi)
  convert! h₁.add h₂ using 1
  funext x
  dsimp only [logPhaseRemainder, Pi.add_apply, Pi.sub_apply]
  rw [mul_sub (2 * Real.pi), logTaylorCoefficients_phase k t z x hz]
  ring

theorem logPhaseRemainder_derivative_bound {k : ℕ} (hk : 0 < k) {t z M w : ℝ}
    (hz : 0 < z) (hM : 0 < M) (hw : 0 ≤ w) (hwM : w ≤ M) (b : Fin k → ℝ)
    (hb : ∀ j, |b j - logTaylorCoefficients k t z j| ≤ polynomialBoxRadius k M j) :
    |t * ((-w) ^ k / (z ^ k * (z + w))) + 2 * Real.pi *
      (powerPhaseDerivative (logTaylorCoefficients k t z) w - powerPhaseDerivative b w)| ≤
        |t| * M ^ k / z ^ (k + 1) + 1 / M := by
  have htail := logTaylorRemainder_derivative_abs_le k hz hw hwM
  have hcoeff := powerPhaseDerivative_perturbation_le hk hM hw hwM b
    (logTaylorCoefficients k t z) hb
  calc
    _ ≤ |t * ((-w) ^ k / (z ^ k * (z + w)))| +
        |2 * Real.pi * (powerPhaseDerivative (logTaylorCoefficients k t z) w -
          powerPhaseDerivative b w)| := abs_add_le _ _
    _ = |t| * |(-w) ^ k / (z ^ k * (z + w))| +
        2 * Real.pi * |powerPhaseDerivative b w -
          powerPhaseDerivative (logTaylorCoefficients k t z) w| := by
      rw [abs_mul, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi), abs_sub_comm]
    _ ≤ |t| * (M ^ k / z ^ (k + 1)) + 1 / M :=
      add_le_add (mul_le_mul_of_nonneg_left htail (abs_nonneg t)) hcoeff
    _ = _ := by ring

theorem logPhaseRemainder_lipschitz {k : ℕ} (hk : 0 < k) {t z M x y : ℝ}
    (hz : 0 < z) (hM : 0 < M) (hscale : |t| * M ^ (k + 1) ≤ z ^ (k + 1))
    (b : Fin k → ℝ)
    (hb : ∀ j, |b j - logTaylorCoefficients k t z j| ≤ polynomialBoxRadius k M j)
    (hx : x ∈ Set.Icc 0 M) (hy : y ∈ Set.Icc 0 M) :
    |logPhaseRemainder t z b y - logPhaseRemainder t z b x| ≤ 2 / M * |y - x| := by
  have hsmall : |t| * M ^ k / z ^ (k + 1) ≤ 1 / M := by
    apply (div_le_div_iff₀ (pow_pos hz _) hM).mpr
    simpa only [one_mul, mul_assoc, ← pow_succ] using hscale
  have hd : ∀ w ∈ Set.Icc 0 M, HasDerivWithinAt (logPhaseRemainder t z b)
      (t * ((-w) ^ k / (z ^ k * (z + w))) + 2 * Real.pi *
        (powerPhaseDerivative (logTaylorCoefficients k t z) w - powerPhaseDerivative b w))
          (Set.Icc 0 M) w := by
    intro w hw
    exact (hasDerivAt_logPhaseRemainder t z w b hz.ne' (by linarith [hw.1])).hasDerivWithinAt
  have hbound : ∀ w ∈ Set.Icc 0 M,
      ‖t * ((-w) ^ k / (z ^ k * (z + w))) + 2 * Real.pi *
        (powerPhaseDerivative (logTaylorCoefficients k t z) w - powerPhaseDerivative b w)‖ ≤
          2 / M := by
    intro w hw
    rw [Real.norm_eq_abs]
    have h := logPhaseRemainder_derivative_bound hk hz hM hw.1 hw.2 b hb
    exact h.trans ((add_le_add hsmall le_rfl).trans_eq (by ring))
  simpa only [Real.norm_eq_abs] using!
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hbound (convex_Icc 0 M) hx hy

end Erdos421
