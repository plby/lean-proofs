import ErdosProblems.Erdos239.External.Erdos67.LSeriesLogPhaseBridge
import ErdosProblems.Erdos1149.AnalyticParameters
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The elementary low-frequency part of a high L-value

The fixed-depth Weyl argument starts only after a small cutoff.  Below that
cutoff no cancellation is needed: the absolute value of the Dirichlet-series
polynomial is bounded by the corresponding harmonic sum.  Keeping this
estimate exact is useful in the epsilon argument, where the cutoff is chosen
near `|t|^(1/R)` and hence its logarithm costs only `log |t| / R`.
-/

open scoped BigOperators

namespace Erdos67.LSeriesLowCutoff

noncomputable section

open Erdos67.LogPhaseSum

/-- The integer cutoff near `t^(1/R)` used in the fixed-depth epsilon
argument. -/
def heightRootCutoff (t : ℝ) (R : ℕ) : ℕ :=
  Nat.ceil (t ^ (((R : ℕ) : ℝ)⁻¹))

theorem heightRootCutoff_pos {t : ℝ} (ht : 0 < t) (R : ℕ) :
    0 < heightRootCutoff t R := by
  unfold heightRootCutoff
  exact Erdos1149.AnalyticParameters.natCeil_pos
    (Real.rpow_pos_of_pos ht _)

/-- Rounding the root cutoff costs only `log 2`. -/
theorem log_heightRootCutoff_le
    {t : ℝ} (ht : 1 ≤ t) {R : ℕ} (hR : 0 < R) :
    Real.log (heightRootCutoff t R) ≤
      Real.log 2 + Real.log t / R := by
  let x : ℝ := t ^ (((R : ℕ) : ℝ)⁻¹)
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have hxpos : 0 < x := Real.rpow_pos_of_pos htpos _
  have hxOne : 1 ≤ x := Real.one_le_rpow ht (by positivity)
  have hceil : ((heightRootCutoff t R : ℕ) : ℝ) ≤ 2 * x := by
    unfold heightRootCutoff
    exact Erdos1149.AnalyticParameters.natCeil_le_two_mul hxOne
  have hcutpos : (0 : ℝ) < heightRootCutoff t R := by
    exact_mod_cast heightRootCutoff_pos htpos R
  calc
    Real.log (heightRootCutoff t R) ≤ Real.log (2 * x) :=
      Real.strictMonoOn_log.monotoneOn hcutpos
        (show 0 < 2 * x by positivity) hceil
    _ = Real.log 2 + Real.log x := by rw [Real.log_mul] <;> positivity
    _ = Real.log 2 + (((R : ℕ) : ℝ)⁻¹ * Real.log t) := by
      rw [show Real.log x = (((R : ℕ) : ℝ)⁻¹ * Real.log t) by
        dsimp only [x]
        exact Real.log_rpow htpos _]
    _ = Real.log 2 + Real.log t / R := by
      rw [div_eq_mul_inv]
      ring

/-- A Dirichlet character and a logarithmic phase both have norm at most one,
so a finite block at real part at least one is bounded by its harmonic mass. -/
theorem norm_sum_Icc_logPhase_character_rpow_le_harmonic
    {q : ℕ} (chi : DirichletCharacter ℂ q) (t sigma : ℝ) (M : ℕ)
    (hsigma : 1 ≤ sigma) :
    ‖∑ n ∈ Finset.Icc 1 M,
        (natLogTwist n t * chi n) *
          (((n : ℝ) ^ (-sigma) : ℝ) : ℂ)‖ ≤ (harmonic M : ℝ) := by
  calc
    ‖∑ n ∈ Finset.Icc 1 M,
        (natLogTwist n t * chi n) *
          (((n : ℝ) ^ (-sigma) : ℝ) : ℂ)‖ ≤
        ∑ n ∈ Finset.Icc 1 M,
          ‖(natLogTwist n t * chi n) *
            (((n : ℝ) ^ (-sigma) : ℝ) : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 M, ((n : ℝ) : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : 0 < n := by
        exact (Finset.mem_Icc.mp hn).1
      have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
      have hpow : (n : ℝ) ^ (-sigma) ≤ (n : ℝ) ^ (-1 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le hnOne
        linarith
      rw [norm_mul, norm_mul, norm_natLogTwist t hnpos,
        one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
      calc
        ‖chi n‖ * (n : ℝ) ^ (-sigma) ≤
            1 * (n : ℝ) ^ (-sigma) := by
          exact mul_le_mul_of_nonneg_right (chi.norm_le_one n)
            (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        _ ≤ (n : ℝ) ^ (-1 : ℝ) := by simpa using hpow
        _ = ((n : ℝ) : ℝ)⁻¹ := Real.rpow_neg_one n
    _ = (harmonic M : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

/-- The same estimate written directly in `LSeries.term` notation. -/
theorem norm_sum_Icc_character_LSeries_term_le_harmonic
    {q : ℕ} (chi : DirichletCharacter ℂ q) (t sigma : ℝ) (M : ℕ)
    (hsigma : 1 ≤ sigma) :
    ‖∑ n ∈ Finset.Icc 1 M,
        LSeries.term (fun m : ℕ ↦ chi m)
          ((sigma : ℂ) + Complex.I * (t : ℂ)) n‖ ≤
      (harmonic M : ℝ) := by
  rw [Finset.sum_congr rfl (fun n hn ↦
    LSeriesLogPhaseBridge.character_LSeries_term_eq_logPhase_mul_rpow
      chi t sigma (Finset.mem_Icc.mp hn).1)]
  exact norm_sum_Icc_logPhase_character_rpow_le_harmonic
    chi t sigma M hsigma

/-- A logarithmic form, convenient after the cutoff has been chosen. -/
theorem norm_sum_Icc_character_LSeries_term_le_one_add_log
    {q : ℕ} (chi : DirichletCharacter ℂ q) (t sigma : ℝ) (M : ℕ)
    (hsigma : 1 ≤ sigma) :
    ‖∑ n ∈ Finset.Icc 1 M,
        LSeries.term (fun m : ℕ ↦ chi m)
          ((sigma : ℂ) + Complex.I * (t : ℂ)) n‖ ≤
      1 + Real.log M := by
  exact (norm_sum_Icc_character_LSeries_term_le_harmonic
    chi t sigma M hsigma).trans (harmonic_le_one_add_log M)

end

end Erdos67.LSeriesLowCutoff
