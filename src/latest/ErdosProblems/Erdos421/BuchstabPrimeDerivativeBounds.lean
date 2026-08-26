import ErdosProblems.Erdos421.BuchstabPrimeWeight

/-! # Uniform derivative bounds for the Buchstab prime weights -/

namespace Erdos421

theorem logarithmicBuchstabArgument_deriv_abs_le {X t K : ℝ} (hX : 1 < X) (ht : 1 < t)
    (hlog : 1 ≤ Real.log t) (hK : 0 ≤ K) (hscale : Real.log X ≤ K * Real.log t) :
    |deriv (logarithmicBuchstabArgument X) t| ≤ K / t := by
  have htp : 0 < t := by linarith
  have hlp := Real.log_pos ht
  rw [(logarithmicBuchstabArgument_hasDerivAt X ht).deriv, abs_div, abs_neg,
    abs_of_pos (Real.log_pos hX), abs_of_pos (mul_pos htp (sq_pos_of_pos hlp))]
  apply (div_le_div_iff₀ (mul_pos htp (sq_pos_of_pos hlp)) htp).mpr
  have hpow : Real.log t ≤ (Real.log t) ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right
    (hscale.trans (mul_le_mul_of_nonneg_left hpow hK)) htp.le
  nlinarith only [hm]

theorem reciprocalLogSquare_pos {t : ℝ} (ht : 1 < t) : 0 < reciprocalLogSquare t := by
  have htp : 0 < t := by linarith
  have hlp := Real.log_pos ht
  exact div_pos zero_lt_one (mul_pos htp (sq_pos_of_pos hlp))

theorem reciprocalLogSquare_deriv_abs_le {t : ℝ} (ht : 1 < t) (hlog : 1 ≤ Real.log t) :
    |deriv reciprocalLogSquare t| ≤ 3 / (t ^ 2 * (Real.log t) ^ 2) := by
  have htp : 0 < t := by linarith
  have hlp := Real.log_pos ht
  rw [(reciprocalLogSquare_hasDerivAt ht).deriv, abs_div, abs_neg,
    abs_of_pos (by positivity : 0 < Real.log t + 2),
    abs_of_pos (by positivity : 0 < t ^ 2 * (Real.log t) ^ 3)]
  calc
    _ ≤ (3 * Real.log t) / (t ^ 2 * (Real.log t) ^ 3) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by field_simp

theorem buchstabPrimeWeight_abs_le {X t : ℝ} {F : ℝ → ℝ} (ht : 1 < t)
    (hF : |F (logarithmicBuchstabArgument X t)| ≤ 1) :
    |buchstabPrimeWeight X F t| ≤ reciprocalLogSquare t := by
  rw [buchstabPrimeWeight, abs_mul, abs_of_pos (reciprocalLogSquare_pos ht)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hF (reciprocalLogSquare_pos ht).le

theorem buchstabPrimeWeight_deriv_abs_le {X t K : ℝ} {F : ℝ → ℝ} (hX : 1 < X) (ht : 1 < t)
    (hlog : 1 ≤ Real.log t) (hK : 0 ≤ K) (hscale : Real.log X ≤ K * Real.log t)
    (hFd : DifferentiableAt ℝ F (logarithmicBuchstabArgument X t))
    (hF : |F (logarithmicBuchstabArgument X t)| ≤ 1)
    (hF' : |deriv F (logarithmicBuchstabArgument X t)| ≤ 2) :
    |deriv (buchstabPrimeWeight X F) t| ≤ (2 * K + 3) / (t ^ 2 * (Real.log t) ^ 2) := by
  have htp : 0 < t := by linarith
  have hlp := Real.log_pos ht
  have harg := logarithmicBuchstabArgument_deriv_abs_le hX ht hlog hK hscale
  have hrec := reciprocalLogSquare_deriv_abs_le ht hlog
  have hrec0 : 0 ≤ reciprocalLogSquare t := (reciprocalLogSquare_pos ht).le
  have heq : deriv (buchstabPrimeWeight X F) t =
      deriv F (logarithmicBuchstabArgument X t) * deriv (logarithmicBuchstabArgument X) t *
        reciprocalLogSquare t +
        F (logarithmicBuchstabArgument X t) * deriv reciprocalLogSquare t := by
    rw [(buchstabPrimeWeight_hasDerivAt ht hFd).deriv,
      (logarithmicBuchstabArgument_hasDerivAt X ht).deriv,
      (reciprocalLogSquare_hasDerivAt ht).deriv]
  rw [heq]
  calc
    _ ≤ |deriv F (logarithmicBuchstabArgument X t)| *
        |deriv (logarithmicBuchstabArgument X) t| * reciprocalLogSquare t +
        |F (logarithmicBuchstabArgument X t)| * |deriv reciprocalLogSquare t| := by
      simpa only [abs_mul, abs_of_pos (reciprocalLogSquare_pos ht)] using abs_add_le
        (deriv F (logarithmicBuchstabArgument X t) * deriv (logarithmicBuchstabArgument X) t *
          reciprocalLogSquare t)
        (F (logarithmicBuchstabArgument X t) * deriv reciprocalLogSquare t)
    _ ≤ 2 * (K / t) * reciprocalLogSquare t + 1 * (3 / (t ^ 2 * (Real.log t) ^ 2)) := by
      gcongr
    _ = _ := by
      dsimp only [reciprocalLogSquare]
      field_simp

end Erdos421
