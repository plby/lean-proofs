import ErdosProblems.Erdos421.BuchstabLipschitz
import ErdosProblems.Erdos421.RoughBuchstabMain
import ErdosProblems.Erdos421.InverseLogInterval

/-! # Freezing the Buchstab main term at the left endpoint -/

namespace Erdos421

theorem frozen_buchstab_main_error (n : ℕ) {x t : ℝ} {z : ℕ}
    (hx : 1 < x) (hxt : x ≤ t) (hz : 2 ≤ z) (hzx : (z : ℝ) ≤ x)
    (hu : 2 ≤ Real.log x / Real.log z) :
    |roughCountMain (n + 1) x t z -
      (t - x) * finiteBuchstab (n + 1) (Real.log x / Real.log z) / Real.log z| ≤
      (t - x) ^ 2 / (x * (Real.log z) ^ 2) := by
  have hxp : 0 < x := by linarith
  have hz1 : (1 : ℝ) < z := by exact_mod_cast (show 1 < z by omega)
  have hLz := Real.log_pos hz1
  have hlogxt := Real.log_le_log hxp hxt
  have huv : Real.log x / Real.log z ≤ Real.log t / Real.log z :=
    div_le_div_of_nonneg_right hlogxt hLz.le
  have hlip := finiteBuchstab_upper_lipschitz n hu (hu.trans huv)
  have hdiff : Real.log t / Real.log z - Real.log x / Real.log z =
      (Real.log t - Real.log x) / Real.log z := by ring
  rw [abs_of_nonneg (sub_nonneg.mpr huv), hdiff] at hlip
  have hfreeze := hlip.trans (div_le_div_of_nonneg_right (log_interval_growth hxp hxt) hLz.le)
  have heq : roughCountMain (n + 1) x t z -
      (t - x) * finiteBuchstab (n + 1) (Real.log x / Real.log z) / Real.log z =
      ((t - x) / Real.log z) * (finiteBuchstab (n + 1) (Real.log t / Real.log z) -
        finiteBuchstab (n + 1) (Real.log x / Real.log z)) := by
    rw [roughCountMain, max_eq_left hzx]
    ring
  rw [heq, abs_mul, abs_of_nonneg (div_nonneg (sub_nonneg.mpr hxt) hLz.le)]
  calc
    _ ≤ ((t - x) / Real.log z) * (((t - x) / x) / Real.log z) :=
      mul_le_mul_of_nonneg_left hfreeze (div_nonneg (sub_nonneg.mpr hxt) hLz.le)
    _ = _ := by ring

end Erdos421
