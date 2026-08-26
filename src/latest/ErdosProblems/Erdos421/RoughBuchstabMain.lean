import ErdosProblems.Erdos421.BuchstabPrimeIntegral
import ErdosProblems.Erdos421.RoughSquareCutoff

/-! # Exact main terms and boundary corrections in the Buchstab recurrence -/

namespace Erdos421

noncomputable def roughCountMain (n : ℕ) (a b : ℝ) (z : ℕ) : ℝ :=
  (b - max a z) / Real.log z * finiteBuchstab n (Real.log b / Real.log z)

theorem cofactor_logarithmic_argument {b p : ℝ} (hb : 0 < b) (hp : 1 < p) :
    Real.log (b / p) / Real.log p = logarithmicBuchstabArgument b p := by
  have hpp : 0 < p := by linarith
  have hlog := Real.log_pos hp
  rw [Real.log_div hb.ne' hpp.ne', logarithmicBuchstabArgument]
  field_simp

theorem clipped_cofactor_length {a b p : ℝ} (hp : 0 < p) :
    b / p - max (a / p) p = (b - a - max (p ^ 2 - a) 0) / p := by
  have hp2 : p ^ 2 / p = p := by field_simp
  have hm : max (a / p) p = max a (p ^ 2) / p := by
    calc
      _ = max (a / p) (p ^ 2 / p) := by rw [hp2]
      _ = _ := max_div_div_right hp.le a (p ^ 2)
  have hmax := max_sub_sub_right a (p ^ 2) a
  rw [sub_self, max_comm] at hmax
  rw [hm, hmax]
  ring

theorem rough_cofactor_main_correction (n : ℕ) {a b : ℝ} {p : ℕ}
    (hb : 0 < b) (hp : 2 ≤ p) :
    (b - a) * (finiteBuchstab n (logarithmicBuchstabArgument b p) /
        ((p : ℝ) * Real.log p)) - roughCountMain n (a / p) (b / p) p =
      max ((p : ℝ) ^ 2 - a) 0 / ((p : ℝ) * Real.log p) *
        finiteBuchstab n (logarithmicBuchstabArgument b p) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hpp : (0 : ℝ) < p := by linarith
  rw [roughCountMain, cofactor_logarithmic_argument hb hp1, clipped_cofactor_length hpp]
  ring

end Erdos421
