import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# The explicit inward-depth function at an attached-handle corner

The radial corner map sends a new-face radius `r` and collar depth `w`
to old radial coordinate `r * (1 + w) - 1` and normal deficit
`w * (1 - r)`. The positive quadratic root below recovers precisely `w`.
Its continuity will identify the open image of the assembled collar.
-/

noncomputable section

namespace Wikipedia.SmoothSixDPoincare.HandleCollarDepth

def depth (t d : ℝ) : ℝ := (t + d + Real.sqrt ((t + d) ^ 2 + 4 * d)) / 2

theorem continuous_depth : Continuous (fun p : ℝ × ℝ => depth p.1 p.2) :=
  ((continuous_fst.add continuous_snd).add
    (((continuous_fst.add continuous_snd).pow 2).add
      (continuous_const.mul continuous_snd)).sqrt).div_const 2

theorem radicand_nonneg (t : ℝ) {d : ℝ} (hd : 0 ≤ d) : 0 ≤ (t + d) ^ 2 + 4 * d := by
  nlinarith [sq_nonneg (t + d)]

theorem sqrt_ge_abs (t : ℝ) {d : ℝ} (hd : 0 ≤ d) :
    |t + d| ≤ Real.sqrt ((t + d) ^ 2 + 4 * d) := by
  have h := Real.sqrt_le_sqrt (show (t + d) ^ 2 ≤ (t + d) ^ 2 + 4 * d by linarith)
  simpa only [Real.sqrt_sq_eq_abs] using h

theorem depth_nonneg (t : ℝ) {d : ℝ} (hd : 0 ≤ d) : 0 ≤ depth t d := by
  have h := sqrt_ge_abs t hd
  have ha := neg_le_abs (t + d)
  unfold depth
  linarith

theorem depth_ge_sum (t : ℝ) {d : ℝ} (hd : 0 ≤ d) : t + d ≤ depth t d := by
  have h := sqrt_ge_abs t hd
  have ha := le_abs_self (t + d)
  unfold depth
  linarith

theorem depth_ge_left (t : ℝ) {d : ℝ} (hd : 0 ≤ d) : t ≤ depth t d :=
  (le_add_of_nonneg_right hd).trans (depth_ge_sum t hd)

theorem depth_equation (t : ℝ) {d : ℝ} (hd : 0 ≤ d) :
    depth t d ^ 2 - (t + d) * depth t d - d = 0 := by
  have h := Real.sq_sqrt (radicand_nonneg t hd)
  unfold depth
  nlinarith

theorem depth_ge_deficit {t d : ℝ} (ht : -1 ≤ t) (hd : 0 ≤ d) : d ≤ depth t d := by
  have hw := depth_nonneg t hd
  have he := depth_equation t hd
  have hp := mul_nonneg (show 0 ≤ t + 1 by linarith) hw
  have hprod : 0 ≤ (depth t d + 1) * (depth t d - d) := by nlinarith
  have hdiff : 0 ≤ depth t d - d :=
    nonneg_of_mul_nonneg_right hprod (by linarith : 0 < depth t d + 1)
  linarith

theorem depth_zero_deficit (t : ℝ) : depth t 0 = max t 0 := by
  simp only [depth, add_zero, mul_zero, Real.sqrt_sq_eq_abs]
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht, max_eq_left ht]
    ring
  · rw [abs_of_nonpos (le_of_not_ge ht), max_eq_right (le_of_not_ge ht)]
    ring

theorem depth_corner {r w : ℝ} (hr : r ≤ 1) (hw : 0 ≤ w) :
    depth (r * (1 + w) - 1) (w * (1 - r)) = w := by
  have hsq : (r * (1 + w) - 1 + w * (1 - r)) ^ 2 + 4 * (w * (1 - r)) =
      (1 - r + w) ^ 2 := by ring
  unfold depth
  rw [hsq, Real.sqrt_sq (by linarith : 0 ≤ 1 - r + w)]
  ring

def radius (t d : ℝ) : ℝ := (t + 1) / (1 + depth t d)

theorem radius_nonneg {t d : ℝ} (ht : -1 ≤ t) (hd : 0 ≤ d) : 0 ≤ radius t d :=
  div_nonneg (by linarith) (by linarith [depth_nonneg t hd])

theorem radius_le_one (t : ℝ) {d : ℝ} (hd : 0 ≤ d) : radius t d ≤ 1 := by
  have hw := depth_nonneg t hd
  exact (div_le_one (by linarith : 0 < 1 + depth t d)).mpr
    (by linarith [depth_ge_left t hd])

theorem radius_reconstruct (t : ℝ) {d : ℝ} (hd : 0 ≤ d) :
    radius t d * (1 + depth t d) - 1 = t := by
  have hw := depth_nonneg t hd
  rw [radius, div_mul_cancel₀ _ (by linarith : 1 + depth t d ≠ 0)]
  ring

theorem deficit_reconstruct (t : ℝ) {d : ℝ} (hd : 0 ≤ d) :
    depth t d * (1 - radius t d) = d := by
  have hw := depth_nonneg t hd
  have he := depth_equation t hd
  have hden : 1 + depth t d ≠ 0 := by linarith
  unfold radius
  apply (mul_right_inj' hden).mp
  field_simp
  nlinarith

theorem normal_pos_of_depth_lt_one {t d : ℝ} (ht : -1 ≤ t) (hd : 0 ≤ d)
    (hw : depth t d < 1) : 0 < 1 - d := by
  linarith [depth_ge_deficit ht hd]

end Wikipedia.SmoothSixDPoincare.HandleCollarDepth
