import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# A smooth radial profile with an exact flat end

The shifted exponential glue is zero up to time `-1` and strictly increases
from zero to one thereafter. Its explicit inverse gives smooth radial time
coordinates. Pairing this profile with its time reverse supplies a neck
whose two ends lie exactly in the two original coordinate three-planes.
-/

noncomputable section

open Set Function
open scoped ContDiff

namespace NoExoticSixSphere.SphereSumNeck

def profile (t : ℝ) : ℝ := expNegInvGlue (t + 1)

def radialTime (r : ℝ) : ℝ := -1 / Real.log r - 1

theorem contDiff_profile : ContDiff ℝ ∞ profile :=
  expNegInvGlue.contDiff.comp (contDiff_id.add contDiff_const)

theorem profile_nonneg (t : ℝ) : 0 ≤ profile t := expNegInvGlue.nonneg _

theorem profile_zero_iff (t : ℝ) : profile t = 0 ↔ t ≤ -1 := by
  rw [profile, expNegInvGlue.zero_iff_nonpos]
  constructor <;> intro h <;> linarith

theorem profile_pos_iff (t : ℝ) : 0 < profile t ↔ -1 < t := by
  constructor
  · intro h
    by_contra ht
    have he := (profile_zero_iff t).mpr (le_of_not_gt ht)
    rw [he] at h
    exact (lt_irrefl 0 h).elim
  · intro h
    exact expNegInvGlue.pos_of_pos (by linarith)

theorem profile_lt_one (t : ℝ) : profile t < 1 := by
  by_cases ht : 0 < t + 1
  · change expNegInvGlue (t + 1) < 1
    rw [expNegInvGlue, if_neg (not_le.mpr ht)]
    exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos (inv_pos.mpr ht))
  · rw [(profile_zero_iff t).mpr (by linarith)]
    norm_num

theorem profile_mem_Ioo {t : ℝ} (ht : -1 < t) : profile t ∈ Ioo (0 : ℝ) 1 :=
  ⟨(profile_pos_iff t).mpr ht, profile_lt_one t⟩

theorem radialTime_gt {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) : -1 < radialTime r := by
  have hl : Real.log r < 0 := Real.log_neg hr.1 hr.2
  have hp : 0 < -1 / Real.log r := div_pos_of_neg_of_neg (by norm_num) hl
  dsimp [radialTime]
  linarith

theorem radialTime_profile {t : ℝ} (ht : -1 < t) : radialTime (profile t) = t := by
  have hp : 0 < t + 1 := by linarith
  simp only [radialTime, profile, expNegInvGlue, if_neg (not_le.mpr hp), Real.log_exp]
  simp [div_eq_mul_inv]

theorem profile_radialTime {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) : profile (radialTime r) = r := by
  have ht : 0 < radialTime r + 1 := by linarith [radialTime_gt hr]
  have hl : Real.log r ≠ 0 := (Real.log_neg hr.1 hr.2).ne
  rw [profile, expNegInvGlue, if_neg (not_le.mpr ht)]
  have he : -(radialTime r + 1)⁻¹ = Real.log r := by
    simp [radialTime, div_eq_mul_inv]
  rw [he, Real.exp_log hr.1]

theorem contDiffAt_radialTime {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ radialTime r :=
  (contDiffAt_const.div (Real.contDiffAt_log.mpr hr.1.ne') (Real.log_neg hr.1 hr.2).ne).sub
    contDiffAt_const

def speed (t : ℝ) : ℝ := ((t + 1)⁻¹) ^ 2 * profile t

theorem hasDerivAt_profile (t : ℝ) : HasDerivAt profile (speed t) t := by
  have h := (expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ) (t + 1)).comp t
    ((hasDerivAt_id t).add_const 1)
  simpa [profile, speed, Function.comp_def] using! h

theorem speed_pos {t : ℝ} (ht : -1 < t) : 0 < speed t := by
  have hp : 0 < t + 1 := by linarith
  exact mul_pos (sq_pos_of_pos (inv_pos.mpr hp)) ((profile_pos_iff t).mpr ht)

theorem profile_or_reverse_pos (t : ℝ) : 0 < profile t ∨ 0 < profile (-t) := by
  by_cases ht : -1 < t
  · exact Or.inl ((profile_pos_iff t).mpr ht)
  · exact Or.inr ((profile_pos_iff (-t)).mpr (by linarith))

end NoExoticSixSphere.SphereSumNeck
