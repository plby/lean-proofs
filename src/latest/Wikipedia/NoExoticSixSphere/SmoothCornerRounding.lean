import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A supported smooth rounding of the concave planar corner

A smooth bump inside the square root rounds the absolute value while keeping
it exact outside a prescribed interval. The superlevel of
`t + q + roundedAbs (t - q)` contains `{t ≥ 0 or q ≥ 0}` and changes that
domain only in a bounded square next to the corner. Its actual differential
on the diagonal direction is always two, so every level is regular.
-/

noncomputable section

open Set Function Metric
open scoped ContDiff

namespace NoExoticSixSphere.SmoothCornerRounding

variable (χ : ContDiffBump (0 : ℝ))

def roundedAbs (u : ℝ) : ℝ := Real.sqrt (u ^ 2 + (χ.rIn * χ u) ^ 2)

theorem radicand_pos (u : ℝ) : 0 < u ^ 2 + (χ.rIn * χ u) ^ 2 := by
  by_cases hu : u = 0
  · subst u
    rw [χ.one_of_mem_closedBall (mem_closedBall_self χ.rIn_pos.le)]
    nlinarith [χ.rIn_pos]
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hu) (sq_nonneg _)

theorem contDiff_roundedAbs : ContDiff ℝ ∞ (roundedAbs χ) :=
  ((contDiff_id.pow 2).add ((contDiff_const.mul χ.contDiff).pow 2)).sqrt
    (fun u ↦ ne_of_gt (radicand_pos χ u))

theorem abs_le_roundedAbs (u : ℝ) : |u| ≤ roundedAbs χ u := by
  calc
    |u| = Real.sqrt (u ^ 2) := (Real.sqrt_sq_eq_abs u).symm
    _ ≤ roundedAbs χ u := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))

theorem roundedAbs_le (u : ℝ) : roundedAbs χ u ≤ |u| + χ.rIn := by
  have hc0 : 0 ≤ χ.rIn * χ u := mul_nonneg χ.rIn_pos.le χ.nonneg
  have hc1 : χ.rIn * χ u ≤ χ.rIn := mul_le_of_le_one_right χ.rIn_pos.le χ.le_one
  have hs : (roundedAbs χ u) ^ 2 = u ^ 2 + (χ.rIn * χ u) ^ 2 :=
    Real.sq_sqrt (radicand_pos χ u).le
  have hn : 0 ≤ roundedAbs χ u := Real.sqrt_nonneg _
  nlinarith [abs_nonneg u, sq_abs u, χ.rIn_pos]

theorem roundedAbs_eq_abs {u : ℝ} (hu : χ.rOut ≤ |u|) : roundedAbs χ u = |u| := by
  have hχ : χ u = 0 := χ.zero_of_le_dist (by simpa only [dist_zero_right, Real.norm_eq_abs])
  simp only [roundedAbs, hχ, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero,
    Real.sqrt_sq_eq_abs]

def level (p : ℝ × ℝ) : ℝ := p.1 + p.2 + roundedAbs χ (p.1 - p.2)

theorem contDiff_level : ContDiff ℝ ∞ (level χ) :=
  (contDiff_fst.add contDiff_snd).add
    ((contDiff_roundedAbs χ).comp (contDiff_fst.sub contDiff_snd))

theorem two_fst_le_level (p : ℝ × ℝ) : 2 * p.1 ≤ level χ p := by
  have h := abs_le_roundedAbs χ (p.1 - p.2)
  have ha := le_abs_self (p.1 - p.2)
  dsimp only [level]
  linarith

theorem two_snd_le_level (p : ℝ × ℝ) : 2 * p.2 ≤ level χ p := by
  have h := abs_le_roundedAbs χ (p.1 - p.2)
  have ha := neg_le_abs (p.1 - p.2)
  dsimp only [level]
  linarith

theorem nonneg_of_corner {p : ℝ × ℝ} (hp : 0 ≤ p.1 ∨ 0 ≤ p.2) : 0 ≤ level χ p := by
  rcases hp with hp | hp
  · linarith [two_fst_le_level χ p]
  · linarith [two_snd_le_level χ p]

theorem level_eq_two_max {p : ℝ × ℝ} (hp : χ.rOut ≤ |p.1 - p.2|) :
    level χ p = 2 * max p.1 p.2 := by
  rw [level, roundedAbs_eq_abs χ hp]
  rcases le_total p.1 p.2 with h | h
  · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

theorem added_point_bounds {p : ℝ × ℝ} (hp : 0 ≤ level χ p)
    (ht : p.1 < 0) (hq : p.2 < 0) : -2 * χ.rOut < p.1 ∧ -2 * χ.rOut < p.2 := by
  have hdiff : |p.1 - p.2| < χ.rOut := by
    by_contra hn
    rw [level_eq_two_max χ (le_of_not_gt hn)] at hp
    have hm : max p.1 p.2 < 0 := max_lt ht hq
    linarith
  have hb := roundedAbs_le χ (p.1 - p.2)
  have hr := χ.rIn_lt_rOut
  change 0 ≤ p.1 + p.2 + roundedAbs χ (p.1 - p.2) at hp
  constructor <;> linarith

theorem fderiv_level_diagonal (p : ℝ × ℝ) : fderiv ℝ (level χ) p (1, 1) = 2 := by
  have hsum : HasFDerivAt (fun q : ℝ × ℝ ↦ q.1 + q.2)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ) + (ContinuousLinearMap.snd ℝ ℝ ℝ)) p :=
    hasFDerivAt_fst.add hasFDerivAt_snd
  have hdiff : HasFDerivAt (fun q : ℝ × ℝ ↦ q.1 - q.2)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ) - (ContinuousLinearMap.snd ℝ ℝ ℝ)) p :=
    hasFDerivAt_fst.sub hasFDerivAt_snd
  have hφ := ((contDiff_roundedAbs χ).differentiable (by simp) (p.1 - p.2)).hasFDerivAt
  have h := (hsum.add (hφ.comp p hdiff)).fderiv
  change fderiv ℝ (level χ) p = _ at h
  rw [h]
  change (1 : ℝ) + 1 + fderiv ℝ (roundedAbs χ) (p.1 - p.2) (1 - 1) = 2
  rw [sub_self, map_zero]
  norm_num

theorem surjective_fderiv_level (p : ℝ × ℝ) : Surjective (fderiv ℝ (level χ) p) := by
  intro y
  refine ⟨(y / 2) • (1, 1), ?_⟩
  rw [map_smul, fderiv_level_diagonal]
  change (y / 2) * 2 = y
  ring

end NoExoticSixSphere.SmoothCornerRounding
