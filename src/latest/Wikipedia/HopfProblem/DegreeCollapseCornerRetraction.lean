import Wikipedia.NoExoticSixSphere.RoundedHandleCorner

/-!
# An explicit deformation back to the unrounded corner

In radius-square and height coordinates, move both corner coordinates by
the same nonnegative amount. The rounded level rises by twice that amount.
The denominator is bounded below by the positive handle radius squared,
so the radial formula is continuous even at the transverse origin.
-/

noncomputable section

open Set Function Metric

namespace Wikipedia.HopfProblem.DegreeCollapse.CornerRetraction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def shift (r : ℝ) (p : E × ℝ) : ℝ := max 0 (min (‖p.1‖ ^ 2 - r ^ 2) (-p.2))

def denominator (r : ℝ) (v : E) : ℝ := max (r ^ 2) (‖v‖ ^ 2)

def deform (r : ℝ) (t : ℝ) (p : E × ℝ) : E × ℝ :=
  (Real.sqrt (1 - t * shift r p / denominator r p.1) • p.1, p.2 + t * shift r p)

theorem shift_nonneg (r : ℝ) (p : E × ℝ) : 0 ≤ shift r p := le_max_left _ _

theorem denominator_pos {r : ℝ} (hr : 0 < r) (v : E) : 0 < denominator r v :=
  (sq_pos_of_pos hr).trans_le (le_max_left _ _)

theorem positive_shift_bounds {r : ℝ} {p : E × ℝ} (h : 0 < shift r p) :
    r ^ 2 < ‖p.1‖ ^ 2 ∧ shift r p ≤ ‖p.1‖ ^ 2 - r ^ 2 ∧
      shift r p ≤ -p.2 ∧ p.2 < 0 := by
  have hm : 0 < min (‖p.1‖ ^ 2 - r ^ 2) (-p.2) := by
    simpa only [shift, lt_max_iff, lt_self_iff_false, false_or] using h
  have hq := (lt_min_iff.mp hm).1
  have ht := (lt_min_iff.mp hm).2
  have he : shift r p = min (‖p.1‖ ^ 2 - r ^ 2) (-p.2) := max_eq_right hm.le
  refine ⟨by linarith, ?_, ?_, by linarith⟩
  · rw [he]
    exact min_le_left _ _
  · rw [he]
    exact min_le_right _ _

theorem shift_lt_denominator {r : ℝ} (hr : 0 < r) (p : E × ℝ) :
    shift r p < denominator r p.1 := by
  rcases eq_or_lt_of_le (shift_nonneg r p) with h | h
  · rw [← h]
    exact denominator_pos hr p.1
  · have hb := positive_shift_bounds h
    have hsq := sq_pos_of_pos hr
    exact (lt_of_le_of_lt hb.2.1 (by linarith)).trans_le (le_max_right _ _)

theorem radicand_pos {r t : ℝ} (hr : 0 < r) (ht : t ∈ Icc (0 : ℝ) 1) (p : E × ℝ) :
    0 < 1 - t * shift r p / denominator r p.1 := by
  have hd := denominator_pos hr p.1
  have hs := shift_lt_denominator hr p
  have hts : t * shift r p ≤ shift r p :=
    mul_le_of_le_one_left (shift_nonneg r p) ht.2
  have hquot : t * shift r p / denominator r p.1 < 1 :=
    (div_lt_one hd).mpr (hts.trans_lt hs)
  linarith

theorem continuous_deform {r : ℝ} (hr : 0 < r) :
    Continuous (fun z : ℝ × (E × ℝ) ↦ deform r z.1 z.2) := by
  have hshift : Continuous (shift (E := E) r) := by unfold shift; fun_prop
  have hden : Continuous (denominator (E := E) r) := by unfold denominator; fun_prop
  have hrad : Continuous (fun z : ℝ × (E × ℝ) ↦
      1 - z.1 * shift r z.2 / denominator r z.2.1) :=
    continuous_const.sub ((continuous_fst.mul (hshift.comp continuous_snd)).div
      (hden.comp (continuous_fst.comp continuous_snd))
      (fun z ↦ (denominator_pos hr z.2.1).ne'))
  exact (hrad.sqrt.smul (continuous_fst.comp continuous_snd)).prodMk
    ((continuous_snd.comp continuous_snd).add (continuous_fst.mul (hshift.comp continuous_snd)))

theorem deform_zero (r : ℝ) (p : E × ℝ) : deform r 0 p = p := by
  simp [deform]

theorem deform_fixed_of_shift_zero {r : ℝ} {p : E × ℝ} (hp : shift r p = 0) (t : ℝ) :
    deform r t p = p := by
  simp [deform, hp]

theorem shift_zero_of_corner {r : ℝ} (hr : 0 ≤ r) {p : E × ℝ}
    (hp : 0 ≤ p.2 ∨ p.1 ∈ closedBall (0 : E) r) : shift r p = 0 := by
  apply max_eq_left
  rcases hp with ht | hv
  · exact (min_le_right _ _).trans (neg_nonpos.mpr ht)
  · have hn : ‖p.1‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hv
    exact (min_le_left _ _).trans (by nlinarith [norm_nonneg p.1])

theorem deform_fixed_of_corner {r : ℝ} (hr : 0 ≤ r) {p : E × ℝ}
    (hp : 0 ≤ p.2 ∨ p.1 ∈ closedBall (0 : E) r) (t : ℝ) : deform r t p = p :=
  deform_fixed_of_shift_zero (shift_zero_of_corner hr hp) t

theorem norm_sq_deform {r t : ℝ} (hr : 0 < r) (ht : t ∈ Icc (0 : ℝ) 1) (p : E × ℝ) :
    ‖(deform r t p).1‖ ^ 2 = ‖p.1‖ ^ 2 - t * shift r p := by
  rcases eq_or_lt_of_le (shift_nonneg r p) with h | h
  · rw [deform_fixed_of_shift_zero h.symm, ← h, mul_zero, sub_zero]
  · have hb := positive_shift_bounds h
    have hd : denominator r p.1 = ‖p.1‖ ^ 2 := max_eq_right hb.1.le
    have hn : ‖p.1‖ ^ 2 ≠ 0 := (lt_trans (sq_pos_of_pos hr) hb.1).ne'
    change ‖Real.sqrt (1 - t * shift r p / denominator r p.1) • p.1‖ ^ 2 = _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt (radicand_pos hr ht p).le, hd]
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hn]

theorem deform_one_mem_corner {r : ℝ} (hr : 0 < r) (p : E × ℝ) :
    0 ≤ (deform r 1 p).2 ∨ (deform r 1 p).1 ∈ closedBall (0 : E) r := by
  by_cases hc : 0 ≤ p.2 ∨ p.1 ∈ closedBall (0 : E) r
  · rwa [deform_fixed_of_corner hr.le hc]
  have ht : p.2 < 0 := lt_of_not_ge (not_or.mp hc).1
  have hn : r < ‖p.1‖ := by
    simpa only [mem_closedBall, dist_zero_right, not_le] using (not_or.mp hc).2
  have hq : 0 < ‖p.1‖ ^ 2 - r ^ 2 := by nlinarith [norm_nonneg p.1]
  have hs : shift r p = min (‖p.1‖ ^ 2 - r ^ 2) (-p.2) :=
    max_eq_right (le_min hq.le (by linarith))
  rcases le_total (-p.2) (‖p.1‖ ^ 2 - r ^ 2) with h | h
  · left
    change 0 ≤ p.2 + 1 * shift r p
    rw [hs, min_eq_right h]
    linarith
  · right
    have he := norm_sq_deform hr (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1) p
    rw [hs, min_eq_left h, one_mul] at he
    rw [mem_closedBall, dist_zero_right]
    nlinarith [norm_nonneg (deform r 1 p).1]

theorem level_deform (χ : ContDiffBump (0 : ℝ)) {r t : ℝ} (hr : 0 < r)
    (ht : t ∈ Icc (0 : ℝ) 1) (p : NoExoticSixSphere.GLOrthonormalization.Vector 3 × ℝ) :
    NoExoticSixSphere.RoundedHandleCorner.level χ r (deform r t p) =
      NoExoticSixSphere.RoundedHandleCorner.level χ r p + 2 * t * shift r p := by
  have hn := norm_sq_deform hr ht p
  unfold NoExoticSixSphere.RoundedHandleCorner.level
    NoExoticSixSphere.RoundedHandleCorner.coordinates NoExoticSixSphere.SmoothCornerRounding.level
  dsimp only [Function.comp_apply]
  rw [hn]
  change (p.2 + t * shift r p) + (r ^ 2 - (‖p.1‖ ^ 2 - t * shift r p)) +
      NoExoticSixSphere.SmoothCornerRounding.roundedAbs χ
        ((p.2 + t * shift r p) - (r ^ 2 - (‖p.1‖ ^ 2 - t * shift r p))) = _
  have hd : (p.2 + t * shift r p) - (r ^ 2 - (‖p.1‖ ^ 2 - t * shift r p)) =
      p.2 - (r ^ 2 - ‖p.1‖ ^ 2) := by ring
  rw [hd]
  ring

end Wikipedia.HopfProblem.DegreeCollapse.CornerRetraction
