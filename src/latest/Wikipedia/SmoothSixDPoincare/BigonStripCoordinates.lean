import Wikipedia.SmoothSixDPoincare.BigonCornerCoordinates
import Wikipedia.SmoothSixDPoincare.StripReflection
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Smooth coordinates along both bigon edges

The transverse scale stays positive on the entire real line. The lower and
upper strip coordinates preserve the original boundary time and agree with
the exact straightening coordinates near the left corner. At the right
corner they use the same construction with reversed time.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.WhitneyPairModel

def cornerTransition (t : ℝ) : ℝ := Real.smoothTransition (3 * t - 1)

def cornerScale (t : ℝ) : ℝ :=
  (1 - cornerTransition t) * (1 - t) + cornerTransition t * t

def cornerSign (t : ℝ) : ℝ := 2 * cornerTransition t - 1

theorem contDiff_cornerTransition : ContDiff ℝ ∞ cornerTransition := by
  unfold cornerTransition
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

theorem cornerTransition_zero {t : ℝ} (ht : t ≤ 1 / 3) : cornerTransition t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem cornerTransition_one {t : ℝ} (ht : 2 / 3 ≤ t) : cornerTransition t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem cornerScale_pos (t : ℝ) : 0 < cornerScale t := by
  by_cases hlo : t ≤ 1 / 3
  · simp only [cornerScale, cornerTransition_zero hlo, sub_zero, one_mul, zero_mul, add_zero]
    linarith
  by_cases hhi : 2 / 3 ≤ t
  · simp only [cornerScale, cornerTransition_one hhi, sub_self, zero_mul, one_mul, zero_add]
    linarith
  have h0 : 0 ≤ cornerTransition t := Real.smoothTransition.nonneg _
  have h1 : cornerTransition t ≤ 1 := Real.smoothTransition.le_one _
  have ht0 : 0 < t := by linarith
  have ht1 : 0 < 1 - t := by linarith
  by_cases hβ : cornerTransition t = 0
  · simp only [cornerScale, hβ, sub_zero, one_mul, zero_mul, add_zero]
    exact ht1
  · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr h1) ht1.le)
      (mul_pos (lt_of_le_of_ne h0 (Ne.symm hβ)) ht0)

theorem contDiff_cornerScale : ContDiff ℝ ∞ cornerScale := by
  exact ((contDiff_const.sub contDiff_cornerTransition).mul
    (contDiff_const.sub contDiff_id)).add (contDiff_cornerTransition.mul contDiff_id)

theorem contDiff_cornerSign : ContDiff ℝ ∞ cornerSign :=
  (contDiff_const.mul contDiff_cornerTransition).sub contDiff_const

/-- Exchange the parabolic upper and straight lower edges. -/
def exchangeEdges (h : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1, h * (1 - p.1 ^ 2) - p.2)

theorem contDiff_exchangeEdges (h : ℝ) : ContDiff ℝ ∞ (exchangeEdges h) := by
  unfold exchangeEdges
  fun_prop

theorem exchangeEdges_involutive (h : ℝ) : Involutive (exchangeEdges h) := by
  intro p
  apply Prod.ext <;> dsimp [exchangeEdges]
  ring

def lowerStripCoordinates (h : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (arcTime p + cornerSign (arcTime p) * (p.2 / (4 * h * cornerScale (arcTime p))),
    p.2 / (4 * h * cornerScale (arcTime p)))

def upperStripCoordinates (h : ℝ) : (ℝ × ℝ) → ℝ × ℝ :=
  lowerStripCoordinates h ∘ exchangeEdges h

theorem contDiff_lowerStripCoordinates {h : ℝ} (hh : h ≠ 0) :
    ContDiff ℝ ∞ (lowerStripCoordinates h) := by
  have hd : ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.2 / (4 * h * cornerScale (arcTime p))) :=
    contDiff_snd.div (contDiff_const.mul (contDiff_cornerScale.comp contDiff_arcTime))
      (fun p => mul_ne_zero (mul_ne_zero (by norm_num) hh) (cornerScale_pos _).ne')
  exact (contDiff_arcTime.add ((contDiff_cornerSign.comp contDiff_arcTime).mul hd)).prodMk hd

theorem contDiff_upperStripCoordinates {h : ℝ} (hh : h ≠ 0) :
    ContDiff ℝ ∞ (upperStripCoordinates h) :=
  (contDiff_lowerStripCoordinates hh).comp (contDiff_exchangeEdges h)

theorem lowerStripCoordinates_lower (h t : ℝ) :
    lowerStripCoordinates h (2 * t - 1, 0) = (t, 0) := by
  simp only [lowerStripCoordinates, arcTime, zero_div, mul_zero, add_zero]
  congr 1
  ring

theorem upperStripCoordinates_upper (h t : ℝ) :
    upperStripCoordinates h (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) = (t, 0) := by
  simp only [upperStripCoordinates, Function.comp_apply, exchangeEdges, sub_self]
  exact lowerStripCoordinates_lower h t

theorem lowerStripCoordinates_left (h : ℝ) {p : ℝ × ℝ} (hp : arcTime p ≤ 1 / 3) :
    lowerStripCoordinates h p = leftCornerCoordinates h p := by
  simp [lowerStripCoordinates, cornerSign, cornerScale, cornerTransition_zero hp,
    leftCornerCoordinates, sub_eq_add_neg]

theorem upperStripCoordinates_left {h : ℝ} (hh : h ≠ 0) {p : ℝ × ℝ}
    (hp : arcTime p ≤ 1 / 3) :
    upperStripCoordinates h p = (leftCornerCoordinates h p).swap := by
  have htime : arcTime (exchangeEdges h p) = arcTime p := rfl
  have hp' : arcTime p ≠ 1 := by linarith
  change lowerStripCoordinates h (exchangeEdges h p) = _
  rw [lowerStripCoordinates_left h (htime ▸ hp)]
  exact leftCornerCoordinates_exchange hh hp'

theorem lowerStripCoordinates_right (h : ℝ) {p : ℝ × ℝ} (hp : 2 / 3 ≤ arcTime p) :
    StripCoordinates.reverse (lowerStripCoordinates h p) = rightCornerCoordinates h p := by
  have hden : 1 - arcTime (bigonReflection p) = arcTime p := by
    rw [arcTime_bigonReflection]
    ring
  simp only [lowerStripCoordinates, cornerSign, cornerScale, cornerTransition_one hp,
    sub_self, zero_mul, one_mul, zero_add]
  norm_num only [mul_one, sub_self, sub_zero]
  change (1 - (arcTime p + 1 * (p.2 / (4 * h * arcTime p))),
    p.2 / (4 * h * arcTime p)) = leftCornerCoordinates h (bigonReflection p)
  simp only [leftCornerCoordinates]
  rw [hden, arcTime_bigonReflection]
  simp only [bigonReflection_apply]
  apply Prod.ext
  · dsimp
    ring
  · rfl

theorem upperStripCoordinates_right {h : ℝ} (hh : h ≠ 0) {p : ℝ × ℝ}
    (hp : 2 / 3 ≤ arcTime p) :
    StripCoordinates.reverse (upperStripCoordinates h p) =
      (rightCornerCoordinates h p).swap := by
  have htime : arcTime (exchangeEdges h p) = arcTime p := rfl
  change StripCoordinates.reverse (lowerStripCoordinates h (exchangeEdges h p)) = _
  rw [lowerStripCoordinates_right h (htime ▸ hp)]
  have heq : bigonReflection (exchangeEdges h p) =
      ((bigonReflection p).1, h * (1 - (bigonReflection p).1 ^ 2) - (bigonReflection p).2) := by
    simp only [bigonReflection_apply, exchangeEdges, neg_sq]
  change leftCornerCoordinates h (bigonReflection (exchangeEdges h p)) = _
  rw [heq]
  apply leftCornerCoordinates_exchange hh
  rw [arcTime_bigonReflection]
  linarith

end Wikipedia.SmoothSixDPoincare.WhitneyPairModel
