import Wikipedia.SmoothSixDPoincare.BigonStripCoordinates
import Wikipedia.SmoothSixDPoincare.StripNormalDetector
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The edge-coordinate maps are immersive on their full boundary arcs

The lower coordinate derivative has a nonzero horizontal component and a
nonzero transverse component. The upper map is its composition with the
smooth involution exchanging the two edges. Both endpoint derivatives are
included in the construction.
-/

noncomputable section

open Function
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.WhitneyPairModel

theorem lowerStripCoordinates_horizontal_derivative {h : ℝ} (hh : h ≠ 0) (s : ℝ) :
    fderiv ℝ (lowerStripCoordinates h) (s, 0) (1, 0) = (1 / 2, 0) := by
  have hf : DifferentiableAt ℝ (lowerStripCoordinates h) (s, 0) :=
    (contDiff_lowerStripCoordinates hh).contDiffAt.differentiableAt (by simp)
  have hd := StripCoordinates.hasDerivAt_horizontalSlice hf
  have heq : (fun x : ℝ => lowerStripCoordinates h (x, 0)) =
      fun x => ((x + 1) / 2, 0) := by
    funext x
    simp [lowerStripCoordinates, arcTime]
  rw [heq] at hd
  exact hd.unique (((hasDerivAt_id s).add_const 1).div_const 2 |>.prodMk
    (hasDerivAt_const s (0 : ℝ)))

theorem lowerStripCoordinates_vertical_derivative {h : ℝ} (hh : h ≠ 0) (s : ℝ) :
    fderiv ℝ (lowerStripCoordinates h) (s, 0) (0, 1) =
      (cornerSign ((s + 1) / 2) * (1 / (4 * h * cornerScale ((s + 1) / 2))),
        1 / (4 * h * cornerScale ((s + 1) / 2))) := by
  have hf : DifferentiableAt ℝ (lowerStripCoordinates h) (s, 0) :=
    (contDiff_lowerStripCoordinates hh).contDiffAt.differentiableAt (by simp)
  have hd := StripCoordinates.hasDerivAt_verticalSlice hf
  have hdiv : HasDerivAt (fun u : ℝ => u / (4 * h * cornerScale ((s + 1) / 2)))
      (1 / (4 * h * cornerScale ((s + 1) / 2))) 0 := (hasDerivAt_id 0).div_const _
  have hfirst := (HasDerivAt.const_mul (cornerSign ((s + 1) / 2)) hdiv).const_add ((s + 1) / 2)
  exact hd.unique (hfirst.prodMk hdiv)

/-- The actual lower edge-coordinate derivative is injective, including at both corners. -/
theorem injective_fderiv_lowerStripCoordinates {h : ℝ} (hh : h ≠ 0) (s : ℝ) :
    Injective (fderiv ℝ (lowerStripCoordinates h) (s, 0)) := by
  let L := fderiv ℝ (lowerStripCoordinates h) (s, 0)
  have hhor : ((2 : ℝ) • L) (1, 0) = (1, 0) := by
    change (2 : ℝ) • (fderiv ℝ (lowerStripCoordinates h) (s, 0) (1, 0)) = (1, 0)
    rw [lowerStripCoordinates_horizontal_derivative hh]
    norm_num
  have hnorm : (((2 : ℝ) • L) (0, 1)).2 ≠ 0 := by
    change ((2 : ℝ) • (fderiv ℝ (lowerStripCoordinates h) (s, 0) (0, 1))).2 ≠ 0
    rw [lowerStripCoordinates_vertical_derivative hh]
    change (2 : ℝ) * (1 / (4 * h * cornerScale ((s + 1) / 2))) ≠ 0
    exact mul_ne_zero (by norm_num) (one_div_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) hh) (cornerScale_pos _).ne'))
  have hi := StripCoordinates.injective_plane_of_horizontal_and_normal ((2 : ℝ) • L) hhor hnorm
  intro x y hxy
  exact hi (congrArg (fun z : ℝ × ℝ => (2 : ℝ) • z) hxy)

theorem injective_fderiv_exchangeEdges (h : ℝ) (p : ℝ × ℝ) :
    Injective (fderiv ℝ (exchangeEdges h) p) := by
  have heq : exchangeEdges h ∘ exchangeEdges h = id := funext (exchangeEdges_involutive h)
  have hd : (fderiv ℝ (exchangeEdges h) (exchangeEdges h p)).comp
      (fderiv ℝ (exchangeEdges h) p) = ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
    rw [← fderiv_comp p ((contDiff_exchangeEdges h).contDiffAt.differentiableAt (by simp))
      ((contDiff_exchangeEdges h).contDiffAt.differentiableAt (by simp)), heq, fderiv_id]
  intro x y hxy
  have he := congrArg (fderiv ℝ (exchangeEdges h) (exchangeEdges h p)) hxy
  change ((fderiv ℝ (exchangeEdges h) (exchangeEdges h p)).comp
    (fderiv ℝ (exchangeEdges h) p)) x =
      ((fderiv ℝ (exchangeEdges h) (exchangeEdges h p)).comp
        (fderiv ℝ (exchangeEdges h) p)) y at he
  rw [hd] at he
  exact he

/-- The upper edge-coordinate derivative is injective along its entire parabolic edge. -/
theorem injective_fderiv_upperStripCoordinates {h : ℝ} (hh : h ≠ 0) (s : ℝ) :
    Injective (fderiv ℝ (upperStripCoordinates h) (s, h * (1 - s ^ 2))) := by
  rw [upperStripCoordinates, fderiv_comp _
    ((contDiff_lowerStripCoordinates hh).contDiffAt.differentiableAt (by simp))
    ((contDiff_exchangeEdges h).contDiffAt.differentiableAt (by simp))]
  have heq : exchangeEdges h (s, h * (1 - s ^ 2)) = (s, 0) := by
    simp only [exchangeEdges, sub_self]
  rw [heq]
  exact (injective_fderiv_lowerStripCoordinates hh s).comp (injective_fderiv_exchangeEdges h _)

end Wikipedia.SmoothSixDPoincare.WhitneyPairModel
