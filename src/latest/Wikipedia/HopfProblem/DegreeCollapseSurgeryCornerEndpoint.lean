import Wikipedia.HopfProblem.DegreeCollapseCornerRetraction
import Wikipedia.NoExoticSixSphere.RoundedCornerZeroCoordinates

/-!
# The rounding deformation preserves the exact boundary difference coordinate

On the rounded boundary graph with sphere direction w and difference u,
the endpoint is (sqrt(r² + max(u,0)) w, min(u,0)). This is the original
piecewise flat boundary with the same direction and difference parameter.
The calculation is needed to compare actual native and flat end maps.
-/

noncomputable section

open Set Function Metric

namespace Wikipedia.HopfProblem.DegreeCollapse.CornerRetraction

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open NoExoticSixSphere.SmoothCornerRounding NoExoticSixSphere.RoundedHandleCorner

variable (χ : ContDiffBump (0 : ℝ)) {r : ℝ} (hr : 0 < r)

theorem shift_zeroPoint (r : ℝ) (p : Sphere 2 × ℝ) :
    shift r (zeroPoint χ r p) = -max (graphHeight χ p.2) (graphRadial χ p.2) := by
  rw [shift, norm_zeroPoint_fst, graphRadius_sq]
  change max 0 (min ((r ^ 2 - graphRadial χ p.2) - r ^ 2) (-graphHeight χ p.2)) = _
  rw [show (r ^ 2 - graphRadial χ p.2) - r ^ 2 = -graphRadial χ p.2 by ring]
  rcases le_total (graphHeight χ p.2) (graphRadial χ p.2) with h | h
  · rw [max_eq_right h, min_eq_left (neg_le_neg h),
      max_eq_right (neg_nonneg.mpr (graphRadial_nonpos χ p.2))]
  · rw [max_eq_left h, min_eq_right (neg_le_neg h),
      max_eq_right (neg_nonneg.mpr (graphHeight_nonpos χ p.2))]

theorem deform_zeroPoint_height (r : ℝ) (p : Sphere 2 × ℝ) :
    (deform r 1 (zeroPoint χ r p)).2 = min p.2 0 := by
  change graphHeight χ p.2 + 1 * shift r (zeroPoint χ r p) = _
  rw [one_mul, shift_zeroPoint]
  have hd : graphHeight χ p.2 - graphRadial χ p.2 = p.2 := graph_difference χ p.2
  rcases le_total p.2 0 with h | h
  · have hh : graphHeight χ p.2 ≤ graphRadial χ p.2 := by linarith
    rw [max_eq_right hh, min_eq_left h]
    linarith
  · have hh : graphRadial χ p.2 ≤ graphHeight χ p.2 := by linarith
    rw [max_eq_left hh, min_eq_right h]
    ring

include hr in
theorem norm_sq_deform_zeroPoint (p : Sphere 2 × ℝ) :
    ‖(deform r 1 (zeroPoint χ r p)).1‖ ^ 2 = r ^ 2 + max p.2 0 := by
  rw [norm_sq_deform hr (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1),
    norm_zeroPoint_fst, graphRadius_sq, one_mul, shift_zeroPoint]
  have hd : graphHeight χ p.2 - graphRadial χ p.2 = p.2 := graph_difference χ p.2
  rcases le_total p.2 0 with h | h
  · have hh : graphHeight χ p.2 ≤ graphRadial χ p.2 := by linarith
    rw [max_eq_right hh, max_eq_right h]
    ring
  · have hh : graphRadial χ p.2 ≤ graphHeight χ p.2 := by linarith
    rw [max_eq_left hh, max_eq_left h]
    linarith

include hr in
theorem deform_zeroPoint_vector (p : Sphere 2 × ℝ) :
    (deform r 1 (zeroPoint χ r p)).1 = Real.sqrt (r ^ 2 + max p.2 0) • p.1.val := by
  let c := Real.sqrt (1 - 1 * shift r (zeroPoint χ r p) /
    denominator r (zeroPoint χ r p).1) * graphRadius χ r p.2
  have hc : 0 ≤ c := mul_nonneg (Real.sqrt_nonneg _) (graphRadius_pos χ hr p.2).le
  have hv : (deform r 1 (zeroPoint χ r p)).1 = c • p.1.val := by
    change Real.sqrt (1 - 1 * shift r (zeroPoint χ r p) /
      denominator r (zeroPoint χ r p).1) • (graphRadius χ r p.2 • p.1.val) = _
    rw [smul_smul]
  have hs := norm_sq_deform_zeroPoint χ hr p
  rw [hv, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc,
    ClosedHemisphere.unit_norm, mul_one] at hs
  have hrad : 0 ≤ r ^ 2 + max p.2 0 := add_nonneg (sq_nonneg r) (le_max_right _ _)
  have he : c = Real.sqrt (r ^ 2 + max p.2 0) := by
    nlinarith [Real.sq_sqrt hrad, Real.sqrt_nonneg (r ^ 2 + max p.2 0)]
  rw [hv, he]

include hr in
theorem deform_zeroPoint_one (p : Sphere 2 × ℝ) :
    deform r 1 (zeroPoint χ r p) =
      (Real.sqrt (r ^ 2 + max p.2 0) • p.1.val, min p.2 0) := by
  apply Prod.ext
  · exact deform_zeroPoint_vector χ hr p
  · exact deform_zeroPoint_height χ r p

end Wikipedia.HopfProblem.DegreeCollapse.CornerRetraction
