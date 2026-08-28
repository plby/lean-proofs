import Wikipedia.NoExoticSixSphere.SpherePinchFiniteFormula

/-!
# The actual axial dilation rescales the finite pinch coordinate

The formulas are checked at every finite chart point. The two scalar
identities retain all nonzero denominator conditions, supplied by positive
scale and the actual squared norm. No limiting argument is used here.
-/

noncomputable section

open Set Function Topology

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

theorem axis_finite_head {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) :
    (axisDenominator c ((1 + r)⁻¹ * (1 - r)))⁻¹ *
      axisNumerator c ((1 + r)⁻¹ * (1 - r)) =
    (1 + (c⁻¹) ^ 2 * r)⁻¹ * (1 - (c⁻¹) ^ 2 * r) := by
  have h1 : 1 + r ≠ 0 := by positivity
  have h2 : r + c ^ 2 ≠ 0 := by positivity
  have h3 : c ^ 2 + r ≠ 0 := by positivity
  rw [axisDenominator_finite c r hr, axisNumerator_finite c r hr]
  field_simp
  ring

theorem axis_finite_tail {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) (z : ℝ) :
    (axisDenominator c ((1 + r)⁻¹ * (1 - r)))⁻¹ *
      ((2 * c) * ((1 + r)⁻¹ * (2 * z))) =
    (1 + (c⁻¹) ^ 2 * r)⁻¹ * (2 * (c⁻¹ * z)) := by
  have h1 : 1 + r ≠ 0 := by positivity
  have h2 : r + c ^ 2 ≠ 0 := by positivity
  have h3 : c ^ 2 + r ≠ 0 := by positivity
  rw [axisDenominator_finite c r hr]
  field_simp
  ring

theorem axisDilation_finite {c : ℝ} (hc : 0 < c) (v : Vector 3) :
    axisDilation c (pinchFiniteChart v) = pinchFiniteChart (c⁻¹ • v) := by
  have hn : ‖c⁻¹ • v‖ ^ 2 = (c⁻¹) ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  apply Subtype.ext
  rw [axisDilation_val hc]
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · change (axisDenominator c ((pinchFiniteChart v).val 0))⁻¹ *
      axisNumerator c ((pinchFiniteChart v).val 0) = (pinchFiniteChart (c⁻¹ • v)).val 0
    rw [pinchFiniteChart_head, pinchFiniteChart_head, hn]
    exact axis_finite_head hc (sq_nonneg ‖v‖)
  · change (axisDenominator c ((pinchFiniteChart v).val 0))⁻¹ *
      ((2 * c) * (pinchFiniteChart v).val j.succ) = (pinchFiniteChart (c⁻¹ • v)).val j.succ
    rw [pinchFiniteChart_head, pinchFiniteChart_succ, pinchFiniteChart_succ, hn]
    exact axis_finite_tail hc (sq_nonneg ‖v‖) (v j)

theorem axisDilation_scaledChart {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (v : Vector 3) :
    axisDilation (ε / δ) (pinchScaledChart ε hε.ne' v) = pinchScaledChart δ hδ.ne' v := by
  change axisDilation (ε / δ) (pinchFiniteChart (ε • v)) = pinchFiniteChart (δ • v)
  rw [axisDilation_finite (div_pos hε hδ)]
  congr 1
  rw [smul_smul]
  congr 1
  field_simp

end NoExoticSixSphere.SphereSumNeck
