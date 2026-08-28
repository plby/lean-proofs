import Wikipedia.HopfProblem.CuspComplementCriticalAnnulusTransitions

/-!
# Separation of the two original pole discs

The normal radius is the already fixed radius of the actual closed
neighborhood. Its injectivity forces a strict gap between the lower
disc and the upper disc, with the unchanged correction-dependent
transition factor. No further shrinking or annular-cut assumption is
used.
-/

noncomputable section

open Set
open scoped OnePoint

namespace Wikipedia.HopfProblem.CuspComplement.CriticalAnnulus

open CuspCircleNormalTrivialization SpecialPeriods SpecialPeriods.Threefold

/-- The fixed closed normal radius strictly separates the two actual
pole discs on either nonfixed double curve. -/
theorem closedRadius_sq_lt_norm_kappa (b : Bool) :
    closedRadius ^ 2 < ‖kappa b‖ := by
  by_contra h
  have hk : ‖kappa b‖ ≤ closedRadius ^ 2 := le_of_not_gt h
  let z : ℂ := closedRadius
  have hz : z ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt closedRadius_pos)
  have hn : ‖z‖ = closedRadius := by
    simp only [z, Complex.norm_real, Real.norm_eq_abs, abs_of_pos closedRadius_pos]
  have hl : radiusSq (lowerNormal b z) ≤ closedRadius ^ 2 := by
    rw [radiusSq_lowerNormal, hn]
  have hw : ‖kappa b * z⁻¹‖ ≤ closedRadius := by
    rw [norm_mul, norm_inv, hn, ← div_eq_mul_inv]
    apply (div_le_iff₀ closedRadius_pos).mpr
    simpa only [pow_two] using hk
  have hu : radiusSq (upperNormal b (kappa b * z⁻¹)) ≤ closedRadius ^ 2 :=
    (radiusSq_upperNormal_le_iff b _).mpr hw
  have he :
      closedProductMap (((0 : ℂ) : RiemannSphere), ⟨lowerNormal b z, hl⟩) =
        closedProductMap ((∞ : RiemannSphere),
          ⟨upperNormal b (kappa b * z⁻¹), hu⟩) :=
    (closedProductMap_lowerNormal b z hl).trans
      (closedProductMap_upperNormal_finite b z hz hu).symm
  have hp := congrArg Prod.fst (closedProductMap_injective he)
  exact OnePoint.coe_ne_infty (0 : ℂ) hp

/-- The outer radius in the unchanged original affine curve parameter. -/
def outerRadius (b : Bool) : ℝ := ‖kappa b‖ / closedRadius

theorem outerRadius_pos (b : Bool) : 0 < outerRadius b :=
  div_pos (norm_pos_iff.mpr (kappa_ne_zero b)) closedRadius_pos

theorem closedRadius_lt_outerRadius (b : Bool) : closedRadius < outerRadius b := by
  apply (lt_div_iff₀ closedRadius_pos).mpr
  simpa only [pow_two] using closedRadius_sq_lt_norm_kappa b

/-- The upper pole disc inequality in the original finite parameter. -/
theorem upper_norm_lt_iff (b : Bool) (z : ℂ) (hz : z ≠ 0) :
    ‖kappa b * z⁻¹‖ < closedRadius ↔ outerRadius b < ‖z‖ := by
  rw [norm_mul, norm_inv, ← div_eq_mul_inv,
    div_lt_iff₀ (norm_pos_iff.mpr hz), outerRadius, div_lt_iff₀ closedRadius_pos]
  rw [mul_comm closedRadius ‖z‖]

/-- The corresponding non-strict inequality retains the true cut boundary. -/
theorem upper_norm_le_iff (b : Bool) (z : ℂ) (hz : z ≠ 0) :
    ‖kappa b * z⁻¹‖ ≤ closedRadius ↔ outerRadius b ≤ ‖z‖ := by
  rw [norm_mul, norm_inv, ← div_eq_mul_inv,
    div_le_iff₀ (norm_pos_iff.mpr hz), outerRadius, div_le_iff₀ closedRadius_pos]
  rw [mul_comm closedRadius ‖z‖]

/-- The upper radius level is exactly the outer boundary circle of the cut. -/
theorem upper_norm_eq_iff (b : Bool) (z : ℂ) (hz : z ≠ 0) :
    ‖kappa b * z⁻¹‖ = closedRadius ↔ ‖z‖ = outerRadius b := by
  rw [norm_mul, norm_inv, ← div_eq_mul_inv,
    div_eq_iff (ne_of_gt (norm_pos_iff.mpr hz)), outerRadius,
    eq_div_iff (ne_of_gt closedRadius_pos)]
  constructor <;> intro h <;> simpa only [mul_comm] using h.symm

end Wikipedia.HopfProblem.CuspComplement.CriticalAnnulus
