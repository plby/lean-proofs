import Wikipedia.HopfProblem.RiemannSphereMobiusClosedDisc
import Wikipedia.HopfProblem.RiemannSphereMobiusInverse

/-!
# Analytic formulas for the closed-disc normalization and its inverse

The natural-topology closed-disc homeomorphism agrees with explicit
complex rational functions in both directions. These formulas are analytic
on neighborhoods of every point of the corresponding closed sets, so in
particular they preserve analyticity on their interiors.
-/

noncomputable section

open Set
open scoped ContDiff

namespace Wikipedia.HopfProblem.RiemannSphere

open MobiusCircle

variable {a b c : ℂ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
variable (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)

/-- The inverse homeomorphism has the ordinary rational inverse formula. -/
@[simp] theorem closedDiscHalfPlaneHomeomorph_symm_apply
    (w : closedOrientedHalfPlane (orientation a b c)) :
    ((closedDiscHalfPlaneHomeomorph hab hac hbc ha hb hc).symm w : ℂ) =
      inverseCrossRatio a b c w := by
  let e := closedDiscHalfPlaneHomeomorph hab hac hbc ha hb hc
  have he : crossRatio a b c ((e.symm w : closedDiscWithoutPole c) : ℂ) = (w : ℂ) := by
    rw [← closedDiscHalfPlaneHomeomorph_apply hab hac hbc ha hb hc (e.symm w)]
    exact congrArg Subtype.val (e.apply_symm_apply w)
  rw [← he, inverseCrossRatio_crossRatio hab.symm hbc hac (e.symm w).property.2]

include hab in
theorem crossRatio_analyticOnNhd_closedDiscWithoutPole :
    AnalyticOnNhd ℂ (crossRatio a b c) (closedDiscWithoutPole c) := by
  intro z hz
  exact crossRatio_analyticAt hab.symm hz.2

include hab hac hbc ha hb hc in
theorem inverseCrossRatio_analyticOnNhd_closedOrientedHalfPlane :
    AnalyticOnNhd ℂ (inverseCrossRatio a b c)
      (closedOrientedHalfPlane (orientation a b c)) :=
  inverseCrossRatio_analyticOnNhd_closedHalfPlane ha hb hc hab.symm hbc hac

/-- The inverse takes precisely the strict half-plane to the open disc. -/
theorem closedDiscHalfPlaneHomeomorph_symm_strict_iff
    (w : closedOrientedHalfPlane (orientation a b c)) :
    ‖((closedDiscHalfPlaneHomeomorph hab hac hbc ha hb hc).symm w : ℂ)‖ < 1 ↔
      0 < orientation a b c * (w : ℂ).im := by
  have h := closedDiscHalfPlaneHomeomorph_strict_iff hab hac hbc ha hb hc
    ((closedDiscHalfPlaneHomeomorph hab hac hbc ha hb hc).symm w)
  simpa only [Homeomorph.apply_symm_apply] using h.symm

/-- The inverse takes precisely the real boundary to the remaining circle. -/
theorem closedDiscHalfPlaneHomeomorph_symm_boundary_iff
    (w : closedOrientedHalfPlane (orientation a b c)) :
    ‖((closedDiscHalfPlaneHomeomorph hab hac hbc ha hb hc).symm w : ℂ)‖ = 1 ↔
      (w : ℂ).im = 0 := by
  have h := closedDiscHalfPlaneHomeomorph_im_eq_zero_iff hab hac hbc ha hb hc
    ((closedDiscHalfPlaneHomeomorph hab hac hbc ha hb hc).symm w)
  simpa only [Homeomorph.apply_symm_apply] using h.symm

end Wikipedia.HopfProblem.RiemannSphere
