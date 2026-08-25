import StackExchange.Puzzling139335.ThreeCorners.Rays
import StackExchange.Puzzling139335.ThreeCorners.NormalUniqueness

/-!
# Identifying the original normals with the ordered angular frame

Choosing the counterclockwise ordering of the inward rays changes at most
the ordering of the two outward normals of a supporting right corner.
-/

open Set

namespace Puzzling139335.ThreeCorners

noncomputable section

/-- Reorder the support frame using its positively oriented inward rays. -/
def angularSupportCorner {P : Set Plane} {a : Plane} (h : SupportCorner P a)
    {θ : ℝ} (hθ : h.bisector = outwardBisector θ) : SupportCorner P a where
  mem := h.mem
  firstNormal := -ray θ
  secondNormal := -perpRay θ
  norm_firstNormal := by simp only [norm_neg, norm_ray]
  norm_secondNormal := by simp only [norm_neg, norm_perpRay]
  orthogonal := by simp only [inner_neg_left, inner_neg_right, neg_neg, ray_inner_perpRay]
  first_support := by
    intro x hx
    have hcoord := (subset_supportCone_of_bisector h hθ hx).1
    simpa only [inner_neg_left] using neg_nonpos.mpr hcoord
  second_support := by
    intro x hx
    have hcoord := (subset_supportCone_of_bisector h hθ hx).2
    simpa only [inner_neg_left] using neg_nonpos.mpr hcoord

@[simp] theorem angularSupportCorner_bisector {P : Set Plane} {a : Plane}
    (h : SupportCorner P a) {θ : ℝ} (hθ : h.bisector = outwardBisector θ) :
    (angularSupportCorner h hθ).bisector = outwardBisector θ := by
  simp [angularSupportCorner, SupportCorner.bisector, outwardBisector, add_comm]

/-- The original two outward normals are exactly the negatives of the
ordered inward rays, in one of their two possible orders. -/
theorem normals_eq_neg_rays_or_swap {P : Set Plane} {a : Plane}
    (h : SupportCorner P a) {θ : ℝ} (hθ : h.bisector = outwardBisector θ) :
    (h.firstNormal = -ray θ ∧ h.secondNormal = -perpRay θ) ∨
      (h.firstNormal = -perpRay θ ∧ h.secondNormal = -ray θ) := by
  have hbis : h.bisector = (angularSupportCorner h hθ).bisector := by
    rw [angularSupportCorner_bisector, hθ]
  have hn := normals_eq_or_swap_of_bisector_eq h (angularSupportCorner h hθ) hbis
  change (-ray θ = h.firstNormal ∧ -perpRay θ = h.secondNormal) ∨
    (-ray θ = h.secondNormal ∧ -perpRay θ = h.firstNormal) at hn
  rcases hn with ⟨hfirst, hsecond⟩ | ⟨hsecond, hfirst⟩
  · exact Or.inl ⟨hfirst.symm, hsecond.symm⟩
  · exact Or.inr ⟨hfirst.symm, hsecond.symm⟩

end

end Puzzling139335.ThreeCorners
