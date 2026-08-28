import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupHalfPlaneCore
import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupHalfPlaneReflection

/-!
# The two actual lifts of regular half-plane values

The inverse half-Ford normalization supplies one continuous lift. Its
composition with the actual circular reflection supplies another, whose
quotient value is the conjugate complex coordinate. Regularity of both
lifts is derived from their original uniformization values.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ComplexConjugate

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians

open SpecialPeriods SpecialPeriods.Triangle RiemannMapping RiemannSphere

/-- Reflecting the actual inverse-normalization lift conjugates its full
quotient uniformization value. -/
theorem circleReflection_halfPlaneLift_projection (w : RegularHalfPlane) :
    trianglePlaneUniformizationHomeomorph
        (triangleOrbitProjection (circleReflection (halfPlaneLift w : ℍ))) =
      conj (w.val : ℂ) := by
  rw [trianglePlaneUniformizationHomeomorph_circleReflection_normalization
    (halfPlaneLift_mem_halfFordRegion w)]
  exact congrArg (fun v : closedOrientedHalfPlane normalizationOrientation => conj (v : ℂ))
    (halfFordNormalizationHomeomorph.apply_symm_apply w.val)

theorem circleReflection_halfPlaneLift_mem_regular (w : RegularHalfPlane) :
    circleReflection (halfPlaneLift w : ℍ) ∈ triangleRegularLocus := by
  apply (triangleRegularLocus_iff_planeUniformization _).mpr
  rw [circleReflection_halfPlaneLift_projection]
  exact (halfPlaneConjugateValue w).property

/-- The actual circular reflection of the inverse-normalization lift. -/
def reflectedHalfPlaneLift (w : RegularHalfPlane) : TriangleRegularPoint :=
  ⟨circleReflection (halfPlaneLift w : ℍ), circleReflection_halfPlaneLift_mem_regular w⟩

@[simp] theorem reflectedHalfPlaneLift_coe (w : RegularHalfPlane) :
    (reflectedHalfPlaneLift w : ℍ) = circleReflection (halfPlaneLift w : ℍ) := rfl

theorem reflectedHalfPlaneLift_continuous : Continuous reflectedHalfPlaneLift :=
  (circleReflection.continuous.comp
    (continuous_subtype_val.comp halfPlaneLift_continuous)).subtype_mk _

/-- The second lift projects through the actual regular quotient to the
complex conjugate value in the canonical twice-punctured plane. -/
@[simp] theorem reflectedHalfPlaneLift_projection (w : RegularHalfPlane) :
    triangleRegularPlaneHomeomorph (triangleRegularProject (reflectedHalfPlaneLift w)) =
      halfPlaneConjugateValue w := by
  apply Subtype.ext
  exact circleReflection_halfPlaneLift_projection w

@[simp] theorem reflectedHalfPlaneLift_real_coe
    (x : ℝ) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    (reflectedHalfPlaneLift (realHalfPlaneValue x hx0 hx1) : ℍ) =
      circleReflection (halfFordRealPreimage x : ℍ) := rfl

end Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians
