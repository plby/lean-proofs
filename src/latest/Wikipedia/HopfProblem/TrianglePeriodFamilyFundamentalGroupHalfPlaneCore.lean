import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupHomeomorph
import Wikipedia.HopfProblem.TriangleRiemannNormalization
import Wikipedia.HopfProblem.TrianglePeriodFamilyMeridiansBoundaryNormalizationCore

/-!
# Actual regular lifts from the normalized closed half-plane

Delete the two marked finite values from the already constructed closed
half-plane. The inverse of the actual half-Ford normalization then gives
a continuous lift into the original regular upper-half-plane locus.
Regularity follows from the established full quotient uniformization.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ComplexConjugate

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians

open SpecialPeriods SpecialPeriods.Triangle RiemannMapping RiemannSphere

/-- The normalized closed half-plane with its two finite marked values removed. -/
abbrev RegularHalfPlane : Type :=
  {w : closedOrientedHalfPlane normalizationOrientation // (w : ℂ) ≠ 0 ∧ (w : ℂ) ≠ 1}

/-- The literal value in the canonical twice-punctured plane. -/
def halfPlaneValue (w : RegularHalfPlane) : TwicePuncturedPlane :=
  ⟨(w.val : ℂ), w.property⟩

@[simp] theorem halfPlaneValue_coe (w : RegularHalfPlane) :
    (halfPlaneValue w : ℂ) = (w.val : ℂ) := rfl

theorem halfPlaneValue_continuous : Continuous halfPlaneValue :=
  (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- Complex conjugation of the literal value still avoids the two real punctures. -/
def halfPlaneConjugateValue (w : RegularHalfPlane) : TwicePuncturedPlane := by
  refine ⟨conj (w.val : ℂ), ?_, ?_⟩
  · intro h
    apply w.property.1
    simpa using congrArg conj h
  · intro h
    apply w.property.2
    simpa using congrArg conj h

@[simp] theorem halfPlaneConjugateValue_coe (w : RegularHalfPlane) :
    (halfPlaneConjugateValue w : ℂ) = conj (w.val : ℂ) := rfl

theorem halfPlaneConjugateValue_continuous : Continuous halfPlaneConjugateValue :=
  (Complex.continuous_conj.comp
    (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _

/-- The actual full quotient projection recovers every normalized half-plane value. -/
theorem halfFordNormalization_symm_projection
    (w : closedOrientedHalfPlane normalizationOrientation) :
    trianglePlaneUniformizationHomeomorph
        (triangleOrbitProjection (halfFordNormalizationHomeomorph.symm w : ℍ)) = (w : ℂ) := by
  rw [trianglePlaneUniformizationHomeomorph_projection
    (halfFordNormalizationHomeomorph.symm w).property,
    triangleSignedHalfPlaneMap_of_mem (halfFordNormalizationHomeomorph.symm w).property]
  exact congrArg (fun v : closedOrientedHalfPlane normalizationOrientation => (v : ℂ))
    (halfFordNormalizationHomeomorph.apply_symm_apply w)

/-- Avoiding the marked plane values is exactly membership in the original
regular upper-half-plane locus. -/
theorem triangleRegularLocus_iff_planeUniformization (z : ℍ) :
    z ∈ triangleRegularLocus ↔
      trianglePlaneUniformizationHomeomorph (triangleOrbitProjection z) ≠ 0 ∧
        trianglePlaneUniformizationHomeomorph (triangleOrbitProjection z) ≠ 1 := by
  rw [← triangleOrbitProjection_mem_regularDomain_iff,
    trianglePlaneUniformizationHomeomorph_regular_iff]
  rfl

theorem halfFordNormalization_symm_mem_regular (w : RegularHalfPlane) :
    (halfFordNormalizationHomeomorph.symm w.val : ℍ) ∈ triangleRegularLocus := by
  apply (triangleRegularLocus_iff_planeUniformization _).mpr
  rw [halfFordNormalization_symm_projection]
  exact w.property

/-- The actual inverse normalization, restricted only to regular values. -/
def halfPlaneLift (w : RegularHalfPlane) : TriangleRegularPoint :=
  ⟨(halfFordNormalizationHomeomorph.symm w.val : ℍ),
    halfFordNormalization_symm_mem_regular w⟩

@[simp] theorem halfPlaneLift_coe (w : RegularHalfPlane) :
    (halfPlaneLift w : ℍ) = (halfFordNormalizationHomeomorph.symm w.val : ℍ) := rfl

theorem halfPlaneLift_mem_halfFordRegion (w : RegularHalfPlane) :
    (halfPlaneLift w : ℍ) ∈ halfFordRegion :=
  (halfFordNormalizationHomeomorph.symm w.val).property

theorem halfPlaneLift_continuous : Continuous halfPlaneLift :=
  (continuous_subtype_val.comp
    (halfFordNormalizationHomeomorph.symm.continuous.comp continuous_subtype_val)).subtype_mk _

/-- The lift projects through the original regular quotient to the original value. -/
@[simp] theorem halfPlaneLift_projection (w : RegularHalfPlane) :
    triangleRegularPlaneHomeomorph (triangleRegularProject (halfPlaneLift w)) =
      halfPlaneValue w := by
  apply Subtype.ext
  exact halfFordNormalization_symm_projection w.val

/-- A real number different from the two marks, as an actual regular half-plane value. -/
def realHalfPlaneValue (x : ℝ) (hx0 : x ≠ 0) (hx1 : x ≠ 1) : RegularHalfPlane := by
  refine ⟨⟨(x : ℂ), by simp [closedOrientedHalfPlane]⟩, ?_, ?_⟩
  · change (x : ℂ) ≠ 0
    exact_mod_cast hx0
  · change (x : ℂ) ≠ 1
    exact_mod_cast hx1

@[simp] theorem realHalfPlaneValue_coe (x : ℝ) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    ((realHalfPlaneValue x hx0 hx1).val : ℂ) = (x : ℂ) := rfl

/-- At real values the lift is the previously fixed canonical boundary preimage. -/
@[simp] theorem halfPlaneLift_real_coe (x : ℝ) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    (halfPlaneLift (realHalfPlaneValue x hx0 hx1) : ℍ) =
      (halfFordRealPreimage x : ℍ) := rfl

end Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians
