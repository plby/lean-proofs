import Wikipedia.HopfProblem.CuspComplementCriticalAnnulusModel
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationStandardBoundaryProduct

/-!
# Literal markings of both annular ends on the fixed normal frontier

The lower and upper parameter-radius circles are marked in the already
constructed product boundary, over its original base points zero and
infinity.  Their normal vectors are the original lower and upper frames,
including conjugation, the upper sign, and the full complex deck factor.
The old boundary homeomorphism sends these exact marked points to the
original annulus map, pointwise in the unchanged threefold.

Both ends lie on the inner normal frontier.  The annulus's outer
parameter radius is not the outer cusp cap boundary.  No new boundary
atlas or reparametrization is introduced.
-/

noncomputable section

open Set Topology
open scoped OnePoint

namespace Wikipedia.HopfProblem.CuspComplement.CriticalAnnulus

open CuspCircleNormalTrivialization SpecialPeriods SpecialPeriods.Threefold

/-- An original affine parameter on the outer annular circle is nonzero. -/
theorem outerLevel_ne_zero (b : Bool) (z : ℂ) (hz : ‖z‖ = outerRadius b) : z ≠ 0 :=
  norm_pos_iff.mp (by rw [hz]; exact outerRadius_pos b)

/-- The lower marking has exactly the previously fixed normal radius. -/
theorem lowerBoundary_radiusSq (b : Bool) (z : ℂ) (hz : ‖z‖ = closedRadius) :
    radiusSq (lowerNormal b z) = closedRadius ^ 2 := by
  rw [radiusSq_lowerNormal, hz]

/-- The upper marking retains the complete complex transition factor;
its radius equality follows from the original outer cut. -/
theorem upperBoundary_radiusSq (b : Bool) (z : ℂ) (hz : ‖z‖ = outerRadius b) :
    radiusSq (upperNormal b (kappa b * z⁻¹)) = closedRadius ^ 2 := by
  rw [radiusSq_upperNormal,
    (upper_norm_eq_iff b z (outerLevel_ne_zero b z hz)).mpr hz]

/-- The lower boundary mark in the old product boundary, with its
literal original lower normal vector over base zero. -/
def lowerBoundaryMark (b : Bool) (z : ℂ) (hz : ‖z‖ = closedRadius) :
    Conifold.ProductBoundary closedRadius :=
  ⟨(((0 : ℂ) : RiemannSphere), lowerNormal b z), lowerBoundary_radiusSq b z hz⟩

/-- The upper boundary mark in the old product boundary.  The vector
is unchanged, including the upper sign, conjugation, and phase of `kappa`. -/
def upperBoundaryMark (b : Bool) (z : ℂ) (hz : ‖z‖ = outerRadius b) :
    Conifold.ProductBoundary closedRadius :=
  ⟨((∞ : RiemannSphere), upperNormal b (kappa b * z⁻¹)), upperBoundary_radiusSq b z hz⟩

@[simp] theorem lowerBoundaryMark_val (b : Bool) (z : ℂ) (hz : ‖z‖ = closedRadius) :
    (lowerBoundaryMark b z hz).val = (((0 : ℂ) : RiemannSphere), lowerNormal b z) := rfl

@[simp] theorem upperBoundaryMark_val (b : Bool) (z : ℂ) (hz : ‖z‖ = outerRadius b) :
    (upperBoundaryMark b z hz).val =
      ((∞ : RiemannSphere), upperNormal b (kappa b * z⁻¹)) := rfl

/-- The old frontier homeomorphism gives the original finite curve
point at every point of the lower radius circle. -/
theorem finite_eq_closedBoundaryHomeomorph_lower (b : Bool) (z : ℂ)
    (hz : ‖z‖ = closedRadius) :
    CuspGeometry.doubleCurveParametrization (curveIndex b) (z : RiemannSphere) =
      (closedBoundaryHomeomorph (lowerBoundaryMark b z hz) : Threefold.Space) := by
  rw [closedBoundaryHomeomorph_coe, ← closedProductMap_productBoundaryIntoClosedProduct]
  exact (closedProductMap_lowerNormal b z (lowerBoundary_radiusSq b z hz).le).symm

/-- The old frontier homeomorphism gives the original finite curve
point at the upper end, with the original correction-dependent transition. -/
theorem finite_eq_closedBoundaryHomeomorph_upper (b : Bool) (z : ℂ)
    (hz : ‖z‖ = outerRadius b) :
    CuspGeometry.doubleCurveParametrization (curveIndex b) (z : RiemannSphere) =
      (closedBoundaryHomeomorph (upperBoundaryMark b z hz) : Threefold.Space) := by
  rw [closedBoundaryHomeomorph_coe, ← closedProductMap_productBoundaryIntoClosedProduct]
  exact (closedProductMap_upperNormal_finite b z (outerLevel_ne_zero b z hz)
    (upperBoundary_radiusSq b z hz).le).symm

/-- The actual annulus map agrees pointwise with its lower mark under
the already established ambient frontier homeomorphism. -/
theorem annulusMap_eq_closedBoundaryHomeomorph_lower (b : Bool) (z : Annulus b)
    (hz : ‖z.val‖ = closedRadius) :
    annulusMap b z =
      (closedBoundaryHomeomorph (lowerBoundaryMark b z.val hz) : Threefold.Space) :=
  finite_eq_closedBoundaryHomeomorph_lower b z.val hz

/-- The actual annulus map agrees pointwise with its upper mark under
the same old frontier homeomorphism, without reparametrizing its circle. -/
theorem annulusMap_eq_closedBoundaryHomeomorph_upper (b : Bool) (z : Annulus b)
    (hz : ‖z.val‖ = outerRadius b) :
    annulusMap b z =
      (closedBoundaryHomeomorph (upperBoundaryMark b z.val hz) : Threefold.Space) :=
  finite_eq_closedBoundaryHomeomorph_upper b z.val hz

/-- The homeomorphism onto the actual remaining curve preserves the
same literal lower boundary marking. -/
theorem annulusHomeomorph_eq_closedBoundaryHomeomorph_lower (b : Bool) (z : Annulus b)
    (hz : ‖z.val‖ = closedRadius) :
    (annulusHomeomorph b z : Threefold.Space) =
      (closedBoundaryHomeomorph (lowerBoundaryMark b z.val hz) : Threefold.Space) := by
  rw [annulusHomeomorph_coe]
  exact annulusMap_eq_closedBoundaryHomeomorph_lower b z hz

/-- The homeomorphism onto the actual remaining curve preserves the
same literal upper boundary marking. -/
theorem annulusHomeomorph_eq_closedBoundaryHomeomorph_upper (b : Bool) (z : Annulus b)
    (hz : ‖z.val‖ = outerRadius b) :
    (annulusHomeomorph b z : Threefold.Space) =
      (closedBoundaryHomeomorph (upperBoundaryMark b z.val hz) : Threefold.Space) := by
  rw [annulusHomeomorph_coe]
  exact annulusMap_eq_closedBoundaryHomeomorph_upper b z hz

end Wikipedia.HopfProblem.CuspComplement.CriticalAnnulus
