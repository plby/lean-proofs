import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyIntersection
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyAlgebra
import Wikipedia.HopfProblem.SingularMayerVietoris

/-!
# The actual Mayer--Vietoris overlap map in torus coordinates

The first Mayer--Vietoris map uses the positive upper inclusion and the
negative lower inclusion. In the middle--left--right intersection marking
it is exactly the previously proved three-component overlap map, with the
two actual deck-induced torus homology maps as its coefficients.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Homology

open SpecialPeriods SingularMayerVietoris
open TrianglePeriodFamilyHomologyAlgebra

variable (D : Data ℂ TriangleRegularPoint) (b : SlitBaseLift)

/-- The actual first Mayer--Vietoris map is the signed three-overlap map in the markings. -/
theorem pairHomologyEquiv_leftHomologyMap (n : ℕ)
    (a : SingularHomology (familyIntersection D) n) :
    pairHomologyEquiv D b n
        (leftHomologyMap (upperFamily D : Set D.Space) (lowerFamily D) n a) =
      overlapMap
        (singularHomologyMap
          (triangleTorusHomeomorph (overlapTransition b 0) : C(RealTorus₄, RealTorus₄)) n)
        (singularHomologyMap
          (triangleTorusHomeomorph (overlapTransition b 2) : C(RealTorus₄, RealTorus₄)) n)
        (intersectionHomologyEquiv D b n a) := by
  refine (congrArg (pairHomologyEquiv D b n)
    (leftHomologyMap_apply (upperFamily D : Set D.Space) (lowerFamily D) n a)).trans ?_
  change
    (upperHomologyEquiv D b n (singularHomologyMap (intersectionToUpper D) n a),
      lowerHomologyEquiv D b n (-singularHomologyMap (intersectionToLower D) n a)) = _
  rw [map_neg, overlapMap_apply]
  apply Prod.ext
  · exact upperHomologyEquiv_intersection D b n a
  · exact congrArg Neg.neg (lowerHomologyEquiv_intersection D b n a)

/-- The marked Mayer--Vietoris square as an equality of actual integral linear maps. -/
theorem pairHomologyEquiv_leftHomologyMap_comp (n : ℕ) :
    (pairHomologyEquiv D b n).toLinearMap.comp
        (leftHomologyMap (upperFamily D : Set D.Space) (lowerFamily D) n) =
      (overlapMap
        (singularHomologyMap
          (triangleTorusHomeomorph (overlapTransition b 0) : C(RealTorus₄, RealTorus₄)) n)
        (singularHomologyMap
          (triangleTorusHomeomorph (overlapTransition b 2) : C(RealTorus₄, RealTorus₄)) n)).comp
        (intersectionHomologyEquiv D b n).toLinearMap := by
  apply LinearMap.ext
  intro a
  exact pairHomologyEquiv_leftHomologyMap D b n a

end Wikipedia.HopfProblem.TrianglePeriodFamily.Homology
