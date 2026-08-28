import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryIntersectionComponents
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTranslations

/-!
# Actual affine fibre coordinates of boundary intersection columns

At a fixed boundary time the original fibre map may contain a constant
translation.  Its literal upper-slit coordinate is computed here using
the actual deck transformation between the two base lifts.  Only after
this pointwise identification is proved is translation invariance applied
to singular homology.  No assertion is made that a translation depending
on the entire boundary-circle parameter can be omitted from that map.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary

open SpecialPeriods SingularMayerVietoris PeriodTorusHigherHomology Homology

attribute [local instance] triangleTorusAction triangleTorusAction_continuous

variable {X : Type} [TopologicalSpace X]
  (D : Data ℂ TriangleRegularPoint) (b : SlitBaseLift)
  (C : C(X, familyIntersection D)) (i : Fin 3)
  (hC : ∀ x, C x ∈ intersectionPiece D i)
  (q : overlapBase (intersectionIndex i)) (z : TriangleRegularPoint)
  (g : TriangleGroup)
  (hz : z = g • upperLiftOnOverlap b (intersectionIndex i) q)

include hC hz

/-- The actual upper-chart coordinate moves the deck action from the
base lift to its inverse action on the complete original fibre map. -/
theorem componentFibreMap_eq_deck_comp (F : C(X, RealTorus₄))
    (hF : ∀ x, (C x).val = D.quotient (z, F x)) :
    componentFibreMap D b C i hC =
      (triangleTorusHomeomorph g⁻¹ : C(RealTorus₄, RealTorus₄)).comp F := by
  apply ContinuousMap.ext
  intro x
  rw [componentFibreMap_apply]
  have he : (⟨(C x).val, hC x⟩ : overlapFamily D (intersectionIndex i)) =
      (overlapChart D b (intersectionIndex i)).symm (q, g⁻¹ • F x) := by
    apply Subtype.ext
    rw [overlapChart_symm_coe, hF, hz]
    have h := D.quotient_smul g
      (upperLiftOnOverlap b (intersectionIndex i) q, g⁻¹ • F x)
    change D.quotient (g • upperLiftOnOverlap b (intersectionIndex i) q,
      g • (g⁻¹ • F x)) = D.quotient
        (upperLiftOnOverlap b (intersectionIndex i) q, g⁻¹ • F x) at h
    simpa only [smul_inv_smul] using h
  rw [he, Homeomorph.apply_symm_apply]
  rfl

/-- The singular-homology coefficient of the actual component map
therefore includes precisely this genuine deck action. -/
theorem componentFibreMap_homology_deck_comp (F : C(X, RealTorus₄))
    (hF : ∀ x, (C x).val = D.quotient (z, F x)) (n : ℕ) :
    singularHomologyMap (componentFibreMap D b C i hC) n =
      (singularHomologyMap
        (triangleTorusHomeomorph g⁻¹ : C(RealTorus₄, RealTorus₄)) n).comp
          (singularHomologyMap F n) := by
  rw [componentFibreMap_eq_deck_comp D b C i hC q z g hz F hF,
    singularHomologyMap_comp]

/-- A constant translation at this fixed boundary time contributes the
identity in all actual singular-homology degrees. -/
theorem componentFibreMap_homology_affine (F : C(X, RealTorus₄)) (v : RealTorus₄)
    (hF : ∀ x, (C x).val = D.quotient (z, F x + v)) (n : ℕ) :
    singularHomologyMap (componentFibreMap D b C i hC) n =
      (singularHomologyMap
        (triangleTorusHomeomorph g⁻¹ : C(RealTorus₄, RealTorus₄)) n).comp
          (singularHomologyMap F n) := by
  rw [componentFibreMap_homology_deck_comp D b C i hC q z g hz
    ((rightTranslation v).comp F) hF, singularHomologyMap_comp,
    rightTranslation_singularHomologyMap, LinearMap.id_comp]

/-- The exact three-component homology column for a geometrically
identified affine fibre map, with the genuine deck frame retained. -/
theorem intersectionHomology_component_affine (F : C(X, RealTorus₄)) (v : RealTorus₄)
    (hF : ∀ x, (C x).val = D.quotient (z, F x + v))
    (n : ℕ) (a : SingularHomology X n) :
    Homology.intersectionHomologyEquiv D b n (singularHomologyMap C n a) =
      componentCoordinates i
        (singularHomologyMap
          (triangleTorusHomeomorph g⁻¹ : C(RealTorus₄, RealTorus₄)) n
            (singularHomologyMap F n a)) := by
  rw [intersectionHomology_componentMap D b C i hC n a,
    componentFibreMap_homology_affine D b C i hC q z g hz F v hF n,
    LinearMap.comp_apply]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary
