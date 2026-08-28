import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologySourceSequence
import Wikipedia.HopfProblem.MappingTorusHomology
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleMayerVietorisNaturality

/-!
# Actual Wang-to-regular-family connecting comparison

A genuine continuous map from a mapping torus, carrying its two arc opens
into the two actual family slits, gives a comparison of the actual singular
Mayer--Vietoris connecting homomorphisms. In the proved markings its source
is the antidiagonal of the signed Wang boundary. The comparison matrix is
defined by the literal map of actual intersections, not supplied as an
assumed homology or monodromy matrix.

Later geometric applications must prove the displayed cover-preservation
conditions and evaluate this actual intersection map.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary

open SpecialPeriods SingularMayerVietoris Homology
open MappingTorus.HomologyCover

variable {X : Type} [TopologicalSpace X]
  (D : Data ℂ TriangleRegularPoint) (φ : X ≃ₜ X)
  (F : C(MappingTorus.Torus φ, D.Space))
  (hU : Set.MapsTo F (U φ) (upperFamily D))
  (hV : Set.MapsTo F (V φ) (lowerFamily D))

/-- The literal restriction of the boundary map to the actual two-cover intersections. -/
def intersectionMap :
    C((U φ ∩ V φ : Set (MappingTorus.Torus φ)), familyIntersection D) :=
  intersectionRestriction F (U φ) (V φ) (upperFamily D) (lowerFamily D) hU hV

@[simp] theorem intersectionMap_apply
    (x : (U φ ∩ V φ : Set (MappingTorus.Torus φ))) :
    (intersectionMap D φ F hU hV x).val = F x.val := rfl

/-- Naturality of the actual connecting maps, retaining the genuine family marking. -/
theorem markedConnecting_naturality (b : SlitBaseLift) (n : ℕ)
    (a : SingularHomology (MappingTorus.Torus φ) (n + 1)) :
    familyMarkedConnecting D b n (singularHomologyMap F (n + 1) a) =
      Homology.intersectionHomologyEquiv D b n
        (singularHomologyMap (intersectionMap D φ F hU hV) n
          (MappingTorusHomology.mayerVietorisConnecting φ n a)) := by
  have h := connectingHomomorphism_naturality_apply F (U φ) (V φ)
    (upperFamily D) (lowerFamily D) hU hV (U_open φ) (V_open φ) (cover φ)
    (upperFamily D).isOpen (lowerFamily D).isOpen (upperFamily_union_lowerFamily D) n a
  exact (congrArg (Homology.intersectionHomologyEquiv D b n) h).symm

/-- The actual map of intersections in two source and three target component coordinates. -/
def intersectionComparison (b : SlitBaseLift) (n : ℕ) :
    (SingularHomology X n × SingularHomology X n) →ₗ[ℤ]
      (SingularHomology RealTorus₄ n ×
        (SingularHomology RealTorus₄ n × SingularHomology RealTorus₄ n)) :=
  (Homology.intersectionHomologyEquiv D b n).toLinearMap.comp
    ((singularHomologyMap (intersectionMap D φ F hU hV) n).comp
      (MappingTorusHomology.intersectionHomologyEquiv φ n).symm.toLinearMap)

@[simp] theorem intersectionComparison_apply (b : SlitBaseLift) (n : ℕ)
    (a : SingularHomology X n × SingularHomology X n) :
    intersectionComparison D φ F hU hV b n a =
      Homology.intersectionHomologyEquiv D b n
        (singularHomologyMap (intersectionMap D φ F hU hV) n
          ((MappingTorusHomology.intersectionHomologyEquiv φ n).symm a)) := rfl

/-- The source actual connecting class is the inverse marking of its signed Wang pair. -/
theorem mappingTorusConnecting_eq_marked_boundary (n : ℕ)
    (a : SingularHomology (MappingTorus.Torus φ) (n + 1)) :
    MappingTorusHomology.mayerVietorisConnecting φ n a =
      (MappingTorusHomology.intersectionHomologyEquiv φ n).symm
        (-MappingTorusHomology.wangBoundary φ n a, MappingTorusHomology.wangBoundary φ n a) := by
  apply (MappingTorusHomology.intersectionHomologyEquiv φ n).injective
  rw [LinearEquiv.apply_symm_apply]
  exact MappingTorusHomology.boundaryCoordinates_eq_antidiagonal φ n a

/-- The actual regular-family connecting map is obtained from the actual Wang boundary. -/
theorem markedConnecting_wangBoundary (b : SlitBaseLift) (n : ℕ)
    (a : SingularHomology (MappingTorus.Torus φ) (n + 1)) :
    familyMarkedConnecting D b n (singularHomologyMap F (n + 1) a) =
      intersectionComparison D φ F hU hV b n
        (-MappingTorusHomology.wangBoundary φ n a, MappingTorusHomology.wangBoundary φ n a) := by
  refine (markedConnecting_naturality D φ F hU hV b n a).trans ?_
  exact congrArg
    (fun z => Homology.intersectionHomologyEquiv D b n
      (singularHomologyMap (intersectionMap D φ F hU hV) n z))
    (mappingTorusConnecting_eq_marked_boundary φ n a)

/-- Applying the already proved meridian orientation change gives the literal
source-kernel boundary coordinates of the actual inclusion map. -/
theorem sourceKernelProjection_wangBoundary (n : ℕ)
    (a : SingularHomology (MappingTorus.Torus φ) (n + 1)) :
    (sourceKernelProjection D n (singularHomologyMap F (n + 1) a) :
      SingularHomology RealTorus₄ n × SingularHomology RealTorus₄ n) =
      normalizedSourceDomainEquiv n
        (intersectionComparison D φ F hU hV normalizedSlitBaseLift n
          (-MappingTorusHomology.wangBoundary φ n a,
            MappingTorusHomology.wangBoundary φ n a)).2 := by
  exact congrArg
    (fun z : SingularHomology RealTorus₄ n ×
      (SingularHomology RealTorus₄ n × SingularHomology RealTorus₄ n) =>
        normalizedSourceDomainEquiv n z.2)
    (markedConnecting_wangBoundary D φ F hU hV normalizedSlitBaseLift n a)

/-- The comparison on a boundary pair is the difference of its two actual columns. -/
theorem intersectionComparison_antidiagonal (b : SlitBaseLift) (n : ℕ)
    (a : SingularHomology X n) :
    intersectionComparison D φ F hU hV b n (-a, a) =
      -intersectionComparison D φ F hU hV b n (a, 0) +
        intersectionComparison D φ F hU hV b n (0, a) := by
  have h : (-a, a) = -(a, (0 : SingularHomology X n)) + (0, a) := by
    ext <;> simp
  rw [h, map_add, map_neg]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary
