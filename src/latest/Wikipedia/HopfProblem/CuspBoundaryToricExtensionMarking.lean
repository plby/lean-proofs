import Wikipedia.HopfProblem.CuspBoundaryToricExtensionBoundary
import Wikipedia.HopfProblem.CuspBoundaryToricExtensionMarkingFibre
import Wikipedia.HopfProblem.CuspBoundaryGammaZeroWangNaturality
import Wikipedia.HopfProblem.MappingTorusHomologyCovering
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusSpaces

/-!
# Positive Wang marking of the literal swept cusp torus

The actual boundary map is the degree-one circle-product covering of
the identity mapping torus, followed by the actual equivariant inclusion.
The proved covering normalization and Wang naturality therefore compute
its signed boundary with coefficient `+1`.  In degree two, sweeping the
two positive fibre generators gives precisely the original third and
fourth first-homology coordinates.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.CuspBoundaryToricExtension

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology MappingTorusHomology
open TrianglePeriodFamily

/-- The degree-one covering has the actual signed circle boundary,
with no finite norm factor left over. -/
theorem identityProductMap_wang (n : ℕ)
    (a : SingularHomology (MappingTorus.Circle × ProductTorus 2) (n + 1)) :
    wangBoundary (Homeomorph.refl (ProductTorus 2)) n
        (singularHomologyMap identityProductMap (n + 1) a) =
      circleBoundary (ProductTorus 2) n a := by
  have h := Covering.wangBoundary_productCover_apply 1 (Homeomorph.refl (ProductTorus 2))
    identityMonodromy_period n a
  rw [Covering.homologyNorm_one, LinearMap.id_apply] at h
  change wangBoundary (Homeomorph.refl (ProductTorus 2)) n
    (singularHomologyMap identityProductMap (n + 1) a) = _ at h
  exact h

/-- The chosen actual product map sends a positive circle cross product
to a class with positive, unchanged Wang coordinate. -/
theorem identityProductMap_wang_positiveCircleCross (n : ℕ)
    (a : SingularHomology (ProductTorus 2) n) :
    wangBoundary (Homeomorph.refl (ProductTorus 2)) n
        (singularHomologyMap identityProductMap (n + 1)
          (positiveCircleCross (ProductTorus 2) n a)) = a := by
  rw [identityProductMap_wang, circleBoundary_positiveCircleCross]

/-- Naturality for the literal time-preserving inclusion of the two mapping tori. -/
theorem mappingTorusInclusion_wang (n : ℕ) (a : SingularHomology IdentityBoundary (n + 1)) :
    wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy n
        (singularHomologyMap mappingTorusInclusion (n + 1) a) =
      singularHomologyMap fibreMap n
        (wangBoundary (Homeomorph.refl (ProductTorus 2)) n a) :=
  CuspBoundaryGammaZero.wangBoundary_mappingTorusMap
    (Homeomorph.refl (ProductTorus 2)) ThreefoldOverlapMappingTorus.Cusp.monodromy
    fibreMap fibreMap_monodromy n a

/-- The actual boundary map preserves the signed circle boundary through
the original fibre inclusion. -/
theorem boundaryMap_wang (n : ℕ)
    (a : SingularHomology (MappingTorus.Circle × ProductTorus 2) (n + 1)) :
    wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy n
        (singularHomologyMap boundaryMap (n + 1) a) =
      singularHomologyMap fibreMap n (circleBoundary (ProductTorus 2) n a) := by
  rw [boundaryMap, singularHomologyMap_comp, LinearMap.comp_apply,
    mappingTorusInclusion_wang, identityProductMap_wang]

/-- The exact positive Wang normalization for every actual swept fibre class. -/
theorem boundaryMap_wang_positiveCircleCross (n : ℕ)
    (a : SingularHomology (ProductTorus 2) n) :
    wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy n
        (singularHomologyMap boundaryMap (n + 1)
          (positiveCircleCross (ProductTorus 2) n a)) =
      singularHomologyMap fibreMap n a := by
  rw [boundaryMap_wang, circleBoundary_positiveCircleCross]

/-- A literal native cusp-boundary class obtained by sweeping the given
fibre loop along the actual positive base circle. -/
def sweptToricClass (a : SingularHomology (ProductTorus 2) 1) :
    SingularHomology (ThreefoldOverlapMappingTorus.Boundary none) 2 :=
  singularHomologyMap boundaryMap 2 (positiveCircleCross (ProductTorus 2) 1 a)

/-- The same actual sweep as an integral linear homology map. -/
def sweptToricClassMap :
    SingularHomology (ProductTorus 2) 1 →ₗ[ℤ]
      SingularHomology (ThreefoldOverlapMappingTorus.Boundary none) 2 :=
  (singularHomologyMap boundaryMap 2).comp (positiveCircleCross (ProductTorus 2) 1)

@[simp] theorem sweptToricClassMap_apply (a : SingularHomology (ProductTorus 2) 1) :
    sweptToricClassMap a = sweptToricClass a := rfl

/-- Its actual signed Wang boundary is exactly the original included fibre class. -/
theorem sweptToricClass_wang (a : SingularHomology (ProductTorus 2) 1) :
    wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy 1 (sweptToricClass a) =
      singularHomologyMap fibreMap 1 a :=
  boundaryMap_wang_positiveCircleCross 1 a

theorem sweptToricClassMap_wang :
    (wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy 1).comp sweptToricClassMap =
      singularHomologyMap fibreMap 1 := by
  apply LinearMap.ext
  exact sweptToricClass_wang

/-- Both actual Mayer--Vietoris overlap coordinates retain the lower-first sign convention. -/
theorem sweptToricClass_boundaryCoordinates (a : SingularHomology (ProductTorus 2) 1) :
    boundaryCoordinates ThreefoldOverlapMappingTorus.Cusp.monodromy 1 (sweptToricClass a) =
      (-singularHomologyMap fibreMap 1 a, singularHomologyMap fibreMap 1 a) := by
  calc
    boundaryCoordinates ThreefoldOverlapMappingTorus.Cusp.monodromy 1 (sweptToricClass a) =
        (-wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy 1 (sweptToricClass a),
          wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy 1 (sweptToricClass a)) :=
      boundaryCoordinates_eq_antidiagonal ThreefoldOverlapMappingTorus.Cusp.monodromy 1 _
    _ = _ := Prod.ext (congrArg Neg.neg (sweptToricClass_wang a)) (sweptToricClass_wang a)

/-- The original first-homology marking of the actual swept class's Wang boundary. -/
theorem sweptToricClass_wang_coordinates (v : Fin 2 → ℤ) :
    FlatTorus.singularH1Equiv
        (wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy 1
          (sweptToricClass (loopHomologyClass (coordinatePeriodLoop 2 v)))) =
      ![0, 0, v 0, v 1] := by
  rw [sweptToricClass_wang, fibreMap_homologyOne_coordinates]

/-- The same marking as an equality of actual first-homology classes. -/
theorem sweptToricClass_wang_periodClass (v : Fin 2 → ℤ) :
    wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy 1
        (sweptToricClass (loopHomologyClass (coordinatePeriodLoop 2 v))) =
      FlatTorus.singularH1Equiv.symm ![0, 0, v 0, v 1] := by
  rw [sweptToricClass_wang, fibreMap_homologyOne_eq]

/-- Sweeping the first positive fibre generator gives coefficient one in position `2`. -/
theorem sweptToricClass_wang_basis_zero :
    wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy 1
        (sweptToricClass (loopHomologyClass (coordinatePeriodLoop 2 (Pi.single 0 1)))) =
      FlatTorus.singularH1Equiv.symm (Pi.single (2 : Fin 4) 1) := by
  rw [sweptToricClass_wang, fibreMap_homologyOne_basis_zero_eq]

/-- Sweeping the second positive fibre generator gives coefficient one in position `3`. -/
theorem sweptToricClass_wang_basis_one :
    wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy 1
        (sweptToricClass (loopHomologyClass (coordinatePeriodLoop 2 (Pi.single 1 1)))) =
      FlatTorus.singularH1Equiv.symm (Pi.single (3 : Fin 4) 1) := by
  rw [sweptToricClass_wang, fibreMap_homologyOne_basis_one_eq]

end Wikipedia.HopfProblem.CuspBoundaryToricExtension
