import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyTopDegree
import Wikipedia.HopfProblem.SpecialPeriodsTrianglePresentation

/-!
# Top homology of the entire actual triangle representation

The two actual triangle generators act trivially on fourth singular
homology of the coordinate four-torus.  They generate the triangle group.
Functoriality of the actual torus maps and actual singular homology maps
extends this identity to products and inverses, hence to every group
element.  In particular this includes either orientation of a meridian.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Homology

open SpecialPeriods SingularMayerVietoris PeriodTorusHigherHomology

private theorem dual_homology_one :
    singularHomologyMap (torusMatrixMap (triangleDualRepresentation 1 : LatticeMatrix)) 4 =
      LinearMap.id := by
  rw [map_one, Matrix.SpecialLinearGroup.coe_one, torusMatrixMap_one, singularHomologyMap_id]

private theorem dual_homology_mul (g h : TriangleGroup) :
    singularHomologyMap (torusMatrixMap (triangleDualRepresentation (g * h) : LatticeMatrix)) 4 =
      (singularHomologyMap (torusMatrixMap (triangleDualRepresentation g : LatticeMatrix)) 4).comp
        (singularHomologyMap
          (torusMatrixMap (triangleDualRepresentation h : LatticeMatrix)) 4) := by
  rw [map_mul, Matrix.SpecialLinearGroup.coe_mul, torusMatrixMap_mul, singularHomologyMap_comp]

/-- Every element of the actual dual triangle representation acts trivially on actual `H₄`. -/
theorem triangleDualRepresentation_homologyFour (g : TriangleGroup) :
    singularHomologyMap (torusMatrixMap (triangleDualRepresentation g : LatticeMatrix)) 4 =
      LinearMap.id := by
  have hg : g ∈ Subgroup.closure
      ({triangleGenerator₁, triangleGenerator₂} : Set TriangleGroup) := by
    rw [triangle_generators_generate]
    exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
      rcases Set.mem_insert_iff.mp hg with rfl | hg
      · rw [triangleDualRepresentation_generator₁_matrix]
        exact torusMatrixMap_A₁_homologyFour
      · have he : g = triangleGenerator₂ := Set.mem_singleton_iff.mp hg
        subst g
        rw [triangleDualRepresentation_generator₂_matrix]
        exact torusMatrixMap_A₂_homologyFour
  | one => exact dual_homology_one
  | mul g h _ _ ihg ihh =>
      rw [dual_homology_mul, ihg, ihh, LinearMap.id_comp]
  | inv g _ ihg =>
      have h := dual_homology_mul g⁻¹ g
      rw [inv_mul_cancel, dual_homology_one, ihg, LinearMap.comp_id] at h
      exact h.symm

/-- The representation identity holds on every actual fourth singular-homology class. -/
theorem triangleDualRepresentation_homologyFour_apply (g : TriangleGroup)
    (a : SingularHomology (ProductTorus 4) 4) :
    singularHomologyMap
      (torusMatrixMap (triangleDualRepresentation g : LatticeMatrix)) 4 a = a := by
  rw [triangleDualRepresentation_homologyFour, LinearMap.id_apply]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Homology
