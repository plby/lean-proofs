import Wikipedia.NoExoticSixSphere.ManifoldSphereBoundaryCoefficients

/-!
# A signed relation among the original boundary sphere maps

The actual connecting class gives a relation with unit coefficients among
the sphere model maps. Their genuine homotopies identify them with the
original boundary maps in the regular parameter space. Injectivity of the
punctured-cylinder inclusion on homology then gives the relation in that
cylinder itself. It holds for every third homology class of the three-sphere.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereFamily.ParityBallSystem

open GLOrthonormalization
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology
open Wikipedia.HopfProblem.SphereHomology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  {g : ℝ → Sphere 3 → M} (P : ParityBallSystem g) [Fintype (BoundaryIndex g)]

theorem sum_modelSphere_boundaryCoefficient_zero (a : SingularHomology (Sphere 3) 3) :
    ∑ i, P.boundaryCoefficient i • singularHomologyMap (P.regularModelSphere i) 3 a = 0 := by
  have h := P.sum_componentConnectingEquiv_inclusion_zero 3 (by decide)
    ((unitSphereHomologyTopEquiv 3).symm (unitSphereHomologyTopEquiv 2 a))
  simp_rw [P.componentConnectingEquiv_marked, LinearEquiv.apply_symm_apply,
    LinearEquiv.symm_apply_apply, map_zsmul] at h
  have hh := congrArg
    (singularHomologyMap
      (sphereRegularHomeomorph g : C(sphereRegularSet g, RegularParameters g)) 3) h
  simp only [map_sum, map_zero, map_zsmul] at hh
  simpa only [regularModelSphere, singularHomologyMap_comp, LinearMap.comp_apply] using hh

theorem sum_regularSphere_boundaryCoefficient_zero (a : SingularHomology (Sphere 3) 3) :
    ∑ i, P.boundaryCoefficient i • singularHomologyMap (P.regularSphereInclusion i) 3 a = 0 := by
  simp_rw [← P.regularModelSphere_homologyMap]
  exact P.sum_modelSphere_boundaryCoefficient_zero a

theorem sum_sphere_boundaryCoefficient_zero (a : SingularHomology (Sphere 3) 3) :
    ∑ i, P.boundaryCoefficient i • singularHomologyMap (P.sphereInclusion i) 3 a = 0 := by
  apply P.inclusionRegular_homology_injective 3
  rw [map_sum, map_zero]
  simp only [map_zsmul]
  simpa only [regularSphereInclusion, singularHomologyMap_comp, LinearMap.comp_apply] using
    P.sum_regularSphere_boundaryCoefficient_zero a

/-- The signed sum of the actual induced boundary maps is zero as a linear map. -/
theorem sum_sphere_boundaryCoefficient_map_zero :
    ∑ i, P.boundaryCoefficient i • singularHomologyMap (P.sphereInclusion i) 3 = 0 := by
  apply LinearMap.ext
  intro a
  let evaluation :
      (SingularHomology (Sphere 3) 3 →ₗ[ℤ] SingularHomology P.puncturedCylinder 3) →+
        SingularHomology P.puncturedCylinder 3 :=
    { toFun := fun f ↦ f a
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  change evaluation (∑ i, P.boundaryCoefficient i •
    singularHomologyMap (P.sphereInclusion i) 3) = 0
  rw [map_sum]
  simp only [map_zsmul]
  exact P.sum_sphere_boundaryCoefficient_zero a

/-- Every actual boundary component occurs, with coefficient one or minus one. -/
theorem exists_signed_sphere_relation : ∃ ε : BoundaryIndex g → ℤ,
    (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ a : SingularHomology (Sphere 3) 3,
        ∑ i, ε i • singularHomologyMap (P.sphereInclusion i) 3 a = 0 :=
  ⟨P.boundaryCoefficient, P.boundaryCoefficient_eq_one_or_neg_one,
    P.sum_sphere_boundaryCoefficient_zero⟩

end NoExoticSixSphere.SphereFamily.ParityBallSystem
