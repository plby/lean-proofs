import Wikipedia.HopfProblem.DegreeCollapseRadialTraceBoundary
import Wikipedia.HopfProblem.SphereHomologyTop
import Wikipedia.NoExoticSixSphere.IntLinearAutomorphism

/-!
# The actual normal boundary map has integral coefficient one or minus one

Use the proved integral top-homology marking of the literal two-sphere.
An actual homology isomorphism, compared with the genuine native sphere
parametrization, becomes an automorphism of the integers. Its coefficient
is therefore a unit. No orientation or generator primitivity is assumed.
-/

noncomputable section

open Set Function Metric ContinuousMap
open scoped Topology ContDiff Manifold
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris PeriodTorusHigherHomology SphereHomology

local notation "P₃" => EuclideanSpace ℝ (Fin 3)
local notation "S₂" => Hemisphere.Sphere 2

theorem two_sphere_map_unit_of_homology_bijective {Y : Type} [TopologicalSpace Y]
    (e : S₂ ≃ₜ Y) (g : C(S₂, Y)) (hg : Bijective (singularHomologyMap g 2)) :
    ∃ k : ℤ, (k = 1 ∨ k = -1) ∧
      singularHomologyMap g 2 = k • singularHomologyMap (e : C(S₂, Y)) 2 := by
  let H := unitSphereHomologyTopEquiv 1
  let B := LinearEquiv.ofBijective (singularHomologyMap g 2) hg
  let J := homeomorphHomologyEquiv e 2
  let K : ℤ ≃ₗ[ℤ] ℤ := H.symm.trans (B.trans (J.symm.trans H))
  refine ⟨K 1, NoExoticSixSphere.IntLinearAutomorphism.apply_one_eq_one_or_neg_one K, ?_⟩
  apply LinearMap.ext
  intro a
  change B a = K 1 • J a
  apply J.symm.injective
  rw [map_zsmul, J.symm_apply_apply]
  apply H.injective
  rw [map_zsmul]
  have hh := NoExoticSixSphere.IntLinearAutomorphism.apply_eq_mul K (H a)
  simpa only [K, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, smul_eq_mul] using hh

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [Fact (Module.finrank ℝ F = 2 + 1)]

theorem normalized_boundary_map_unit {f : P₃ → F} {L : P₃ ≃L[ℝ] F} {s : Set P₃}
    (b : LocalDegree.BoundaryData f L s) :
    ∃ k : ℤ, (k = 1 ∨ k = -1) ∧
      singularHomologyMap b.normalizedMap 2 =
        k • singularHomologyMap ((SphereCoordinates.standardParametrization F 2).toHomeomorph :
          C(S₂, sphere (0 : F) 1)) 2 := by
  apply two_sphere_map_unit_of_homology_bijective
    (SphereCoordinates.standardParametrization F 2).toHomeomorph b.normalizedMap
  have heq : (b.normalizedHomologyEquiv 2 :
      SingularHomology S₂ 2 → SingularHomology (sphere (0 : F) 1) 2) =
      singularHomologyMap b.normalizedMap 2 :=
    funext (fun a => b.normalizedHomologyEquiv_apply 2 a)
  rw [← heq]
  exact (b.normalizedHomologyEquiv 2).bijective

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
