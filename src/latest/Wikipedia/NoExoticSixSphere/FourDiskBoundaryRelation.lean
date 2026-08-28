import Wikipedia.NoExoticSixSphere.FourDiskBoundaryCoefficients

/-!
# The signed homology relation for the original punctured-disk boundary

The actual outer sphere is the sum of the actual linking spheres with
unit integral coefficients. The local model-to-link annuli and the
literal retraction put the relation in the original punctured disk,
not merely in a replacement space or in assigned coordinate groups.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.GenericFourDisk.ParityBallSystem

open GLOrthonormalization DiskDoublePoints
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {g : Vector 4 → M} (P : ParityBallSystem g) [Fintype (singularSet g)]

def complementModelSphere (x : singularSet g) : C(Sphere 3, SingularComplement g) :=
  (P.puncturedPieceInclusion x).comp (P.pieceSphereEquiv x).symm.toFun

omit [Fintype (singularSet g)] in
theorem complementModelSphere_eq_smallLink (x : singularSet g) :
    P.complementModelSphere x = (P.ball x).complementSmallLink := by
  apply ContinuousMap.ext
  intro s
  rfl

omit [Fintype (singularSet g)] in
theorem complementModelSphere_homologyMap (x : singularSet g) (n : ℕ) :
    singularHomologyMap (P.complementModelSphere x) n =
      singularHomologyMap (P.complementLink x) n := by
  rw [P.complementModelSphere_eq_smallLink]
  exact (P.ball x).complementSmallLink_homologyMap n

theorem outer_eq_sum_modelSpheres (a : SingularHomology (Sphere 3) 3) :
    singularHomologyMap P.complementOuterBoundary 3 a =
      ∑ x, P.boundaryCoefficient x • singularHomologyMap (P.complementModelSphere x) 3 a := by
  have h := P.sum_complementCoordinates 3 (by decide)
    (singularHomologyMap P.complementOuterBoundary 3 a)
  simp_rw [← P.componentOuterEquiv_apply, P.componentOuterEquiv_marked, map_zsmul] at h
  simpa only [complementModelSphere, singularHomologyMap_comp, LinearMap.comp_apply] using h

theorem outer_eq_sum_complementLinks (a : SingularHomology (Sphere 3) 3) :
    singularHomologyMap P.complementOuterBoundary 3 a =
      ∑ x, P.boundaryCoefficient x • singularHomologyMap (P.complementLink x) 3 a := by
  rw [P.outer_eq_sum_modelSpheres]
  simp_rw [P.complementModelSphere_homologyMap]

theorem outer_eq_sum_linkingSpheres (a : SingularHomology (Sphere 3) 3) :
    singularHomologyMap P.outerBoundary 3 a =
      ∑ x, P.boundaryCoefficient x • singularHomologyMap (P.linkingSphere x) 3 a := by
  apply P.inclusionComplement_homology_injective 3
  rw [map_sum]
  simp only [map_zsmul]
  simpa only [complementOuterBoundary, complementLink,
    singularHomologyMap_comp, LinearMap.comp_apply] using P.outer_eq_sum_complementLinks a

theorem exists_signed_boundary_relation : ∃ ε : singularSet g → ℤ,
    (∀ x, ε x = 1 ∨ ε x = -1) ∧
      ∀ a : SingularHomology (Sphere 3) 3,
        singularHomologyMap P.outerBoundary 3 a =
          ∑ x, ε x • singularHomologyMap (P.linkingSphere x) 3 a :=
  ⟨P.boundaryCoefficient, P.boundaryCoefficient_eq_one_or_neg_one, P.outer_eq_sum_linkingSpheres⟩

end NoExoticSixSphere.GenericFourDisk.ParityBallSystem
