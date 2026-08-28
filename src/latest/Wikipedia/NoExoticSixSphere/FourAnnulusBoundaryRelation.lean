import Wikipedia.NoExoticSixSphere.FourAnnulusBoundaryCoefficients
import Wikipedia.NoExoticSixSphere.FourAnnulusPuncturedBallHomotopy

/-!
# The signed homology relation retaining both original annulus boundaries

The actual outer sphere minus the actual inner sphere is a sum of the
original linking spheres with unit integral coefficients. Native
Mayer--Vietoris exactness supplies the overlap lift; the actual one-point
comparisons mark its coordinates; and the original retraction places
the resulting relation in the same punctured annulus.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.GenericFourAnnulus.ParityBallSystem

open GLOrthonormalization AnnulusDoublePoints
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {g : Vector 4 → M} (P : ParityBallSystem g) [Fintype (singularSet g)]

def complementModelSphere (x : singularSet g) : C(Sphere 3, SingularComplement g) :=
  (P.puncturedPieceInclusion x).comp (P.pieceSphereEquiv x).symm.toFun

omit [Fintype (singularSet g)] in
theorem complementModelSphere_eq_smallLink (x : singularSet g) :
    P.complementModelSphere x = (P.ball x).annulusComplementSmallLink := by
  apply ContinuousMap.ext
  intro q
  rfl

omit [Fintype (singularSet g)] in
theorem complementModelSphere_homologyMap (x : singularSet g) (n : ℕ) :
    singularHomologyMap (P.complementModelSphere x) n =
      singularHomologyMap (P.complementLink x) n := by
  have he : (P.ball x).annulusComplementLink = P.complementLink x :=
    ContinuousMap.ext (fun _ ↦ rfl)
  rw [P.complementModelSphere_eq_smallLink, (P.ball x).annulusComplementSmallLink_homologyMap, he]

theorem boundaryDifference_eq_sum_modelSpheres (a : SingularHomology (Sphere 3) 3) :
    P.boundaryDifference 3 a =
      ∑ x, P.boundaryCoefficient x • singularHomologyMap (P.complementModelSphere x) 3 a := by
  obtain ⟨b, hb⟩ := P.exists_boundaryDifference_lift 3 a
  have hcoords (x : singularSet g) : P.overlapHomologyEquiv 3 b x =
      P.boundaryCoefficient x • singularHomologyMap (P.pieceSphereEquiv x).symm.toFun 3 a := by
    rw [← P.componentBoundaryDifferenceEquiv_of_lift x 3 (by decide) a b hb,
      P.componentBoundaryDifferenceEquiv_marked]
  have h := P.overlapHomologyEquiv_inclusion 3 b
  rw [hb] at h
  simp_rw [hcoords, map_zsmul] at h
  simpa only [complementModelSphere, singularHomologyMap_comp, LinearMap.comp_apply] using h

theorem boundaryDifference_eq_sum_complementLinks (a : SingularHomology (Sphere 3) 3) :
    P.boundaryDifference 3 a =
      ∑ x, P.boundaryCoefficient x • singularHomologyMap (P.complementLink x) 3 a := by
  rw [P.boundaryDifference_eq_sum_modelSpheres]
  simp_rw [P.complementModelSphere_homologyMap]

theorem outer_sub_inner_eq_sum_linkingSpheres (a : SingularHomology (Sphere 3) 3) :
    singularHomologyMap P.outerBoundary 3 a - singularHomologyMap P.innerBoundary 3 a =
      ∑ x, P.boundaryCoefficient x • singularHomologyMap (P.linkingSphere x) 3 a := by
  apply P.inclusionComplement_homology_injective 3
  rw [map_sub, map_sum]
  simp only [map_zsmul]
  simpa only [boundaryDifference, complementOuterBoundary, complementInnerBoundary, complementLink,
    singularHomologyMap_comp, LinearMap.comp_apply] using
      P.boundaryDifference_eq_sum_complementLinks a

theorem exists_signed_boundary_relation : ∃ ε : singularSet g → ℤ,
    (∀ x, ε x = 1 ∨ ε x = -1) ∧
      ∀ a : SingularHomology (Sphere 3) 3,
        singularHomologyMap P.outerBoundary 3 a - singularHomologyMap P.innerBoundary 3 a =
          ∑ x, ε x • singularHomologyMap (P.linkingSphere x) 3 a :=
  ⟨P.boundaryCoefficient, P.boundaryCoefficient_eq_one_or_neg_one,
    P.outer_sub_inner_eq_sum_linkingSpheres⟩

end NoExoticSixSphere.GenericFourAnnulus.ParityBallSystem
