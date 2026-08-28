import Wikipedia.NoExoticSixSphere.FourAnnulusOverlapCoordinates
import Wikipedia.NoExoticSixSphere.IntLinearAutomorphism
import Wikipedia.HopfProblem.SphereHomologyTop

/-!
# Unit coefficients of the original annulus boundary difference

The original outer-minus-inner class marks every puncture coordinate by
an isomorphism from third sphere homology. Comparing with the retained
chart's sphere model gives an automorphism of the integers. Its coefficient
is therefore one or minus one, independently of the input homology class.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.GenericFourAnnulus.ParityBallSystem

open GLOrthonormalization AnnulusDoublePoints
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology
open Wikipedia.HopfProblem.SphereHomology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {g : Vector 4 → M} (P : ParityBallSystem g) [Fintype (singularSet g)]

def componentSphereBoundaryDifferenceEquiv (x : singularSet g) :
    SingularHomology (Sphere 3) 3 ≃ₗ[ℤ] SingularHomology (Sphere 3) 3 :=
  (P.componentBoundaryDifferenceEquiv x 3 (by decide)).trans
    (homotopyEquivHomologyEquiv (P.pieceSphereEquiv x) 3)

def boundaryIntegerEquiv (x : singularSet g) : ℤ ≃ₗ[ℤ] ℤ :=
  (unitSphereHomologyTopEquiv 2).symm.trans
    ((P.componentSphereBoundaryDifferenceEquiv x).trans (unitSphereHomologyTopEquiv 2))

def boundaryCoefficient (x : singularSet g) : ℤ := P.boundaryIntegerEquiv x 1

theorem boundaryCoefficient_eq_one_or_neg_one (x : singularSet g) :
    P.boundaryCoefficient x = 1 ∨ P.boundaryCoefficient x = -1 :=
  IntLinearAutomorphism.apply_one_eq_one_or_neg_one (P.boundaryIntegerEquiv x)

theorem componentSphereBoundaryDifferenceEquiv_marked (x : singularSet g)
    (a : SingularHomology (Sphere 3) 3) :
    P.componentSphereBoundaryDifferenceEquiv x a = P.boundaryCoefficient x • a := by
  apply (unitSphereHomologyTopEquiv 2).injective
  rw [map_zsmul]
  have h := IntLinearAutomorphism.apply_eq_mul (P.boundaryIntegerEquiv x)
    (unitSphereHomologyTopEquiv 2 a)
  simpa only [boundaryCoefficient, boundaryIntegerEquiv, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, smul_eq_mul] using h

theorem componentBoundaryDifferenceEquiv_marked (x : singularSet g)
    (a : SingularHomology (Sphere 3) 3) :
    P.componentBoundaryDifferenceEquiv x 3 (by decide) a =
      P.boundaryCoefficient x • singularHomologyMap (P.pieceSphereEquiv x).symm.toFun 3 a := by
  have h := congrArg (homotopyEquivHomologyEquiv (P.pieceSphereEquiv x) 3).symm
    (P.componentSphereBoundaryDifferenceEquiv_marked x a)
  simpa only [componentSphereBoundaryDifferenceEquiv, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, map_zsmul, homotopyEquivHomologyEquiv_symm_apply] using h

end NoExoticSixSphere.GenericFourAnnulus.ParityBallSystem
