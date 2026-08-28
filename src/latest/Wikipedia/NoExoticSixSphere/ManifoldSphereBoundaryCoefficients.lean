import Wikipedia.NoExoticSixSphere.ManifoldSphereBoundaryComparison
import Wikipedia.NoExoticSixSphere.IntLinearAutomorphism
import Wikipedia.HopfProblem.SphereHomologyTop

/-!
# Unit coefficients of the actual connecting class

The actual component isomorphisms and the genuine local sphere models give
isomorphisms from fourth sphere homology to third sphere homology. Under the
proved integral sphere markings these are automorphisms of the integers.
Their coefficients are therefore one or minus one.
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

def componentSphereConnectingEquiv (i : BoundaryIndex g) (n : ℕ) (hn : n ≠ 0) :
    SingularHomology (Sphere 4) (n + 1) ≃ₗ[ℤ] SingularHomology (Sphere 3) n :=
  (P.componentConnectingEquiv i n hn).trans
    (homotopyEquivHomologyEquiv (P.pieceSphereEquiv i) n)

def boundaryIntegerEquiv (i : BoundaryIndex g) : ℤ ≃ₗ[ℤ] ℤ :=
  (unitSphereHomologyTopEquiv 3).symm.trans
    ((P.componentSphereConnectingEquiv i 3 (by decide)).trans (unitSphereHomologyTopEquiv 2))

def boundaryCoefficient (i : BoundaryIndex g) : ℤ := P.boundaryIntegerEquiv i 1

theorem boundaryCoefficient_eq_one_or_neg_one (i : BoundaryIndex g) :
    P.boundaryCoefficient i = 1 ∨ P.boundaryCoefficient i = -1 :=
  IntLinearAutomorphism.apply_one_eq_one_or_neg_one (P.boundaryIntegerEquiv i)

theorem componentSphereConnectingEquiv_marked (i : BoundaryIndex g)
    (a : SingularHomology (Sphere 4) 4) :
    P.componentSphereConnectingEquiv i 3 (by decide) a =
      P.boundaryCoefficient i •
        (unitSphereHomologyTopEquiv 2).symm (unitSphereHomologyTopEquiv 3 a) := by
  apply (unitSphereHomologyTopEquiv 2).injective
  rw [map_zsmul, LinearEquiv.apply_symm_apply]
  have h := IntLinearAutomorphism.apply_eq_mul (P.boundaryIntegerEquiv i)
    (unitSphereHomologyTopEquiv 3 a)
  simpa only [boundaryCoefficient, boundaryIntegerEquiv, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, smul_eq_mul] using h

theorem componentConnectingEquiv_marked (i : BoundaryIndex g)
    (a : SingularHomology (Sphere 4) 4) :
    P.componentConnectingEquiv i 3 (by decide) a =
      P.boundaryCoefficient i •
        singularHomologyMap (P.pieceSphereEquiv i).symm.toFun 3
          ((unitSphereHomologyTopEquiv 2).symm (unitSphereHomologyTopEquiv 3 a)) := by
  have h := congrArg (homotopyEquivHomologyEquiv (P.pieceSphereEquiv i) 3).symm
    (P.componentSphereConnectingEquiv_marked i a)
  simpa only [componentSphereConnectingEquiv, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, map_zsmul, homotopyEquivHomologyEquiv_symm_apply] using h

end NoExoticSixSphere.SphereFamily.ParityBallSystem
