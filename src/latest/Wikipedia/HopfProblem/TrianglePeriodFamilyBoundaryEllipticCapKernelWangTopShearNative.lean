import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangTopShearReal
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangTransfer

/-!
# The native elliptic twist-circle shear in the top required Wang degree

The already constructed geometric shear is literally the real-torus
character shear. Its proved additivity discharges the character hypothesis.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang

open Elliptic SingularMayerVietoris PeriodTorusHigherHomology

/-- The native twist shear fixes every actual positive-circle cross class in degree four. -/
theorem nativeShear_positiveCircleCross_three (j : Kind) (a : SingularHomology RealTorus₄ 3) :
    singularHomologyMap (nativeShear j) 4 (positiveCircleCross RealTorus₄ 3 a) =
      positiveCircleCross RealTorus₄ 3 a := by
  rw [nativeShear_eq_realShear]
  exact BoundaryEllipticCapKernelWangShear.realShear_positiveCircleCross_three
    (twistCircleCharacter j) (twistCircleCharacter_add j) a

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang
