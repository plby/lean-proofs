import Wikipedia.NoExoticSixSphere.JamesSphereFiniteFiberQuotient
import Wikipedia.NoExoticSixSphere.JamesSphereSecondStageHomotopyRange
import Wikipedia.NoExoticSixSphere.JamesSphereFiberQuotientMap
import Wikipedia.NoExoticSixSphere.HomotopyFiberTargetComparison

/-!
# The original finite-to-full inclusion-fiber map

The source sphere and its pole are unchanged. The original second-stage
inclusion postcomposes the actual fiber paths. Its proved native maps
in two consecutive degrees give bijectivity of this fiber map through
degree `3n - 3`.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.JamesSphere.FiniteFiberQuotient

def toFull (n : ℕ) : C(Fiber n (spherePole n), FiberQuotient.Fiber n) :=
  HomotopyFiberTargetMap.map (SecondStageCone.attaching n) (SecondStage.wordInclusion n)
    (spherePole n)

theorem toFull_basepoint (n : ℕ) :
    toFull n (basepoint n (spherePole n)) = FiberQuotient.basepoint n := rfl

def toFullHom (n d : ℕ) [NeZero d] :=
  HigherHomotopy.mapMonoidHom (N := Fin d) (toFull n) (toFull_basepoint n)

theorem toFullHom_bijective (n d : ℕ) [NeZero d] (hn : 2 ≤ n) (hdn : d ≤ 3 * n - 3) :
    Function.Bijective (toFullHom n d) := by
  change Function.Bijective (HomotopyFiberTargetMap.hom (SecondStageCone.attaching n)
    (SecondStage.wordInclusion n) (spherePole n) d)
  apply HomotopyFiberTargetMap.hom_bijective
  · exact (SecondStage.wordInclusion_pi_bijective n hn d
      (Nat.pos_of_ne_zero (NeZero.ne d)) (by omega)
        (SecondStageCone.attaching n (spherePole n))).injective
  · exact SecondStage.wordInclusion_pi_bijective n hn (d + 1) (by omega) (by omega)
      (SecondStageCone.attaching n (spherePole n))

end NoExoticSixSphere.JamesSphere.FiniteFiberQuotient
