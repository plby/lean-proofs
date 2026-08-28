import Wikipedia.NoExoticSixSphere.JamesSphereEHPMetastable
import Wikipedia.NoExoticSixSphere.JamesSphereCellBoundaryLift

/-!
# The EHP connecting map on the actual second-cell boundary lift

The finite quotient homomorphism followed by its original sphere
homeomorphism gives a concrete input to suspension. The full EHP
connecting map sends that suspension to the exact finite-fiber
projection. For the characteristic-disk lift this is the original
attaching map. Identifying the quotient class with a standard generator
is not assumed or claimed here.
-/

noncomputable section

open scoped Topology unitInterval
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.JamesSphere.FiniteFiberQuotient

def sphereHom (n d : ℕ) [NeZero d] :=
  (HigherHomotopy.mapMonoidHom (N := Fin (d + 1))
    (SecondStage.quotientHomeomorph n : C(SecondStage.QuotientSpace n, Sphere (n + n)))
      (FirstStageQuotient.secondQuotient_pole n)).comp (hom n (spherePole n) d)

theorem projection_toFullHom (n d : ℕ) [NeZero d]
    (c : π_ d (Fiber n (spherePole n)) (basepoint n (spherePole n))) :
    FiberQuotient.projectionHom n d (toFullHom n d c) =
      HigherHomotopy.map (N := Fin d)
        (HomotopyFiber.projection (SecondStageCone.attaching n)
          (SecondStageCone.attaching n (spherePole n)))
        (HomotopyFiber.projection_basepoint (SecondStageCone.attaching n) (spherePole n)) c := by
  refine Quotient.inductionOn c fun p ↦ ?_
  rfl

theorem sphereEquiv_toFullHom (n d : ℕ) [NeZero d] (hn : 2 ≤ n) (hdn : d + 3 ≤ 3 * n)
    (c : π_ d (Fiber n (spherePole n)) (basepoint n (spherePole n))) :
    EHP.fiberSphereEquiv n d hn hdn (FiberQuotient.hom_bijective_range n d hn hdn)
      (toFullHom n d c) = CubicalSphereSuspension.hom (d + 1) (n + n) (sphereHom n d c) := by
  change FirstStageQuotient.sphereHopfHom n hn (d + 1)
    (FiberQuotient.hom n d (toFullHom n d c)) = _
  rw [hom_toFull]
  have hf := congrFun (FirstStageQuotient.stageMap_native_factor n (d + 1))
    (hom n (spherePole n) d c)
  change HigherHomotopy.map (N := Fin (d + 1)) (FirstStageQuotient.bottomSphere n)
    (FirstStageQuotient.bottomSphere_pole n) (sphereHom n d c) =
      HigherHomotopy.map (N := Fin (d + 1)) (FirstStageQuotient.stageMap n)
        (FirstStageQuotient.stageMap_basepoint n) (hom n (spherePole n) d c) at hf
  rw [← hf]
  exact FirstStageQuotient.sphereHopfHom_bottomSphere n hn (d + 1) (sphereHom n d c)

theorem connecting_sphereHom (n d : ℕ) [NeZero d] (hn : 2 ≤ n) (hdn : d + 3 ≤ 3 * n)
    (c : π_ d (Fiber n (spherePole n)) (basepoint n (spherePole n))) :
    EHP.connectingHomMetastable n d hn hdn
      (CubicalSphereSuspension.hom (d + 1) (n + n) (sphereHom n d c)) =
      HigherHomotopy.map (N := Fin d)
        (HomotopyFiber.projection (SecondStageCone.attaching n)
          (SecondStageCone.attaching n (spherePole n)))
        (HomotopyFiber.projection_basepoint (SecondStageCone.attaching n) (spherePole n)) c := by
  rw [← sphereEquiv_toFullHom n d hn hdn]
  exact (EHP.connectingHom_fiberSphereEquiv n d hn hdn
    (FiberQuotient.hom_bijective_range n d hn hdn) (toFullHom n d c)).trans
      (projection_toFullHom n d c)

end NoExoticSixSphere.JamesSphere.FiniteFiberQuotient

namespace NoExoticSixSphere.JamesSphere.CellBoundary

def quotientHom (n : ℕ) (hn : 0 < n) (d : ℕ) [NeZero d] :=
  (FiniteFiberQuotient.sphereHom n d).comp (liftHom n hn d)

theorem connecting_quotientHom (n d : ℕ) [NeZero d] (hn : 2 ≤ n) (hdn : d + 3 ≤ 3 * n)
    (c : π_ d (Boundary n) (corner n (by omega))) :
    EHP.connectingHomMetastable n d hn hdn
      (CubicalSphereSuspension.hom (d + 1) (n + n) (quotientHom n (by omega) d c)) =
        HigherHomotopy.map (N := Fin d) (attaching n) (attaching_corner n (by omega)) c := by
  exact (FiniteFiberQuotient.connecting_sphereHom n d hn hdn (liftHom n (by omega) d c)).trans
    (projection_liftHom n (by omega) d c)

end NoExoticSixSphere.JamesSphere.CellBoundary
