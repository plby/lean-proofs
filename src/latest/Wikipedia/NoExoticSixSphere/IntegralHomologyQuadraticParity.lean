import Wikipedia.NoExoticSixSphere.IntegralSphereHomotopyClass
import Wikipedia.NoExoticSixSphere.GeometricQuadraticSpherePinch
import Wikipedia.NoExoticSixSphere.GeometricIntersectionAlternating
import Wikipedia.NoExoticSixSphere.GeometricSphereParityNullhomotopy

/-!
# Geometric quadratic parity on actual integral middle homology

The native Hurewicz comparison makes the geometric parity independent of the
chosen sphere representative. Actual hemisphere pinches give its quadratic
identity with the already constructed integral intersection pairing. In
particular the parity vanishes on twice any integral class.
-/

noncomputable section

open Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization SmoothCube SphereSumNeck
open Wikipedia.HopfProblem.SingularMayerVietoris

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
  (e : EuclideanEmbedding 6 M)
  (ν : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) (r : TubularRetraction e)
  (m : M) [Subsingleton (π_ 2 M m)]

def integralHomologyParity (c : SingularHomology M 3) : ZMod 2 :=
  e.geometricSphereParity ν r (integralClassRepresentative m c).val

theorem integralHomologyParity_sphereClass (f : C(Sphere 3, M)) :
    e.integralHomologyParity ν r m (integralSphereClass f) =
      e.geometricSphereParity ν r f :=
  e.geometricSphereParity_homotopic ν r _ f
    ((integralSphereClass_eq_iff_homotopic m _ f).mp
      (integralSphereClass_representative m (integralSphereClass f)))

theorem integralHomologyParity_zero : e.integralHomologyParity ν r m 0 = 0 := by
  have h := e.integralHomologyParity_sphereClass ν r m (ContinuousMap.const (Sphere 3) m)
  rwa [integralSphereClass_const, geometricSphereParity_const] at h

theorem integralHomologyParity_add (a b : SingularHomology M 3) :
    e.integralHomologyParity ν r m (a + b) =
      e.integralHomologyParity ν r m a + e.integralHomologyParity ν r m b +
        e.integralHomologyIntersection r m a b := by
  let f := integralClassRepresentative m a
  let g := integralClassRepresentative m b
  let F := f.val.comp SphereThreeAntipodal.map
  let G := g.val.comp SphereThreeAntipodal.map
  have HF : f.val.Homotopic F :=
    (ContinuousMap.Homotopic.refl f.val).comp ⟨SphereThreeAntipodal.homotopy⟩
  have HG : g.val.Homotopic G :=
    (ContinuousMap.Homotopic.refl g.val).comp ⟨SphereThreeAntipodal.homotopy⟩
  have hF : integralSphereClass F = a :=
    (integralSphereClass_homotopic HF).symm.trans (integralSphereClass_representative m a)
  have hG : integralSphereClass G = b :=
    (integralSphereClass_homotopic HG).symm.trans (integralSphereClass_representative m b)
  have ha : SphereThreeAntipodal.map (antipode pinchPole) = spherePole 3 :=
    Subtype.ext (neg_neg _)
  have hbase : F (antipode pinchPole) = G (antipode pinchPole) := by
    change f.val (SphereThreeAntipodal.map (antipode pinchPole)) =
      g.val (SphereThreeAntipodal.map (antipode pinchPole))
    rw [ha, f.property, g.property]
  have hp : integralSphereClass (SphereFold.pinch pinchPole F G hbase) = a + b := by
    rw [integralSphereClass_pinch, hF, hG]
  calc
    e.integralHomologyParity ν r m (a + b) =
        e.geometricSphereParity ν r (SphereFold.pinch pinchPole F G hbase) := by
      rw [← hp, integralHomologyParity_sphereClass]
    _ = e.geometricSphereParity ν r F + e.geometricSphereParity ν r G +
        e.sphereIntersectionNumber r F G := e.geometricSphereParity_pinch ν r F G hbase
    _ = e.integralHomologyParity ν r m a + e.integralHomologyParity ν r m b +
        e.integralHomologyIntersection r m a b := by
      rw [← integralHomologyParity_sphereClass e ν r m F,
        ← integralHomologyParity_sphereClass e ν r m G,
        ← integralHomologyIntersection_integralSphereClass e r m F G, hF, hG]

theorem integralHomologyParity_two_zsmul (a : SingularHomology M 3) :
    e.integralHomologyParity ν r m ((2 : ℤ) • a) = 0 := by
  rw [two_zsmul, integralHomologyParity_add, integralHomologyIntersection_self e ν r m,
    add_zero, ← two_mul, show (2 : ZMod 2) = 0 from by decide, zero_mul]

theorem integralHomologyParity_add_two_zsmul (a b : SingularHomology M 3) :
    e.integralHomologyParity ν r m (a + (2 : ℤ) • b) =
      e.integralHomologyParity ν r m a := by
  rw [integralHomologyParity_add, integralHomologyParity_two_zsmul, add_zero]
  have hB : e.integralHomologyIntersection r m a ((2 : ℤ) • b) = 0 := by
    rw [two_zsmul, map_add, ← two_mul, show (2 : ZMod 2) = 0 from by decide, zero_mul]
  rw [hB, add_zero]

theorem integralHomologyParity_retraction_independent (r' : TubularRetraction e) :
    e.integralHomologyParity ν r m = e.integralHomologyParity ν r' m := by
  funext a
  exact e.geometricSphereParity_retraction_independent ν r r' _

theorem integralHomologyParity_basepoint_independent
    (m' : M) [Subsingleton (π_ 2 M m')] :
    e.integralHomologyParity ν r m = e.integralHomologyParity ν r m' := by
  funext a
  rw [← integralSphereClass_representative m a,
    integralHomologyParity_sphereClass, integralHomologyParity_sphereClass]

end NoExoticSixSphere.EuclideanEmbedding
