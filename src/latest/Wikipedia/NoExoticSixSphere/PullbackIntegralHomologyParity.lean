import Wikipedia.NoExoticSixSphere.IntegralSpherePinchNaturality
import Wikipedia.NoExoticSixSphere.GeometricQuadraticSpherePinch
import Wikipedia.NoExoticSixSphere.GeometricIntersectionAlternating
import Wikipedia.NoExoticSixSphere.GeometricIntersectionAdditivity
import Wikipedia.NoExoticSixSphere.GeometricSphereParityNullhomotopy

/-!
# Integral quadratic parity pulled back from a possibly disconnected manifold

The source of the specified continuous map is two-connected. The compact
framed six-dimensional target need not be connected. Source Hurewicz
representatives and actual postcomposed sphere maps define the parity and
pairing. The geometric pinch identities prove the quadratic identity and
invariance under adding twice any integral source class.
-/

noncomputable section

open Function ContinuousMap
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization SmoothCube SphereSumNeck
open Wikipedia.HopfProblem.SingularMayerVietoris

variable {M X : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] [CompactSpace M]
  [TopologicalSpace X] [SimplyConnectedSpace X]
  (e : EuclideanEmbedding 6 M)
  (ν : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) (r : TubularRetraction e)
  (i : C(X, M)) (x : X) [Subsingleton (π_ 2 X x)]

def pullbackIntegralParity (a : SingularHomology X 3) : ZMod 2 :=
  e.geometricSphereParity ν r (i.comp (integralClassRepresentative x a).val)

def pullbackIntegralIntersection (a b : SingularHomology X 3) : ZMod 2 :=
  e.sphereIntersectionNumber r (i.comp (integralClassRepresentative x a).val)
    (i.comp (integralClassRepresentative x b).val)

theorem pullbackIntegralParity_sphereClass (f : C(Sphere 3, X)) :
    e.pullbackIntegralParity ν r i x (integralSphereClass f) =
      e.geometricSphereParity ν r (i.comp f) := by
  apply e.geometricSphereParity_homotopic
  exact (Homotopic.refl i).comp
    ((integralSphereClass_eq_iff_homotopic x _ f).mp
      (integralSphereClass_representative x (integralSphereClass f)))

theorem pullbackIntegralIntersection_sphereClass (f g : C(Sphere 3, X)) :
    e.pullbackIntegralIntersection r i x (integralSphereClass f) (integralSphereClass g) =
      e.sphereIntersectionNumber r (i.comp f) (i.comp g) := by
  apply e.sphereIntersectionNumber_homotopic
  · exact (Homotopic.refl i).comp
      ((integralSphereClass_eq_iff_homotopic x _ f).mp
        (integralSphereClass_representative x (integralSphereClass f)))
  · exact (Homotopic.refl i).comp
      ((integralSphereClass_eq_iff_homotopic x _ g).mp
        (integralSphereClass_representative x (integralSphereClass g)))

include ν in
theorem pullbackIntegralIntersection_self (a : SingularHomology X 3) :
    e.pullbackIntegralIntersection r i x a a = 0 :=
  e.sphereIntersectionNumber_self ν r (i.comp (integralClassRepresentative x a).val)

theorem pullbackIntegralIntersection_add_right (a b c : SingularHomology X 3) :
    e.pullbackIntegralIntersection r i x a (b + c) =
      e.pullbackIntegralIntersection r i x a b + e.pullbackIntegralIntersection r i x a c := by
  obtain ⟨g, h, hbase, hg, hh⟩ := exists_common_pinch_representatives x b c
  let f := (integralClassRepresentative x a).val
  have hf : integralSphereClass f = a := integralSphereClass_representative x a
  have hp : integralSphereClass (SphereFold.pinch pinchPole g h hbase) = b + c := by
    rw [integralSphereClass_pinch, hg, hh]
  calc
    e.pullbackIntegralIntersection r i x a (b + c) =
        e.sphereIntersectionNumber r (i.comp f)
          (i.comp (SphereFold.pinch pinchPole g h hbase)) := by
      rw [← hf, ← hp, pullbackIntegralIntersection_sphereClass]
    _ = e.sphereIntersectionNumber r (i.comp f) (i.comp g) +
        e.sphereIntersectionNumber r (i.comp f) (i.comp h) := by
      rw [SphereFold.comp_pinch, sphereIntersectionNumber_pinch_add_right]
    _ = e.pullbackIntegralIntersection r i x a b +
        e.pullbackIntegralIntersection r i x a c := by
      rw [← pullbackIntegralIntersection_sphereClass e r i x f g,
        ← pullbackIntegralIntersection_sphereClass e r i x f h, hf, hg, hh]

theorem pullbackIntegralParity_zero : e.pullbackIntegralParity ν r i x 0 = 0 := by
  have h := e.pullbackIntegralParity_sphereClass ν r i x (ContinuousMap.const (Sphere 3) x)
  rw [integralSphereClass_const] at h
  exact h.trans (e.geometricSphereParity_const ν r (i x))

theorem pullbackIntegralParity_add (a b : SingularHomology X 3) :
    e.pullbackIntegralParity ν r i x (a + b) =
      e.pullbackIntegralParity ν r i x a + e.pullbackIntegralParity ν r i x b +
        e.pullbackIntegralIntersection r i x a b := by
  obtain ⟨f, g, hbase, hf, hg⟩ := exists_common_pinch_representatives x a b
  have hp : integralSphereClass (SphereFold.pinch pinchPole f g hbase) = a + b := by
    rw [integralSphereClass_pinch, hf, hg]
  calc
    e.pullbackIntegralParity ν r i x (a + b) =
        e.geometricSphereParity ν r (i.comp (SphereFold.pinch pinchPole f g hbase)) := by
      rw [← hp, pullbackIntegralParity_sphereClass]
    _ = e.geometricSphereParity ν r (i.comp f) + e.geometricSphereParity ν r (i.comp g) +
        e.sphereIntersectionNumber r (i.comp f) (i.comp g) := by
      rw [SphereFold.comp_pinch, geometricSphereParity_pinch]
    _ = e.pullbackIntegralParity ν r i x a + e.pullbackIntegralParity ν r i x b +
        e.pullbackIntegralIntersection r i x a b := by
      rw [← pullbackIntegralParity_sphereClass e ν r i x f,
        ← pullbackIntegralParity_sphereClass e ν r i x g,
        ← pullbackIntegralIntersection_sphereClass e r i x f g, hf, hg]

theorem pullbackIntegralParity_two_zsmul (a : SingularHomology X 3) :
    e.pullbackIntegralParity ν r i x ((2 : ℤ) • a) = 0 := by
  rw [two_zsmul, pullbackIntegralParity_add, pullbackIntegralIntersection_self e ν r i x,
    add_zero, ← two_mul, show (2 : ZMod 2) = 0 from by decide, zero_mul]

theorem pullbackIntegralParity_add_two_zsmul (a b : SingularHomology X 3) :
    e.pullbackIntegralParity ν r i x (a + (2 : ℤ) • b) =
      e.pullbackIntegralParity ν r i x a := by
  rw [pullbackIntegralParity_add, pullbackIntegralParity_two_zsmul, add_zero]
  have hB : e.pullbackIntegralIntersection r i x a ((2 : ℤ) • b) = 0 := by
    rw [two_zsmul, pullbackIntegralIntersection_add_right,
      ← two_mul, show (2 : ZMod 2) = 0 from by decide, zero_mul]
  rw [hB, add_zero]

theorem pullbackIntegralParity_neg (a : SingularHomology X 3) :
    e.pullbackIntegralParity ν r i x (-a) = e.pullbackIntegralParity ν r i x a := by
  have h := e.pullbackIntegralParity_add_two_zsmul ν r i x (-a) a
  have ha : -a + (2 : ℤ) • a = a := by simp [two_zsmul]
  rw [ha] at h
  exact h.symm

theorem pullbackIntegralParity_zsmul_zero (a : SingularHomology X 3)
    (ha : e.pullbackIntegralParity ν r i x a = 0) (k : ℤ) :
    e.pullbackIntegralParity ν r i x (k • a) = 0 := by
  have hk : k = k % 2 + 2 * (k / 2) := by omega
  conv_lhs => rw [hk, add_zsmul, mul_smul, pullbackIntegralParity_add_two_zsmul]
  have hmod : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases hmod with h | h
  · rw [h, zero_zsmul, pullbackIntegralParity_zero]
  · rwa [h, one_zsmul]

theorem pullbackIntegralParity_even_longitude (a b : SingularHomology X 3)
    (hb : e.pullbackIntegralParity ν r i x b = 0) (k : ℤ) :
    e.pullbackIntegralParity ν r i x ((2 : ℤ) • a + k • b) = 0 := by
  rw [add_comm, pullbackIntegralParity_add_two_zsmul]
  exact e.pullbackIntegralParity_zsmul_zero ν r i x b hb k

end NoExoticSixSphere.EuclideanEmbedding
