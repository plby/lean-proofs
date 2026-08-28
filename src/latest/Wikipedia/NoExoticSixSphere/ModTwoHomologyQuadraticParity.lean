import Wikipedia.NoExoticSixSphere.IntegralHomologyQuadraticParity
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# The geometric quadratic refinement on actual mod-two middle homology

The exact coefficient sequence identifies equal reductions with differences
twice an integral class. The proved integral parity is unchanged by such
differences, so its value descends to actual mod-two homology. Its companion
bilinear form is the original geometric intersection pairing, not a newly
assigned form. Evaluation on every continuous sphere map is retained.
-/

noncomputable section

open Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization SmoothCube
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.SphereHomologyCoefficients

attribute [local instance] modHomologyModule

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
  (e : EuclideanEmbedding 6 M)
  (ν : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) (r : TubularRetraction e)
  (m : M) [h₂ : Subsingleton (π_ 2 M m)]

theorem integralHomologyParity_eq_of_reduction_eq (a b : SingularHomology M 3)
    (hab : reductionHomologyMap 2 M 3 a = reductionHomologyMap 2 M 3 b) :
    e.integralHomologyParity ν r m a = e.integralHomologyParity ν r m b := by
  have hd : a - b ∈ scalarImage 2 (SingularHomology M 3) := by
    rw [scalarImage_eq_reduction_ker 2 (by decide) M 3]
    change reductionHomologyMap 2 M 3 (a - b) = 0
    rw [map_sub, hab, sub_self]
  obtain ⟨c, hc⟩ := hd
  change (2 : ℤ) • c = a - b at hc
  have he : a = b + (2 : ℤ) • c := by rw [hc]; abel
  rw [he, integralHomologyParity_add_two_zsmul]

def modTwoHomologyParity (c : ModHomology 2 M 3) : ZMod 2 :=
  e.integralHomologyParity ν r m (TwoConnectedCoefficients.middleReduction_surjective m c).choose

theorem modTwoHomologyParity_reduction (a : SingularHomology M 3) :
    e.modTwoHomologyParity ν r m (reductionHomologyMap 2 M 3 a) =
      e.integralHomologyParity ν r m a :=
  e.integralHomologyParity_eq_of_reduction_eq ν r m _ a
    (TwoConnectedCoefficients.middleReduction_surjective m
      (reductionHomologyMap 2 M 3 a)).choose_spec

theorem modTwoHomologyParity_zero : e.modTwoHomologyParity ν r m 0 = 0 := by
  have h := e.modTwoHomologyParity_reduction ν r m 0
  rwa [map_zero, integralHomologyParity_zero] at h

theorem modTwoHomologyParity_add (c d : ModHomology 2 M 3) :
    e.modTwoHomologyParity ν r m (c + d) =
      e.modTwoHomologyParity ν r m c + e.modTwoHomologyParity ν r m d +
        e.modTwoHomologyIntersection r m c d := by
  obtain ⟨a, rfl⟩ := TwoConnectedCoefficients.middleReduction_surjective m c
  obtain ⟨b, rfl⟩ := TwoConnectedCoefficients.middleReduction_surjective m d
  rw [← map_add, modTwoHomologyParity_reduction, modTwoHomologyParity_reduction,
    modTwoHomologyParity_reduction, modTwoHomologyIntersection_reduction]
  exact e.integralHomologyParity_add ν r m a b

theorem modTwoHomologyParity_smul (c : ZMod 2) (a : ModHomology 2 M 3) :
    e.modTwoHomologyParity ν r m (c • a) =
      (c * c) • e.modTwoHomologyParity ν r m a := by
  rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 from by decide) c with rfl | rfl
  · rw [zero_smul, zero_mul, zero_smul, modTwoHomologyParity_zero]
  · rw [one_smul, one_mul, one_smul]

def modTwoHomologyQuadraticForm : QuadraticForm (ZMod 2) (ModHomology 2 M 3) where
  toFun := e.modTwoHomologyParity ν r m
  toFun_smul := e.modTwoHomologyParity_smul ν r m
  exists_companion' := ⟨e.modTwoHomologyIntersection r m, e.modTwoHomologyParity_add ν r m⟩

theorem modTwoHomologyQuadraticForm_apply (a : ModHomology 2 M 3) :
    e.modTwoHomologyQuadraticForm ν r m a = e.modTwoHomologyParity ν r m a := rfl

theorem modTwoHomologyQuadraticForm_polar :
    (e.modTwoHomologyQuadraticForm ν r m).polarBilin = e.modTwoHomologyIntersection r m := by
  ext a b
  change e.modTwoHomologyParity ν r m (a + b) -
    e.modTwoHomologyParity ν r m a - e.modTwoHomologyParity ν r m b =
      e.modTwoHomologyIntersection r m a b
  rw [modTwoHomologyParity_add]
  abel

theorem modTwoHomologyParity_integralSphereClass (f : C(Sphere 3, M)) :
    e.modTwoHomologyParity ν r m (reductionHomologyMap 2 M 3 (integralSphereClass f)) =
      e.geometricSphereParity ν r f := by
  rw [modTwoHomologyParity_reduction, integralHomologyParity_sphereClass]

theorem modTwoHomologyQuadraticForm_sphereClass (f : C(Sphere 3, M)) :
    e.modTwoHomologyQuadraticForm ν r m (SixSphereMiddleParity.sphereClass f) =
      e.geometricSphereParity ν r f := by
  have hclass : reductionHomologyMap 2 M 3 (integralSphereClass f) =
      SixSphereMiddleParity.sphereClass f := by
    change reductionHomologyMap 2 M 3
      (singularHomologyMap f 3 integralCubeSphereClass) =
        modHomologyMap 2 f 3 (unitSphereModTopClass 2 2)
    rw [← modHomologyMap_reduction, ← modTwoCubeSphereClass_eq_standard]
    rfl
  rw [modTwoHomologyQuadraticForm_apply, ← hclass, modTwoHomologyParity_integralSphereClass]

include m h₂ in
theorem geometricSphereParity_eq_of_modTwoSphereClass_eq (f g : C(Sphere 3, M))
    (h : SixSphereMiddleParity.sphereClass f = SixSphereMiddleParity.sphereClass g) :
    e.geometricSphereParity ν r f = e.geometricSphereParity ν r g := by
  rw [← modTwoHomologyQuadraticForm_sphereClass e ν r m f,
    ← modTwoHomologyQuadraticForm_sphereClass e ν r m g, h]

theorem modTwoHomologyQuadraticForm_unique
    (Q : QuadraticForm (ZMod 2) (ModHomology 2 M 3))
    (hQ : ∀ f : C(Sphere 3, M),
      Q (SixSphereMiddleParity.sphereClass f) = e.geometricSphereParity ν r f) :
    Q = e.modTwoHomologyQuadraticForm ν r m := by
  ext c
  obtain ⟨f, rfl⟩ := modTwoSphereClass_surjective m c
  rw [modTwoSphereClass_eq_standard]
  exact (hQ f.val).trans (e.modTwoHomologyQuadraticForm_sphereClass ν r m f.val).symm

theorem modTwoHomologyQuadraticForm_retraction_independent (r' : TubularRetraction e) :
    e.modTwoHomologyQuadraticForm ν r m = e.modTwoHomologyQuadraticForm ν r' m := by
  apply e.modTwoHomologyQuadraticForm_unique ν r' m
  intro f
  rw [modTwoHomologyQuadraticForm_sphereClass]
  exact e.geometricSphereParity_retraction_independent ν r r' f

theorem modTwoHomologyQuadraticForm_basepoint_independent
    (m' : M) [Subsingleton (π_ 2 M m')] :
    e.modTwoHomologyQuadraticForm ν r m = e.modTwoHomologyQuadraticForm ν r m' := by
  apply e.modTwoHomologyQuadraticForm_unique ν r m'
  exact e.modTwoHomologyQuadraticForm_sphereClass ν r m

end NoExoticSixSphere.EuclideanEmbedding
