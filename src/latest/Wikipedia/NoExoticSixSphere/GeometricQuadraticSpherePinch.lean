import Wikipedia.NoExoticSixSphere.GeometricQuadraticComparisonPinch
import Wikipedia.NoExoticSixSphere.GeometricIntersectionReparametrization
import Wikipedia.NoExoticSixSphere.GeometricCapPinchReparametrization

/-!
# Quadratic parity for the standard geometric sphere pinch

Undo both actual cap comparison isometries, including the southern reflection,
before applying the arbitrary-input comparison-pinch formula. Their inverses
preserve corrected parity and the mutual intersection number. The resulting
identity concerns the original input maps and the original hemisphere pinch.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere
namespace SphereSumNeck

open GLOrthonormalization SphereLinearReparametrization

variable {M : Type*} [TopologicalSpace M]

theorem northPinchInput_inverse_linear (f : C(Sphere 3, M)) :
    northPinchInput (f.comp (sphereMap capComparisonLinearEquiv.symm)) 2
      (by norm_num) = f := by
  rw [northPinchInput_two]
  apply ContinuousMap.ext
  intro x
  change f (sphereMap capComparisonLinearEquiv.symm
    (sphereMap capComparisonLinearEquiv x)) = f x
  apply congrArg f
  apply Subtype.ext
  exact capComparisonLinearEquiv.symm_apply_apply x.val

theorem southPinchInput_inverse_linear (g : C(Sphere 3, M)) :
    southPinchInput (g.comp (sphereMap
      (tailReflectionLinearEquiv.trans capComparisonLinearEquiv).symm)) 2
      (by norm_num) = g := by
  rw [southPinchInput_two]
  apply ContinuousMap.ext
  intro x
  change g (sphereMap (tailReflectionLinearEquiv.trans capComparisonLinearEquiv).symm
    (sphereMap (tailReflectionLinearEquiv.trans capComparisonLinearEquiv) x)) = g x
  apply congrArg g
  apply Subtype.ext
  exact (tailReflectionLinearEquiv.trans capComparisonLinearEquiv).symm_apply_apply x.val

end SphereSumNeck

namespace EuclideanEmbedding

open GLOrthonormalization SphereSumNeck SphereLinearReparametrization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] [CompactSpace M]
  (e : EuclideanEmbedding 6 M)
  (ν : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) (r : TubularRetraction e)

theorem geometricSphereParity_pinch (f g : C(Sphere 3, M))
    (hbase : f (antipode pinchPole) = g (antipode pinchPole)) :
    e.geometricSphereParity ν r (SphereFold.pinch pinchPole f g hbase) =
      e.geometricSphereParity ν r f + e.geometricSphereParity ν r g +
        e.sphereIntersectionNumber r f g := by
  let L := capComparisonLinearEquiv
  let K := tailReflectionLinearEquiv.trans capComparisonLinearEquiv
  let F := f.comp (sphereMap L.symm)
  let G := g.comp (sphereMap K.symm)
  have hn : northPinchInput F 2 (by norm_num) = f := northPinchInput_inverse_linear f
  have hs : southPinchInput G 2 (by norm_num) = g := southPinchInput_inverse_linear g
  have hn0 := congrArg (fun h : C(Sphere 3, M) ↦ h (antipode pinchPole)) hn
  have hs0 := congrArg (fun h : C(Sphere 3, M) ↦ h (antipode pinchPole)) hs
  change F (capPinchComparison 2 (by norm_num) (antipode pinchPole)) =
    f (antipode pinchPole) at hn0
  change G (capPinchComparison 2 (by norm_num) (tailReflection (antipode pinchPole))) =
    g (antipode pinchPole) at hs0
  rw [capPinchComparison_base] at hn0
  rw [tailReflection_base, capPinchComparison_base] at hs0
  have hzero : F (sourceChart 0) = G (sourceChart 0) := hn0.trans (hbase.trans hs0.symm)
  have hq := e.geometricSphereParity_comparisonPinch_of_based ν r F G hzero
    (τ := 2) (by norm_num)
  have hp : comparisonPinch F G 2 (by norm_num) hzero =
      SphereFold.pinch pinchPole f g hbase := by
    unfold comparisonPinch
    simp only [hn, hs]
  rw [hp] at hq
  have hF : e.geometricSphereParity ν r F = e.geometricSphereParity ν r f :=
    e.geometricSphereParity_precomp_linear ν r L.symm f
  have hG : e.geometricSphereParity ν r G = e.geometricSphereParity ν r g :=
    e.geometricSphereParity_precomp_linear ν r K.symm g
  have hI : e.sphereIntersectionNumber r F G = e.sphereIntersectionNumber r f g :=
    e.sphereIntersectionNumber_precomp_linear r L.symm K.symm f g
  exact hq.trans (by rw [hF, hG, hI])

end EuclideanEmbedding
end NoExoticSixSphere
