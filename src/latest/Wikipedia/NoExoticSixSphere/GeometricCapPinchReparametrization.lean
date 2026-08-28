import Wikipedia.NoExoticSixSphere.GeometricSphereLinearReparametrization
import Wikipedia.NoExoticSixSphere.SphereTailReflectionIsometry
import Wikipedia.NoExoticSixSphere.SphereCapComparisonDiffeomorphism
import Wikipedia.NoExoticSixSphere.SphereResolutionPinchScaleHomotopy

/-!
# The explicit cap-to-pinch input changes preserve geometric sphere parity

Positive scale is removed by a genuine based homotopy. At scale two the
northern change is the constructed ambient linear isometry, and the
southern change is its composition with the actual tail reflection.
The checked frame and double-point calculations prove parity preservation
for both inputs. This does not yet give the quadratic identity for their pinch.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere
namespace SphereSumNeck

open GLOrthonormalization SphereLinearReparametrization

variable {M : Type*} [TopologicalSpace M]

theorem northPinchInput_two (F : C(Sphere 3, M)) :
    northPinchInput F 2 (by norm_num) = F.comp (sphereMap capComparisonLinearEquiv) := by
  apply ContinuousMap.ext
  intro x
  change F (capPinchComparison 2 (by norm_num) x) = F (sphereMap capComparisonLinearEquiv x)
  apply congrArg F
  apply Subtype.ext
  exact capPinchComparison_two_val x

theorem southPinchInput_two (G : C(Sphere 3, M)) :
    southPinchInput G 2 (by norm_num) =
      G.comp (sphereMap (tailReflectionLinearEquiv.trans capComparisonLinearEquiv)) := by
  apply ContinuousMap.ext
  intro x
  change G (capPinchComparison 2 (by norm_num) (tailReflection x)) =
    G (sphereMap (tailReflectionLinearEquiv.trans capComparisonLinearEquiv) x)
  apply congrArg G
  apply Subtype.ext
  rw [capPinchComparison_two_val]
  rfl

end SphereSumNeck

namespace EuclideanEmbedding

open GLOrthonormalization SphereSumNeck

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) (r : TubularRetraction e)

theorem geometricSphereParity_northPinchInput (F : C(Sphere 3, M)) {ε : ℝ} (hε : 0 < ε) :
    e.geometricSphereParity a r (northPinchInput F ε hε.ne') = e.geometricSphereParity a r F := by
  have h := e.geometricSphereParity_homotopic a r (northPinchInput F ε hε.ne')
    (northPinchInput F 2 (by norm_num))
    ⟨(northPinchScaleHomotopy F hε (by norm_num)).toHomotopy⟩
  rw [northPinchInput_two] at h
  exact h.trans (e.geometricSphereParity_precomp_linear a r capComparisonLinearEquiv F)

theorem geometricSphereParity_southPinchInput (G : C(Sphere 3, M)) {ε : ℝ} (hε : 0 < ε) :
    e.geometricSphereParity a r (southPinchInput G ε hε.ne') = e.geometricSphereParity a r G := by
  have h := e.geometricSphereParity_homotopic a r (southPinchInput G ε hε.ne')
    (southPinchInput G 2 (by norm_num))
    ⟨(southPinchScaleHomotopy G hε (by norm_num)).toHomotopy⟩
  rw [southPinchInput_two] at h
  exact h.trans (e.geometricSphereParity_precomp_linear a r
    (tailReflectionLinearEquiv.trans capComparisonLinearEquiv) G)

end EuclideanEmbedding
end NoExoticSixSphere
