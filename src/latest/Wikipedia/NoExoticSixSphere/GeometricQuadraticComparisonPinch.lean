import Wikipedia.NoExoticSixSphere.BasedTransverseImmersedSpherePair
import Wikipedia.NoExoticSixSphere.ComparisonPinchBasedHomotopy
import Wikipedia.NoExoticSixSphere.CleanQuadraticSphereResolution
import Wikipedia.NoExoticSixSphere.GeometricSphereIntersection

/-!
# Quadratic parity for comparison pinches of arbitrary continuous based inputs

All immersion, transversality, and unique-fiber conditions are discharged by
the constructed representatives. The actual based homotopies compare their
pinch with the original one, and ordinary homotopy invariance transfers both
corrected parities and the intersection number. No genericity or clean-chart
data are assumptions on the input sphere maps.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization SphereSumNeck

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] [CompactSpace M]
  (e : EuclideanEmbedding 6 M)
  (ν : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) (r : TubularRetraction e)

theorem geometricSphereParity_comparisonPinch_of_based
    (f g : C(Sphere 3, M)) (hzero : f (sourceChart 0) = g (sourceChart 0))
    {τ : ℝ} (hτ : 0 < τ) :
    e.geometricSphereParity ν r (comparisonPinch f g τ hτ.ne' hzero) =
      e.geometricSphereParity ν r f + e.geometricSphereParity ν r g +
        e.sphereIntersectionNumber r f g := by
  obtain ⟨F, G, hF, hG, HF, HG, hFi, hGi, hFt, hGt, hFGt, hFG0, hFu, hGu⟩ :=
    e.exists_based_transverse_immersed_pair r f g hzero
  have HP := comparisonPinch_homotopic_of_based f g F G τ hτ.ne' hzero hFG0 HF HG
  have hqF := e.geometricSphereParity_homotopic ν r f F HF.homotopic
  have hqG := e.geometricSphereParity_homotopic ν r g G HG.homotopic
  have hI : e.sphereIntersectionNumber r f g = MapIntersections.parity F G :=
    (e.sphereIntersectionNumber_homotopic r f F g G HF.homotopic HG.homotopic).trans
      (e.sphereIntersectionNumber_eq_parity r F G hF hG hFGt)
  calc
    e.geometricSphereParity ν r (comparisonPinch f g τ hτ.ne' hzero) =
        e.geometricSphereParity ν r (comparisonPinch F G τ hτ.ne' hFG0) :=
      e.geometricSphereParity_homotopic ν r _ _ HP
    _ = e.geometricSphereParity ν r F + e.geometricSphereParity ν r G +
        MapIntersections.parity F G :=
      e.geometricSphereParity_comparisonPinch ν r F G hF hG hFi hGi hFt hGt hFGt
        hFG0 hFu hGu hτ
    _ = e.geometricSphereParity ν r f + e.geometricSphereParity ν r g +
        e.sphereIntersectionNumber r f g := by rw [← hqF, ← hqG, ← hI]

end NoExoticSixSphere.EuclideanEmbedding
