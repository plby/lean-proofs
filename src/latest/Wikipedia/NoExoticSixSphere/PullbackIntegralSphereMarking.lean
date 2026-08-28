import Wikipedia.NoExoticSixSphere.PullbackIntegralHomologyParity
import Wikipedia.HopfProblem.DegreeCollapseCubeSphereGenerator

/-!
# Pulled-back parity and the independently marked sphere generator

The genuine cubical generator equals the surgery marking up to sign.
Negation invariance of the actual pulled-back parity removes that sign;
the two integral generators are never identified by definition.
-/

noncomputable section

open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization SmoothCube
open Wikipedia.HopfProblem.SingularMayerVietoris Wikipedia.HopfProblem.SphereHomology

variable {M X : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] [CompactSpace M]
  [TopologicalSpace X] [SimplyConnectedSpace X]
  (e : EuclideanEmbedding 6 M)
  (ν : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) (r : TubularRetraction e)
  (i : C(X, M)) (x : X) [Subsingleton (π_ 2 X x)]

theorem pullbackIntegralParity_markedSphereClass (f : C(Sphere 3, X)) :
    e.pullbackIntegralParity ν r i x (singularHomologyMap f 3 (unitSphereTopClass 2)) =
      e.geometricSphereParity ν r (i.comp f) := by
  have h := e.pullbackIntegralParity_sphereClass ν r i x f
  rcases Wikipedia.HopfProblem.DegreeCollapse.CubeSphereGenerator.standard_or_negative with hp | hn
  · unfold integralSphereClass at h
    rwa [hp] at h
  · unfold integralSphereClass at h
    rwa [hn, map_neg, pullbackIntegralParity_neg] at h

end NoExoticSixSphere.EuclideanEmbedding
