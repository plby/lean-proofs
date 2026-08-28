import Wikipedia.NoExoticSixSphere.AffineStabilizedSphereParity
import Wikipedia.NoExoticSixSphere.DiffeomorphQuadraticTransport

/-!
# Actual quadratic and Arf transport through affine framed comparisons

The equivalence is the original diffeomorphism's induced middle-homology
map. The proved sphere-parity comparison supplies its quadratic-isometry
property, and the existing nondegenerate Arf theorem gives invariance.
No bordism-invariance or Arf-detection hypothesis is added.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Wikipedia.HopfProblem SphereHomologyCoefficients

namespace NoExoticSixSphere.AffineStabilizedFramedDiffeomorph

open GLOrthonormalization EuclideanEmbedding

attribute [local instance] modHomologyModule

variable {M M' : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [TopologicalSpace M'] [ChartedSpace (Vector 6) M']
  {e : EuclideanEmbedding 6 M} {e' : EuclideanEmbedding 6 M'}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel}
  {a' : SmoothRangeFrame (𝓡 6) e'.normalProjection e'.NormalModel}
  (F : AffineStabilizedFramedDiffeomorph e a e' a')
  [IsManifold (𝓡 6) ∞ M] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
  [IsManifold (𝓡 6) ∞ M'] [T2Space M'] [CompactSpace M'] [SimplyConnectedSpace M']
  (r : TubularRetraction e) (r' : TubularRetraction e') (m : M) (m' : M')
  [Subsingleton (π_ 2 M m)] [Subsingleton (π_ 2 M' m')]

def quadraticFormIsometry :
    (e.modTwoHomologyQuadraticForm a r m).IsometryEquiv
      (e'.modTwoHomologyQuadraticForm a' r' m') :=
  DiffeomorphQuadraticTransport.quadraticFormIsometry F.diffeomorph e e' a a'
    (fun f hf hi hd ↦ F.sphereParity_comp f hf hd hi) r r' m m'

include F in
theorem geometricArf_eq :
    GeometricArf.invariant e a r m = GeometricArf.invariant e' a' r' m' :=
  DiffeomorphQuadraticTransport.geometricArf_eq F.diffeomorph e e' a a'
    (fun f hf hi hd ↦ F.sphereParity_comp f hf hd hi) r r' m m'

end NoExoticSixSphere.AffineStabilizedFramedDiffeomorph
