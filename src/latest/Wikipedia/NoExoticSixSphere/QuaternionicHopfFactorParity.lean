import Wikipedia.NoExoticSixSphere.QuaternionicHopfFactorContraction
import Wikipedia.NoExoticSixSphere.ConstantHopfFrameTwist
import Wikipedia.NoExoticSixSphere.ModTwoHomologyQuadraticParity

/-!
# The actual Hopf-product factor spheres both have geometric parity one

The raw combined frame maps contract, but their common source twist has
the proved nonzero obstruction. This computes the actual spanning-disk
parities. The values also hold for the choice-independent geometric parity
and for the original quadratic refinement on mod-two middle homology.
No Arf or bordism detection theorem is assumed.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.QuaternionicHopf

open Stiefel DiskBoundary SpanningDiskFrameCoordinates EuclideanEmbedding

local instance : ChartedSpace (V 6) (Sphere 3 × Sphere 3) := southPairEuclideanAtlas
local instance : IsManifold (𝓡 6) ∞ (Sphere 3 × Sphere 3) := southPairEuclideanIsManifold

theorem southPairLeftSphere_parity_one :
    southPairEuclideanEmbedding.sphereParity southPairEuclideanNormalFrame
      southPairLeftSphere contMDiff_southPairLeftSphere southPairLeftSphere_injective
        southPairLeftSphere_differential_injective = 1 := by
  apply zmodTwo_eq_of_zero_iff
  apply iff_of_false _ (by decide)
  intro hz
  have he := southPairLeftSphere_parity_zero_iff.mp hz
  exact twisted_constant_not_extends (southPairLeftRawFrameMap southFrameReference)
    ((extends_homotopic_iff southPairLeftRawFrame_twisted_constant).mp he)

theorem southPairRightSphere_parity_one :
    southPairEuclideanEmbedding.sphereParity southPairEuclideanNormalFrame
      southPairRightSphere contMDiff_southPairRightSphere southPairRightSphere_injective
        southPairRightSphere_differential_injective = 1 := by
  apply zmodTwo_eq_of_zero_iff
  apply iff_of_false _ (by decide)
  intro hz
  have he := southPairRightSphere_parity_zero_iff.mp hz
  exact twisted_constant_not_extends (southPairRightRawFrameMap southFrameReference)
    ((extends_homotopic_iff southPairRightRawFrame_twisted_constant).mp he)

variable (r : TubularRetraction southPairEuclideanEmbedding)

theorem southPairLeftSphere_geometricParity_one :
    southPairEuclideanEmbedding.geometricSphereParity southPairEuclideanNormalFrame r
      southPairLeftSphere = 1 := by
  rw [southPairEuclideanEmbedding.geometricSphereParity_eq_of_embedding
    southPairEuclideanNormalFrame r southPairLeftSphere contMDiff_southPairLeftSphere
      southPairLeftSphere_injective southPairLeftSphere_differential_injective]
  exact southPairLeftSphere_parity_one

theorem southPairRightSphere_geometricParity_one :
    southPairEuclideanEmbedding.geometricSphereParity southPairEuclideanNormalFrame r
      southPairRightSphere = 1 := by
  rw [southPairEuclideanEmbedding.geometricSphereParity_eq_of_embedding
    southPairEuclideanNormalFrame r southPairRightSphere contMDiff_southPairRightSphere
      southPairRightSphere_injective southPairRightSphere_differential_injective]
  exact southPairRightSphere_parity_one

local instance spherePiTwo (s : Sphere 3) :
    Subsingleton (HomotopyGroup (Fin 2) (Sphere 3) s) :=
  subsingleton_sphereHomotopyGroup (by decide) s

local instance productSimplyConnected : SimplyConnectedSpace (Sphere 3 × Sphere 3) :=
  HigherHomotopy.simplyConnected_product

local instance productPiTwo (p : Sphere 3 × Sphere 3) :
    Subsingleton (HomotopyGroup (Fin 2) (Sphere 3 × Sphere 3) p) :=
  HigherHomotopy.subsingleton_product p.1 p.2

variable (p : Sphere 3 × Sphere 3)

theorem southPairLeftSphere_quadraticValue_one :
    southPairEuclideanEmbedding.modTwoHomologyQuadraticForm southPairEuclideanNormalFrame r p
      (SixSphereMiddleParity.sphereClass southPairLeftSphere) = 1 := by
  rw [southPairEuclideanEmbedding.modTwoHomologyQuadraticForm_sphereClass]
  exact southPairLeftSphere_geometricParity_one r

theorem southPairRightSphere_quadraticValue_one :
    southPairEuclideanEmbedding.modTwoHomologyQuadraticForm southPairEuclideanNormalFrame r p
      (SixSphereMiddleParity.sphereClass southPairRightSphere) = 1 := by
  rw [southPairEuclideanEmbedding.modTwoHomologyQuadraticForm_sphereClass]
  exact southPairRightSphere_geometricParity_one r

end NoExoticSixSphere.QuaternionicHopf
