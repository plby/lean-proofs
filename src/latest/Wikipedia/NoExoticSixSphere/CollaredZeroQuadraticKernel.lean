import Wikipedia.NoExoticSixSphere.CollaredZeroNormalFrame
import Wikipedia.NoExoticSixSphere.EmbeddedTimeTwoConnectedQuadraticKernel

/-!
# The checked quadratic kernel on actual low-surgery filling states

The map is the literal inclusion of the native zero fiber into the
state's positive half. The embedding and full induced frame are exactly
the state constructions, including their chosen ambient retraction.
No frame, collar, or compactness datum is added to the state.
-/

noncomputable section

open Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.CollaredZero

open GLOrthonormalization Wikipedia.HopfProblem.DegreeCollapse
open Wikipedia.HopfProblem.SingularMayerVietoris Wikipedia.HopfProblem.SphereHomology
open Wikipedia.HopfProblem.SphereHomologyCoefficients

attribute [local instance] modHomologyModule

variable {B : Type} [TopologicalSpace B] (S : LowCollaredSevenState B)

def halfInclusion : C(S.Zero, S.PositiveHalf) := SphereFourTube.zeroToHalf S.zeroTimeMap

variable [SimplyConnectedSpace S.PositiveHalf]
  [Subsingleton (SingularHomology S.PositiveHalf 2)] (m : S.Space)

theorem sphereParity_zero_of_even_half_image
    (f : C(Sphere 3, S.Zero)) (y : SingularHomology S.PositiveHalf 3)
    (hclass : singularHomologyMap (halfInclusion S) 3
      (singularHomologyMap f 3 (unitSphereTopClass 2)) = (2 : ℤ) • y) :
    letI := S.zeroAtlas;
    ∀ (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
      (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)),
      (embedding S).sphereParity (normalFrame S m) f hf hi hd = 0 := by
  let := S.zeroAtlas
  let : SimplyConnectedSpace (TimeCollar.NonnegativeHalf S.zeroTimeMap) :=
    ‹SimplyConnectedSpace S.PositiveHalf›
  let : Subsingleton (SingularHomology (TimeCollar.NonnegativeHalf S.zeroTimeMap) 2) :=
    ‹Subsingleton (SingularHomology S.PositiveHalf 2)›
  intro hf hi hd
  exact EmbeddedTime.sphereParity_zero_of_even_half_image S.embedding (retraction S m)
    S.zeroTimeMap S.time_smooth S.time_regular S.normalFrame m S.collar f y hclass hf hi hd

variable [SimplyConnectedSpace S.Zero] (z : S.Zero) [Subsingleton (π_ 2 S.Zero z)]

theorem modTwoQuadraticForm_zero_on_full_kernel :
    letI := S.zeroAtlas;
    letI := S.zero_isManifold;
    letI : CompactSpace S.Zero :=
      (isClosed_eq S.zeroTimeMap.continuous continuous_const
        ).isClosedEmbedding_subtypeVal.compactSpace;
    ∀ (rZ : (embedding S).TubularRetraction) (b : ModHomology 2 S.Zero 3),
      modHomologyMap 2 (halfInclusion S) 3 b = 0 →
      (embedding S).modTwoHomologyQuadraticForm (normalFrame S m) rZ z b = 0 := by
  let := S.zeroAtlas
  let := S.zero_isManifold
  let : SimplyConnectedSpace (TimeCollar.NonnegativeHalf S.zeroTimeMap) :=
    ‹SimplyConnectedSpace S.PositiveHalf›
  let : Subsingleton (SingularHomology (TimeCollar.NonnegativeHalf S.zeroTimeMap) 2) :=
    ‹Subsingleton (SingularHomology S.PositiveHalf 2)›
  let : SimplyConnectedSpace {x : S.Space // S.zeroTimeMap x = 0} :=
    ‹SimplyConnectedSpace S.Zero›
  let : Subsingleton (π_ 2 {x : S.Space // S.zeroTimeMap x = 0} z) :=
    ‹Subsingleton (π_ 2 S.Zero z)›
  let : CompactSpace S.Zero :=
    (isClosed_eq S.zeroTimeMap.continuous continuous_const
      ).isClosedEmbedding_subtypeVal.compactSpace
  intro rZ b hker
  exact EmbeddedTime.modTwoQuadraticForm_zero_on_full_boundary_kernel S.embedding (retraction S m)
    S.zeroTimeMap S.time_smooth S.time_regular S.normalFrame m S.collar z rZ b hker

end NoExoticSixSphere.CollaredZero
