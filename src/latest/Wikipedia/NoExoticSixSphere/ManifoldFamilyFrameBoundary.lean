import Wikipedia.NoExoticSixSphere.ManifoldFamilyGlobalFrame
import Wikipedia.NoExoticSixSphere.ManifoldSphereBoundaryParity

/-!
# The boundary obstruction relation for the constructed global frame map

This applies the actual boundary homology theorem to the frame map built
from the original family, its spatial derivative, and its given normal
framing. The frame map is constructed, not supplied as an extra input.
The local obstruction-one calculation and the comparison of the endpoint
values with geometric normal-disk parity are still separate obligations.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (g : ℝ → Sphere 3 → M)
  (hg : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 6) ∞ (uncurry g))
  (P : SphereFamily.ParityBallSystem g)

def familyBoundaryObstruction (i : SphereFamily.ParityBallSystem.BoundaryIndex g) : ZMod 2 :=
  sphereThirdObstruction ((e.ambientDimension - 6) + 1)
    ((e.puncturedGlobalFrameMap a g hg P).comp (P.sphereInclusion i))

theorem sum_familyBoundaryObstruction_zero
    [Fintype (SphereFamily.ParityBallSystem.BoundaryIndex g)] :
    ∑ i, e.familyBoundaryObstruction a g hg P i = 0 :=
  P.sum_boundary_frame_obstruction_zero ((e.ambientDimension - 6) + 1)
    (e.puncturedGlobalFrameMap a g hg P)

theorem endpoint_familyBoundaryObstruction_eq_of_even_links
    (heven : Even (Nat.card (SphereFamily.singularParameters (n := 6) g)))
    (hlinks : ∀ q : SphereFamily.singularParameters (n := 6) g,
      e.familyBoundaryObstruction a g hg P (.inr q) = 1) :
    e.familyBoundaryObstruction a g hg P (.inl false) =
      e.familyBoundaryObstruction a g hg P (.inl true) :=
  P.endpoint_frame_obstruction_eq_of_even_links ((e.ambientDimension - 6) + 1)
    (e.puncturedGlobalFrameMap a g hg P) heven hlinks

end NoExoticSixSphere.EuclideanEmbedding
