import Wikipedia.NoExoticSixSphere.TimeCollarBoundaryFundamentalClass
import Wikipedia.NoExoticSixSphere.ZeroSecondHomologyCapKernel

/-!
# Self-orthogonality of the collared half's actual boundary cap kernel

The genuine boundary fundamental class supplies the cap-restriction
criterion. Thus vanishing of second integral homology on the boundary and
half makes the full middle-dimensional inclusion kernel self-orthogonal
for the actual cap pairing. No connectedness of the boundary is required.
This statement does not assert that a geometric quadratic form vanishes.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.TimeCollarDuality

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
open Wikipedia.HopfProblem.SphereHomologyCoefficients
open Wikipedia.HopfProblem.SingularMayerVietoris

attribute [local instance] modHomologyModule

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B]
  [ChartedSpace (Vector 7) M] [IsManifold (𝓡 7) ∞ M] [T2Space M] [CompactSpace M]
  {t : M → ℝ} (C : TimeCollar t B)
  [ChartedSpace (Vector 6) (boundary t)] [CompactSpace (boundary t)]
  [Subsingleton (SingularHomology (boundary t) 2)]
  [Subsingleton (SingularHomology (NonnegativeHalf t) 2)]

local instance : Fact (Module.finrank ℝ (Vector 6) = (3 + 2) + 1) := ⟨by simp⟩

include C in
theorem boundaryCapKernel_selfOrthogonal (b : ModHomology 2 (boundary t) 3) :
    (∀ a : ModHomology 2 (boundary t) 3,
      modHomologyMap 2 (subtypeInclusion (boundary t)) 3 a = 0 →
        ZeroSecondHomologyCap.pairing (E := Vector 6) (boundary t) a b = 0) ↔
      modHomologyMap 2 (subtypeInclusion (boundary t)) 3 b = 0 :=
  ZeroSecondHomologyCap.kernel_selfOrthogonal (E := Vector 6)
    (subtypeInclusion (boundary t)) (boundaryCap_kernel C 3 3 rfl) b

end NoExoticSixSphere.TimeCollarDuality
