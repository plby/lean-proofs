import Wikipedia.HopfProblem.DegreeCollapseSurgeryPairConnectivity
import Wikipedia.HopfProblem.DegreeCollapseSevenSurgeryHalfQuotients
import Wikipedia.NoExoticSixSphere.Topology.SimplyConnectedSphere

/-!
# The actual seven-dimensional surgery preserves simple connectivity and H2

Both actual attaching spheres are three-spheres. The original surgery pair
therefore preserves simple connectivity of the closed ambient manifold and
of its nonnegative half. The original half's existing homology comparison
and the closed pair's genuine inclusion comparison identify H2 as well.
No finiteness or fourth-homology assumption is used.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery

open NoExoticSixSphere GLOrthonormalization
open SingularMayerVietoris SphereHomology

local instance : SimplyConnectedSpace (Sphere 3) := EuclideanSphere.simplyConnectedSpace 1
local instance : Subsingleton (SingularHomology (Sphere 3) 1) :=
  unitSphere_homology_subsingleton 2 1 (by decide) (by decide)
local instance : Subsingleton (SingularHomology (Sphere 3) 2) :=
  unitSphere_homology_subsingleton 2 2 (by decide) (by decide)

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2) (T : TimeData A)

local instance : CompactSpace (Target A hR) := compactSpace_target A hR
local instance : CompactSpace (PositiveHalf A hR T) := compactSpace_positiveHalf A hR T

theorem target_simplyConnected_iff :
    SimplyConnectedSpace (Target A hR) ↔ SimplyConnectedSpace M :=
  SurgeryPairBody.simplyConnected_iff (closedBoundaryPair A hR)

theorem positiveHalf_simplyConnected_iff :
    SimplyConnectedSpace (PositiveHalf A hR T) ↔ SimplyConnectedSpace (OldPositiveHalf A T) :=
  SurgeryPairBody.simplyConnected_iff (halfBoundaryPair A hR T)

theorem positiveHalf_simplyConnected [SimplyConnectedSpace (OldPositiveHalf A T)] :
    SimplyConnectedSpace (PositiveHalf A hR T) :=
  (positiveHalf_simplyConnected_iff A hR T).2 inferInstance

def targetSecondHomologyEquiv : SingularHomology M 2 ≃ₗ[ℤ] SingularHomology (Target A hR) 2 := by
  let : Subsingleton (SingularHomology
      (Wikipedia.SmoothSixDPoincare.PuncturedHandle.UnitSphere (Vector 4)) 1) :=
    inferInstanceAs (Subsingleton (SingularHomology (Sphere 3) 1))
  let : Subsingleton (SingularHomology
      (Wikipedia.SmoothSixDPoincare.PuncturedHandle.UnitSphere (Vector 4)) (1 + 1)) :=
    inferInstanceAs (Subsingleton (SingularHomology (Sphere 3) 2))
  exact SurgeryPairBody.lowHomologyEquiv (closedBoundaryPair A hR) 1

theorem target_second_homology [Subsingleton (SingularHomology M 2)] :
    Subsingleton (SingularHomology (Target A hR) 2) :=
  (targetSecondHomologyEquiv A hR).symm.injective.subsingleton

theorem positiveHalf_second_homology [Subsingleton (SingularHomology (OldPositiveHalf A T) 2)] :
    Subsingleton (SingularHomology (PositiveHalf A hR T) 2) :=
  (halfHomologyEquivOther A hR T 1 (by decide) (by decide) (by decide)).symm.injective.subsingleton

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery
