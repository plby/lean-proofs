import Wikipedia.HopfProblem.DegreeCollapseTimeCollarExteriorPair
import Wikipedia.HopfProblem.DegreeCollapseSevenClosedRelativePair

/-!
# Actual relative half-to-closed comparison for every collared seven-surgery

The original positive attachment margin puts the entire core at positive
time. The preserved time collar then proves the original relative homology
inclusion bijective in every degree and the original degree-four cohomology
pullback bijective. No reflected presentation or comparison premise is used.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
namespace FramedAttachingProduct.UnitSurgery.ExteriorTwist

open NoExoticSixSphere GLOrthonormalization

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hA : A.radius = 2) (T : TimeData A)
  {B : Type} [TopologicalSpace B] (C : TimeCollar T.time B)

include C in
theorem collaredHalfToClosedPairMap_bijective (k : ℕ) :
    Bijective (halfToClosedPairMap A hA T k) := by
  refine C.halfExterior_relative_bijective (closedBoundaryPair A hA) (timeFunction A hA T)
    (fun p ↦ (closedBoundaryPair_oldPiece_positive A hA T p).le)
    (fun p ↦ by rw [closedBoundaryPair_newPiece_time]; norm_num)
    (fun p ↦ by
      rw [closedBoundaryPair_exterior_time]
      exact (SurgeryTimeProfile.profile_nonneg_iff T.margin_pos _).symm) ?_ k
  intro s
  apply T.margin_pos.trans_le
  change T.margin ≤ T.time (A.tube (s, 0))
  exact T.tube_time s 0 (by rw [hA]; simp)

include C in
theorem collaredHalfToClosedCohomologyPullback_bijective :
    Bijective (halfToClosedCohomologyPullback A hA T 4) :=
  halfToClosedCohomologyPullback_bijective A hA T
    (collaredHalfToClosedPairMap_bijective A hA T C 3).2
    (collaredHalfToClosedPairMap_bijective A hA T C 4)

end FramedAttachingProduct.UnitSurgery.ExteriorTwist
end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
