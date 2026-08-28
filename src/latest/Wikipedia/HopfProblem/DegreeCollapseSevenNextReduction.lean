import Wikipedia.HopfProblem.DegreeCollapseTimeCollarNonzeroDiagonalSurgery
import Wikipedia.HopfProblem.DegreeCollapseSevenSurgeryHalfLinking

/-!
# The actual finite order-four surgery half admits a further strict reduction

The first surgery's actual target has its own embedding, full normal frame,
regular time function, and preserved collar. Its original new-half linking
pairing supplies a nonzero diagonal whenever some class has nonzero double.
The generic collared reduction constructs the next actual surgery and a
strict drop in its half's finite third-homology cardinality.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery

open NoExoticSixSphere GLOrthonormalization SingularMayerVietoris

local instance : Fact (Module.finrank ℝ (Vector 7) = 7) := ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2) (T : TimeData A)
  [SimplyConnectedSpace M] [Subsingleton (SingularHomology M 2)] [Finite (SingularHomology M 3)]
  [SimplyConnectedSpace (OldPositiveHalf A T)] [Finite (SingularHomology (PositiveHalf A hR T) 3)]
  {B : Type} [TopologicalSpace B] (C : TimeCollar T.time B)
  [Subsingleton (SingularHomology B 2)] [Subsingleton (SingularHomology B 3)]
  [Subsingleton (SingularHomology B 4)]

include C in
theorem strict_reduction_after_double_ne_zero
    (x : SingularHomology (PositiveHalf A hR T) 3) (hx : (2 : ℤ) • x ≠ 0) (v : Sphere 3) :
    letI := targetChartedSpace A hR;
    letI := target_isManifold A hR;
    letI := compactSpace_target A hR;
    TimeCollar.HasStrictReduction (inducedEmbedding A hR) (normalFraming A hR)
      (timeFunction A hR T) v := by
  let := targetChartedSpace A hR
  let := target_isManifold A hR
  let := compactSpace_target A hR
  let : SimplyConnectedSpace (Target A hR) := (target_simplyConnected_iff A hR).2 inferInstance
  let : Subsingleton (SingularHomology (Target A hR) 2) := target_second_homology A hR
  let : Finite (SingularHomology (Target A hR) 3) := target_third_finite_of_half A hR T
  let : SimplyConnectedSpace (PositiveHalf A hR T) := positiveHalf_simplyConnected A hR T
  obtain ⟨c, hc⟩ := positiveHalfLinking_nonzero_diagonal_of_double_ne_zero A hR T C x hx
  exact (preservedTimeCollar A hR T C).strictReduction_of_diagonal
    (inducedEmbedding A hR) (normalFraming A hR) (contMDiff_timeFunction A hR T)
    (regular_timeFunction_zero A hR T) c hc v

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery
