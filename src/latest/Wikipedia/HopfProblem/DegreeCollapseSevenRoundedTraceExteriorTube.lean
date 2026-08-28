import Wikipedia.HopfProblem.DegreeCollapseSevenRoundedTraceBoundaryExterior
import Wikipedia.NoExoticSixSphere.RoundedCornerGraphEnds

/-! # Exact exterior membership in the original tube and rounded collar coordinates -/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel SevenRoundedHandleCorner SmoothCornerRounding

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem tube_mem_outer_iff (s : Sphere 3) {v : Vector 4}
    (hv : v ∈ closedBall (0 : Vector 4) A.radius) :
    A.tube (s, v) ∈ outerTubeImage A ↔ v ∈ closedBall (0 : Vector 4) (outerRadius A) := by
  constructor
  · rintro ⟨q, hq, he⟩
    have hqA := (closedBall_subset_closedBall (outerRadius_lt A).le) hq.2
    have hpair : (q.1, (⟨q.2, hqA⟩ : closedBall (0 : Vector 4) A.radius)) =
        (s, ⟨v, hv⟩) := A.tube_embedded.injective he
    have hval := congrArg (fun p : Sphere 3 × closedBall (0 : Vector 4) A.radius ↦ p.2.val)
      hpair
    change q.2 = v at hval
    exact hval ▸ hq.2
  · intro h
    exact ⟨(s, v), ⟨mem_univ _, h⟩, rfl⟩

theorem tube_mem_retainedExterior_iff (s : Sphere 3) {v : Vector 4}
    (hv : v ∈ closedBall (0 : Vector 4) A.radius) :
    A.tube (s, v) ∈ retainedExterior A ↔ outerRadius A < ‖v‖ := by
  change A.tube (s, v) ∉ outerTubeImage A ↔ _
  rw [tube_mem_outer_iff A s hv, mem_closedBall, dist_zero_right, not_le]

theorem outerRadius_lt_graphRadius_iff (u : ℝ) :
    outerRadius A < graphRadius (bump A) (UnroundedTrace.handleRadius A) u ↔
      2 * (bump A).rOut < u := by
  rw [← graphRadial_lt_neg_twice_outer_iff (bump A) u]
  have hR := outerRadius_sq A
  have hr := graphRadius_sq (bump A) (UnroundedTrace.handleRadius A) u
  have hR0 := outerRadius_nonneg A
  have hr0 := graphRadius_pos (bump A) (UnroundedTrace.handleRadius_pos A) u
  constructor
  · intro h
    nlinarith
  · intro h
    by_contra hn
    have hle := le_of_not_gt hn
    nlinarith

theorem collar_tube_mem_retainedExterior_iff (p : boundaryCollarParameters A) :
    A.tube (collarZeroPoint (bump A) (UnroundedTrace.handleRadius A) p.val).1 ∈
      retainedExterior A ↔ 2 * (bump A).rOut < p.val.2.2 := by
  have hp := (mem_boundaryCollarParameters_iff A p.val).mp p.property
  have hv : (zeroPoint (bump A) (UnroundedTrace.handleRadius A) p.val.2).1 ∈
      closedBall (0 : Vector 4) A.radius := by
    rw [mem_closedBall, dist_zero_right, norm_zeroPoint_fst]
    exact hp.1.le
  change A.tube (p.val.1, (zeroPoint (bump A) (UnroundedTrace.handleRadius A) p.val.2).1) ∈
    retainedExterior A ↔ _
  rw [tube_mem_retainedExterior_iff A p.val.1 hv, norm_zeroPoint_fst,
    outerRadius_lt_graphRadius_iff]

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace
