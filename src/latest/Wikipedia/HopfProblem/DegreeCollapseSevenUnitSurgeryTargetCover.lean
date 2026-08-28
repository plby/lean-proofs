import Wikipedia.HopfProblem.DegreeCollapseSevenUnitSurgeryRadialCover

/-! # The three rounded-end maps cover the actual canonical surgery target -/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel SevenRoundedHandleCorner RoundedTrace
open Wikipedia.SmoothSixDPoincare

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [T2Space M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2)

theorem oldPoint_cover (q : OldPatch A hR) :
    FramedSurgery.oldMap (E := Vector 4) (face A hR) 3 q ∈
      range (exteriorMap A hR) ∪ range (handleMap A hR) ∪ range (collarMap A hR) := by
  by_cases hext : q.val ∈ retainedExterior A
  · exact Or.inl (Or.inl ⟨⟨q.val, hext⟩, rfl⟩)
  · have hout : q.val ∈ outerTubeImage A := by
      change ¬ q.val ∉ outerTubeImage A at hext
      exact not_not.mp hext
    obtain ⟨⟨s, v⟩, hv, he⟩ := hout
    have hvA : v ∈ closedBall (0 : Vector 4) A.radius :=
      (closedBall_subset_closedBall (outerRadius_lt A).le) hv.2
    have hne : v ≠ 0 := by
      intro hz
      apply q.property
      change q.val ∈ range (FramedSurgery.coreMap (E := Vector 4) (face A hR))
      rw [range_face_coreMap A hR, ← he]
      exact (tube_mem_core_iff A s hvA).mpr hz
    have hq : oldTubePoint A hR s hvA hne = q := Subtype.ext he
    rw [← hq]
    by_cases hlo : ‖v‖ < handleCoreRadius A
    · exact Or.inl (Or.inr (oldTubeMap_mem_handle A hR s hvA hne hlo))
    · have hhi : ‖v‖ < A.radius :=
        (mem_closedBall_zero_iff.mp hv.2).trans_lt (outerRadius_lt A)
      refine Or.inr ⟨collarParametersOfRadius A hR s
        (SphereRadialRetraction.retract (pole 3) v) ‖v‖ (le_of_not_gt hlo) hhi, ?_⟩
      exact congrArg (FramedSurgery.oldMap (E := Vector 4) (face A hR) 3)
        (collarPoint_ofTube A hR s hvA hne (le_of_not_gt hlo) hhi)

theorem newPoint_cover (q : FramedSurgery.NewPatch (Vector 4) (Vector 4)) :
    FramedSurgery.newMap (E := Vector 4) (face A hR) 3 q ∈
      range (handleMap A hR) ∪ range (collarMap A hR) := by
  by_cases hlo : ‖q.1.val‖ < handleCoreRadius A
  · refine Or.inl ⟨⟨(q.1.val, q.2), (mem_boundaryHandleParameters_iff A _).mpr ?_⟩, rfl⟩
    exact mem_ball_zero_iff.mpr hlo
  · exact Or.inr (newPoint_mem_collar A hR q (le_of_not_gt hlo))

theorem target_cover (q : Target A hR) :
    q ∈ range (exteriorMap A hR) ∪ range (handleMap A hR) ∪ range (collarMap A hR) := by
  rcases FramedSurgery.cover (E := Vector 4) (face A hR) 3 q with
    ⟨x, rfl⟩ | ⟨x, rfl⟩
  · exact oldPoint_cover A hR x
  · rcases newPoint_cover A hR x with h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery
