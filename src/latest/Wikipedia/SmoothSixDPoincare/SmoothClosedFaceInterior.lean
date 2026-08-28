import Wikipedia.SmoothSixDPoincare.SmoothClosedFace

/-!
# The open interior of a full framed face is determined by its closed point map

The chart image of the open normal disk equals the image of those same
coordinates under the closed-face map. Restricting or retaining the full
framed neighborhood does not introduce a different removed region.
-/

noncomputable section

open Set Function Topology Metric
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SmoothClosedFace

variable {E H F K B N X : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  [TopologicalSpace B] [ChartedSpace H B]
  [NormedAddCommGroup N] [NormedSpace ℝ N]
  [TopologicalSpace X] [ChartedSpace K X]
  (C : SmoothClosedFace I J B N X)

def interiorImage : Set X := C.map ''
  ((univ : Set B) ×ˢ {v : MorseHandle.UnitDisk N | ‖v.val‖ < 1})

theorem interiorImage_eq_chart :
    C.interiorImage = C.chart '' ((univ : Set B) ×ˢ ball (0 : N) 1) := by
  ext x
  constructor
  · rintro ⟨⟨u, v⟩, ⟨_, hv⟩, rfl⟩
    exact ⟨(u, v.val), ⟨mem_univ _, mem_ball_zero_iff.mpr hv⟩, C.point u v⟩
  · rintro ⟨⟨u, v⟩, ⟨_, hv⟩, rfl⟩
    exact ⟨(u, ⟨v, ball_subset_closedBall hv⟩),
      ⟨mem_univ _, mem_ball_zero_iff.mp hv⟩,
      (C.point u ⟨v, ball_subset_closedBall hv⟩).symm⟩

theorem isOpen_interiorImage : IsOpen C.interiorImage := by
  rw [C.interiorImage_eq_chart]
  apply C.chart.toOpenPartialHomeomorph.isOpen_image_of_subset_source
    (isOpen_univ.prod isOpen_ball)
  exact fun _ hz => C.source ⟨hz.1, ball_subset_closedBall hz.2⟩

theorem interiorImage_subset_range : C.interiorImage ⊆ range C.map := image_subset_range _ _

theorem map_mem_interiorImage_iff (p : B × MorseHandle.UnitDisk N) :
    C.map p ∈ C.interiorImage ↔ ‖p.2.val‖ < 1 := by
  constructor
  · rintro ⟨q, ⟨_, hq⟩, he⟩
    exact C.closedEmbedding.injective he ▸ hq
  · intro hp
    exact ⟨p, ⟨mem_univ _, hp⟩, rfl⟩

end Wikipedia.SmoothSixDPoincare.SmoothClosedFace
