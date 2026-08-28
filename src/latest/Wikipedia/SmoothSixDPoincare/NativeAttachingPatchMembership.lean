import Wikipedia.SmoothSixDPoincare.NativeFramedBoundaryRealization
import Wikipedia.SmoothSixDPoincare.FramedSurgeryBoundaryUpdate

/-!
# Detect the original attaching face and its core in the full native neighborhood

Injectivity of the original attaching-neighborhood homeomorphism identifies
the entire framed face by its exact product coordinates. The open face is
the strict unit normal disk and the removed core is its zero section.
-/

noncomputable section

open Set Function Topology Metric
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

open PuncturedHandle FramedSurgery

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (m : ℕ)
  [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = m + 1)]

open Classical in
theorem attachingNeighborhood_eq_face_iff :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    ∀ (z : d.chart.attachingSource d.radius d.radius_pos)
      (q : UnitSphere d.chart.NegativeCoordinates ×
        MorseHandle.UnitDisk d.chart.PositiveCoordinates),
      (d.chart.attachingNeighborhoodHomeomorph d.radius d.radius_pos z).val =
        (d.attachingSmoothFace hf m).map q ↔ z.val = (q.1, q.2.val) := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  intro z q
  let w := d.chart.closedAttachingPoint d.radius d.radius_pos d.block q.1 q.2
  have hface : (d.chart.attachingNeighborhoodHomeomorph d.radius d.radius_pos w).val =
      (d.attachingSmoothFace hf m).map q :=
    Subtype.ext (d.chart.attachingNeighborhoodHomeomorph_face
      d.radius d.radius_pos d.block q.1 q.2)
  constructor
  · intro h
    have he : z = w := (d.chart.attachingNeighborhoodHomeomorph d.radius d.radius_pos).injective
      (Subtype.ext (h.trans hface.symm))
    exact congrArg (fun x : d.chart.attachingSource d.radius d.radius_pos => x.val) he
  · intro h
    exact (congrArg (fun x : d.chart.attachingSource d.radius d.radius_pos =>
      (d.chart.attachingNeighborhoodHomeomorph d.radius d.radius_pos x).val)
        (show z = w from Subtype.ext h)).trans hface

open Classical in
theorem attachingNeighborhood_mem_faceInterior_iff :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    ∀ z : d.chart.attachingSource d.radius d.radius_pos,
      (d.chart.attachingNeighborhoodHomeomorph d.radius d.radius_pos z).val ∈
        faceInterior (d.attachingSmoothFace hf m) ↔ ‖z.val.2‖ < 1 := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  intro z
  rw [faceInterior_eq_interiorImage]
  constructor
  · rintro ⟨q, hq, he⟩
    have hv := congrArg (fun w : UnitSphere d.chart.NegativeCoordinates ×
        d.chart.PositiveCoordinates => w.2)
      ((d.attachingNeighborhood_eq_face_iff hf m z q).mp he.symm)
    rw [hv]
    exact hq.2
  · intro hz
    let q : UnitSphere d.chart.NegativeCoordinates ×
        MorseHandle.UnitDisk d.chart.PositiveCoordinates :=
      (z.val.1, ⟨z.val.2, mem_closedBall_zero_iff.mpr hz.le⟩)
    exact ⟨q, ⟨mem_univ _, hz⟩, ((d.attachingNeighborhood_eq_face_iff hf m z q).mpr rfl).symm⟩

open Classical in
theorem attachingNeighborhood_mem_core_iff :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    ∀ z : d.chart.attachingSource d.radius d.radius_pos,
      (d.chart.attachingNeighborhoodHomeomorph d.radius d.radius_pos z).val ∈
        range (coreMap (d.attachingSmoothFace hf m)) ↔ z.val.2 = 0 := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  intro z
  constructor
  · rintro ⟨u, hu⟩
    exact congrArg (fun w : UnitSphere d.chart.NegativeCoordinates ×
        d.chart.PositiveCoordinates => w.2)
      ((d.attachingNeighborhood_eq_face_iff hf m z (u, ⟨0, by simp⟩)).mp hu.symm)
  · intro hz
    refine ⟨z.val.1, ?_⟩
    exact ((d.attachingNeighborhood_eq_face_iff hf m z (z.val.1, ⟨0, by simp⟩)).mpr
      (Prod.ext rfl hz)).symm

open Classical in
theorem attachingNeighborhood_mem_oldPatch_iff :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    ∀ z : d.chart.attachingSource d.radius d.radius_pos,
      (d.chart.attachingNeighborhoodHomeomorph d.radius d.radius_pos z).val ∈
        oldPatch (d.attachingSmoothFace hf m) ↔ z.val.2 ≠ 0 := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  intro z
  exact not_congr (d.attachingNeighborhood_mem_core_iff hf m z)

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
