import Wikipedia.SmoothSixDPoincare.NativeBeltFramedRealization

/-!
# The corrected native exterior retains the original model boundary orbits

Every constructed exterior point is a point of the recorded native
attachment frontier, including the corner. The corrected realization
therefore obeys the recorded quadratic boundary-orbit formula there.
-/

noncomputable section

open Set Function Topology Metric
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

open FramedSurgery

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (m : ℕ)
  [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = m + 1)]

open Classical in
omit [CompactSpace M] in
theorem framedExterior_mem_frontier :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    ∀ r : Exterior (d.attachingSmoothFace hf m), r.val.val ∈
      frontier ({y : M | f y ≤ f p - d.radius ^ 2} ∪
        range (d.chart.attachingHandleMap d.radius d.radius_pos d.block)) := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  intro r
  let r₀ := presentationExteriorCoordinates (d.attachingSmoothFace hf m)
    d.surgery (d.attachingSmoothFace_oldPiece hf m) r
  have he : r₀.val = r.val.val := (d.oldExterior_eq r₀).symm.trans
    (congrArg (fun x : d.LowerLevel => x.val)
      (presentationExteriorCoordinates_point (d.attachingSmoothFace hf m)
        d.surgery (d.attachingSmoothFace_oldPiece hf m) r))
  have hfront : r.val.val ∈ frontier ({y : M | f y ≤ f p - d.radius ^ 2} ∪
      range (d.chart.normHandleMap d.radius d.radius_pos d.block)) := he ▸ r₀.property.2
  rw [d.chart.range_normHandleMap d.radius d.radius_pos d.block] at hfront
  exact hfront

variable (n : ℕ) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]

open Classical in
theorem framedBoundaryRealization_exterior_attachment :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    ∀ r : Exterior (d.attachingSmoothFace hf m),
      (d.framedBoundaryRealization hf m n (exteriorNewMap (d.attachingSmoothFace hf m) n r)).val =
      (d.attachmentHomeomorph ⟨r.val.val, Or.inl r.val.property.le⟩).val := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ : CompactSpace d.LowerLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  intro r
  let r₀ := presentationExteriorCoordinates (d.attachingSmoothFace hf m)
    d.surgery (d.attachingSmoothFace_oldPiece hf m) r
  have he : r₀.val = r.val.val := (d.oldExterior_eq r₀).symm.trans
    (congrArg (fun x : d.LowerLevel => x.val)
      (presentationExteriorCoordinates_point (d.attachingSmoothFace hf m)
        d.surgery (d.attachingSmoothFace_oldPiece hf m) r))
  have h₁ := congrArg (fun x : d.UpperLevel => x.val)
    (presentationBoundaryHomeomorph_exterior (d.attachingSmoothFace hf m)
      d.surgery (d.attachingSmoothFace_oldPiece hf m) n r)
  exact h₁.trans ((d.newExterior_eq r₀).trans
    (congrArg (fun x => (d.attachmentHomeomorph x).val) (Subtype.ext he)))

open Classical in
theorem beltFramedBoundaryRealization_exterior_model :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    ∀ (r : Exterior (d.attachingSmoothFace hf m))
      (_hsource : r.val.val ∈ d.chart.splitChart.source) (t : ℝ), t ≤ 0 →
      (∀ s ∈ uIcc 0 t, MorseHandle.descentFlow s (d.chart.splitChart r.val.val) ∈
        closedBall (0 : d.chart.NegativeCoordinates) (2 * d.radius) ×ˢ
          closedBall (0 : d.chart.PositiveCoordinates) (2 * d.radius)) →
      f (d.chart.splitChart.symm
        (MorseHandle.descentFlow t (d.chart.splitChart r.val.val))) = f p + d.radius ^ 2 →
      (d.beltFramedBoundaryRealization hf m n
        (exteriorNewMap (d.attachingSmoothFace hf m) n r)).val =
        d.chart.splitChart.symm (MorseHandle.descentFlow t (d.chart.splitChart r.val.val)) := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  intro r hsource t ht hpath hlevel
  have horbit := d.attachment_model_orbits ⟨r.val.val, Or.inl r.val.property.le⟩
    (d.framedExterior_mem_frontier hf m r) hsource t ht hpath hlevel
  exact (congrArg (fun x : d.UpperLevel => x.val)
    (d.beltFramedBoundaryRealization_exterior hf m n r)).trans
      ((d.framedBoundaryRealization_exterior_attachment hf m n r).trans horbit)

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
