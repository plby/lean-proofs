import Wikipedia.SmoothSixDPoincare.AttachmentOnePointCollapse
import Wikipedia.SmoothSixDPoincare.MorseCellCover

/-!
# The actual Morse attachment collapse and its belt fiber

The collapse is defined on the entire original upper sublevel using its
retained whole-attachment homeomorphism. Its restriction to the upper level
has the actual belt as its finite zero fiber. On the core-cell presentation
it is exactly the old-space collapse, not an unrelated local detector.
-/

noncomputable section

open Set Metric Function Topology ContinuousMap
open scoped OnePoint

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

open Classical in
def attachmentCollapseMap (hf : Continuous f) :
    C(↥({y : M | f y ≤ f p - d.radius ^ 2} ∪ range d.handleMap),
      OnePoint d.chart.NegativeCoordinates) :=
  ClosedHandleCore.collapseMap _ d.handleMap (isClosed_le hf continuous_const)
    (d.chart.attachingHandleMap_isClosedEmbedding d.radius d.radius_pos d.block)
    (d.chart.attachingHandleMap_lower_iff d.radius d.radius_pos d.block)

open Classical in
def upperCollapseMap (hf : Continuous f) :
    C({y : M // f y ≤ f p + d.radius ^ 2}, OnePoint d.chart.NegativeCoordinates) :=
  (d.attachmentCollapseMap hf).comp d.attachmentHomeomorph.symm.toHomotopyEquiv.toFun

open Classical in
theorem upperCollapse_realization (hf : Continuous f)
    (x : ↥({y : M | f y ≤ f p - d.radius ^ 2} ∪ range d.handleMap)) :
    d.upperCollapseMap hf (d.attachmentHomeomorph x) = d.attachmentCollapseMap hf x := by
  change d.attachmentCollapseMap hf (d.attachmentHomeomorph.symm (d.attachmentHomeomorph x)) = _
  exact congrArg (d.attachmentCollapseMap hf) (d.attachmentHomeomorph.symm_apply_apply x)

open Classical in
theorem upperCollapse_old (hf : Continuous f) (x : {y : M // f y ≤ f p - d.radius ^ 2}) :
    d.upperCollapseMap hf (d.realizedLowerInclusion x) = ∞ := by
  change d.upperCollapseMap hf (d.attachmentHomeomorph
    (ClosedHandleCore.oldInclusion _ d.handleMap x)) = ∞
  rw [d.upperCollapse_realization]
  exact ClosedHandleCore.collapseMap_old _ d.handleMap _ _ _ x

open Classical in
theorem upperCollapse_handle (hf : Continuous f) (z : d.HandleDomain) :
    d.upperCollapseMap hf (d.attachmentHomeomorph ⟨d.handleMap z, Or.inr ⟨z, rfl⟩⟩) =
      DiskOnePointCollapse.collapse z.1 := by
  exact (d.upperCollapse_realization hf
    (ClosedHandleCore.handleInclusion _ d.handleMap z)).trans
      (ClosedHandleCore.collapseMap_handle _ d.handleMap _ _ _ z)

open Classical in
def levelCollapseMap (hf : Continuous f) : C(d.UpperLevel, OnePoint d.chart.NegativeCoordinates) :=
  (d.upperCollapseMap hf).comp
    ⟨Set.inclusion (fun _ hx => hx.le), continuous_inclusion _⟩

open Classical in
theorem levelCollapse_realized (hf : Continuous f) (y : d.UpperLevel)
    (x : ↥({z : M | f z ≤ f p - d.radius ^ 2} ∪ range d.handleMap))
    (hy : (y : M) = (d.attachmentHomeomorph x).val) :
    d.levelCollapseMap hf y = d.attachmentCollapseMap hf x := by
  change d.upperCollapseMap hf ⟨y.val, y.property.le⟩ = _
  have heq : (⟨y.val, y.property.le⟩ : {z : M // f z ≤ f p + d.radius ^ 2}) =
      d.attachmentHomeomorph x := Subtype.ext hy
  rw [heq, d.upperCollapse_realization]

open Classical in
theorem levelCollapse_newExterior (hf : Continuous f) (r) :
    d.levelCollapseMap hf (d.surgery.newExterior r) = ∞ := by
  rw [d.levelCollapse_realized hf _ _ (d.newExterior_eq r)]
  exact ClosedHandleCore.collapseMap_old _ d.handleMap _ _ _ ⟨r.val, r.property.1.le⟩

open Classical in
theorem levelCollapse_newPiece (hf : Continuous f)
    (z : PuncturedHandle.UnitBall d.chart.NegativeCoordinates ×
      PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.levelCollapseMap hf (d.surgery.newPiece z) =
      DiskOnePointCollapse.collapse
        (MorseHandle.unitBallHomeomorph d.chart.NegativeCoordinates z.1) := by
  rw [d.levelCollapse_realized hf _ _ (d.newPiece_eq z)]
  exact ClosedHandleCore.collapseMap_handle _ d.handleMap _ _ _
    (d.chart.handleBallCoordinates (z.1, PuncturedHandle.sphereToBall z.2))

open Classical in
/-- The full actual belt, and no other upper-level point, maps to finite zero. -/
theorem levelCollapse_zero_iff (hf : Continuous f) (x : d.UpperLevel) :
    d.levelCollapseMap hf x = ((0 : d.chart.NegativeCoordinates) : OnePoint _) ↔
      x ∈ range d.surgery.beltSphere := by
  have hx : x ∈ range d.surgery.newExterior ∪ range d.surgery.newPiece := by
    rw [d.surgery.new_cover]
    trivial
  rcases hx with ⟨r, rfl⟩ | ⟨z, rfl⟩
  · rw [d.levelCollapse_newExterior]
    exact iff_of_false (OnePoint.infty_ne_coe _) (d.surgery.newExterior_avoids r)
  · rw [d.levelCollapse_newPiece, DiskOnePointCollapse.collapse_eq_zero_iff,
      d.surgery.newPiece_mem_belt_iff]
    rfl

open Classical in
/-- The whole-sublevel collapse restricts to the original cell-attachment collapse. -/
theorem upperCollapse_coreCell (hf : Continuous f) :
    (d.upperCollapseMap hf).comp (d.coreUnionHomotopyEquiv hf).toFun =
      (d.coreCellPresentation hf).collapseMap := by
  apply ContinuousMap.ext
  rintro ⟨x, hx | ⟨u, rfl⟩⟩
  · exact (d.upperCollapse_old hf ⟨x, hx⟩).trans
      ((d.coreCellPresentation hf).collapseMap_old ⟨⟨x, Or.inl hx⟩, hx⟩).symm
  · change d.upperCollapseMap hf
      (d.attachmentHomeomorph ⟨d.handleMap (u, ⟨0, by simp⟩), Or.inr ⟨_, rfl⟩⟩) =
      (d.coreCellPresentation hf).collapseMap ((d.coreCellPresentation hf).cell u)
    rw [d.upperCollapse_handle, (d.coreCellPresentation hf).collapseMap_cell]

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
