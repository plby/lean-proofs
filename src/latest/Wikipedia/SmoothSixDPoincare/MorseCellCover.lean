import Wikipedia.SmoothSixDPoincare.MorseCoreCellAttachment
import Wikipedia.SmoothSixDPoincare.CellCoverHomotopy

/-!
# The constructed cell cover for each original Morse surgery

The cover is constructed on the actual lower-sublevel/core union. Its old
space is the original lower sublevel, and its attaching map is the original
Morse attaching sphere. The comparison to the upper sublevel is the same
whole-attachment realization already retained by the surgery data.
-/

noncomputable section

open Set Metric Function Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

open Classical in
def coreCellPresentation (hf : Continuous f) :
    EmbeddedCellAttachment d.chart.NegativeCoordinates
      ↥({y : M | f y ≤ f p - d.radius ^ 2} ∪ range d.coreMap) :=
  EmbeddedCellAttachment.ofUnion _ d.coreMap (isClosed_le hf continuous_const)
    d.coreMap_isClosedEmbedding d.coreMap_lower_iff

open Classical in
def cellOldHomeomorph (hf : Continuous f) :
    {y : M // f y ≤ f p - d.radius ^ 2} ≃ₜ (d.coreCellPresentation hf).old where
  toFun x := ⟨⟨x.val, Or.inl x.property⟩, x.property⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

open Classical in
def coreBoundaryMap : C(sphere (0 : d.chart.NegativeCoordinates) 1,
    {y : M // f y ≤ f p - d.radius ^ 2}) :=
  (⟨Set.inclusion (fun _ hx => hx.le), continuous_inclusion _⟩ :
    C(d.LowerLevel, {y : M // f y ≤ f p - d.radius ^ 2})).comp d.surgery.attachingSphere

open Classical in
theorem coreCell_attaching_eq (hf : Continuous f) :
    (d.coreCellPresentation hf).attachingSphere =
      (d.cellOldHomeomorph hf).toHomotopyEquiv.toFun.comp d.coreBoundaryMap := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  apply Subtype.ext
  exact d.coreMap_boundary u

open Classical in
def realizedLowerInclusion :
    C({y : M // f y ≤ f p - d.radius ^ 2}, {y : M // f y ≤ f p + d.radius ^ 2}) :=
  ⟨fun x => d.attachmentHomeomorph ⟨x.val, Or.inl x.property⟩,
    d.attachmentHomeomorph.continuous.comp (continuous_inclusion (fun _ hx => Or.inl hx))⟩

open Classical in
theorem coreCell_old_realization (hf : Continuous f) :
    (d.coreUnionHomotopyEquiv hf).toFun.comp
      ((⟨Subtype.val, continuous_subtype_val⟩ :
        C((d.coreCellPresentation hf).old,
          ↥({y : M | f y ≤ f p - d.radius ^ 2} ∪ range d.coreMap))).comp
        (d.cellOldHomeomorph hf).toHomotopyEquiv.toFun) = d.realizedLowerInclusion := rfl

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
