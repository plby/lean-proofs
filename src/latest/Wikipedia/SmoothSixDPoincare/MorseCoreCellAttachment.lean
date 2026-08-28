import Wikipedia.SmoothSixDPoincare.ClosedHandleCore
import Wikipedia.SmoothSixDPoincare.TransportedMorseAttachment

/-!
# The actual Morse surgery as a core-cell attachment up to homotopy

The full handle collapses onto its negative core relative to the original
lower sublevel. The core boundary is the original attaching sphere. Compose
this inclusion homotopy equivalence with the same original whole-attachment
homeomorphism to obtain the upper sublevel's core-cell presentation.

The forward map into the upper sublevel is the attachment realization; it
is not asserted to be the literal ambient inclusion of the lower sublevel.
-/

noncomputable section

open Set Metric Function Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

open Classical in
def coreMap : C(MorseHandle.UnitDisk d.chart.NegativeCoordinates, M) :=
  HandleCoreAttachment.core d.handleMap

open Classical in
theorem coreMap_boundary (u : PuncturedHandle.UnitSphere d.chart.NegativeCoordinates) :
    d.coreMap ⟨u, sphere_subset_closedBall u.property⟩ = (d.surgery.attachingSphere u : M) :=
  d.handleMap_core u

open Classical in
theorem coreMap_lower_iff (u : MorseHandle.UnitDisk d.chart.NegativeCoordinates) :
    f (d.coreMap u) ≤ f p - d.radius ^ 2 ↔ ‖(u : d.chart.NegativeCoordinates)‖ = 1 :=
  d.chart.attachingHandleMap_lower_iff d.radius d.radius_pos d.block (u, ⟨0, by simp⟩)

variable [T2Space M]

open Classical in
theorem coreMap_isClosedEmbedding : IsClosedEmbedding d.coreMap := by
  apply d.coreMap.continuous.isClosedEmbedding
  intro x y hxy
  have heq := (d.chart.attachingHandleMap_isClosedEmbedding d.radius d.radius_pos d.block).injective
    hxy
  exact congrArg Prod.fst heq

open Classical in
/-- The core and old lower sublevel include into the original full attachment by a homotopy
equivalence, followed by the original attachment realization in the upper sublevel. -/
def coreUnionHomotopyEquiv (hf : Continuous f) :
    ↥({y : M | f y ≤ f p - d.radius ^ 2} ∪ range d.coreMap) ≃ₕ
      {y : M // f y ≤ f p + d.radius ^ 2} :=
  (ClosedHandleCore.unionHomotopyEquiv {y : M | f y ≤ f p - d.radius ^ 2} d.handleMap
    (isClosed_le hf continuous_const)
    (d.chart.attachingHandleMap_isClosedEmbedding d.radius d.radius_pos d.block)
    (d.chart.attachingHandleMap_lower_iff d.radius d.radius_pos d.block)).trans
      d.attachmentHomeomorph.toHomotopyEquiv

open Classical in
theorem coreUnionHomotopyEquiv_apply (hf : Continuous f)
    (x : ↥({y : M | f y ≤ f p - d.radius ^ 2} ∪ range d.coreMap)) :
    d.coreUnionHomotopyEquiv hf x = d.attachmentHomeomorph
      ⟨x.val, ClosedHandleCore.core_subset _ d.handleMap x.property⟩ := rfl

variable [CompactSpace M]

open Classical in
/-- Attach a single negative-coordinate disk by its original sphere map, obtaining the
actual upper sublevel up to homotopy. No cellular presentation is assumed. -/
def coreAttachmentHomotopyEquiv (hf : Continuous f) :
    ClosedAttachment.Space {y : M | f y ≤ f p - d.radius ^ 2}
      {u : MorseHandle.UnitDisk d.chart.NegativeCoordinates |
        ‖(u : d.chart.NegativeCoordinates)‖ = 1} d.coreMap ≃ₕ
      {y : M // f y ≤ f p + d.radius ^ 2} :=
  (ClosedHandleCore.coreQuotientHomeomorph {y : M | f y ≤ f p - d.radius ^ 2} d.handleMap
    (d.chart.attachingHandleMap_isClosedEmbedding d.radius d.radius_pos d.block)
    (d.chart.attachingHandleMap_lower_iff d.radius d.radius_pos d.block)
    (isClosed_le hf continuous_const).isCompact).toHomotopyEquiv.trans
      (d.coreUnionHomotopyEquiv hf)

open Classical in
theorem coreAttachmentHomotopyEquiv_old (hf : Continuous f)
    (x : {y : M // f y ≤ f p - d.radius ^ 2}) :
    d.coreAttachmentHomotopyEquiv hf (Quot.mk _ (.inl x)) =
      d.attachmentHomeomorph ⟨x.val, Or.inl x.property⟩ := rfl

open Classical in
theorem coreAttachmentHomotopyEquiv_core (hf : Continuous f)
    (u : MorseHandle.UnitDisk d.chart.NegativeCoordinates) :
    d.coreAttachmentHomotopyEquiv hf (Quot.mk _ (.inr u)) =
      d.attachmentHomeomorph ⟨d.coreMap u, Or.inr ⟨(u, ⟨0, by simp⟩), rfl⟩⟩ := rfl

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
