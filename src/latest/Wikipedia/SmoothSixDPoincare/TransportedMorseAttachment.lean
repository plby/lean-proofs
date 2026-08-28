import Wikipedia.SmoothSixDPoincare.AttachmentChangeOfCoordinates
import Wikipedia.SmoothSixDPoincare.SmoothMorseSurgery

/-!
# Transporting the whole realized Morse handle attachment

The surgery record retains the constructed homeomorphism onto its actual
upper sublevel. Changing ambient coordinates transports the full embedded
handle and its attaching face, and yields a homeomorphic realization of the
changed attachment. The original handle parametrization is retained exactly.
-/

noncomputable section

open Set Metric Function Topology
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

open Classical in
abbrev HandleDomain := MorseHandle.UnitDisk d.chart.NegativeCoordinates ×
  MorseHandle.UnitDisk d.chart.PositiveCoordinates

open Classical in
def handleFace : Set d.HandleDomain := {z | ‖(z.1 : d.chart.NegativeCoordinates)‖ = 1}

open Classical in
def handleMap : C(d.HandleDomain, M) :=
  d.chart.attachingHandleMap d.radius d.radius_pos d.block

open Classical in
def handleFacePoint (u : PuncturedHandle.UnitSphere d.chart.NegativeCoordinates)
    (v : MorseHandle.UnitDisk d.chart.PositiveCoordinates) : d.HandleDomain :=
  (⟨u, sphere_subset_closedBall u.property⟩, v)

open Classical in
def attachingFace :
    C(PuncturedHandle.UnitSphere d.chart.NegativeCoordinates ×
      MorseHandle.UnitDisk d.chart.PositiveCoordinates, d.LowerLevel) :=
  d.chart.attachingBoundaryMap d.radius d.radius_pos d.block

open Classical in
theorem handleMap_face (u : PuncturedHandle.UnitSphere d.chart.NegativeCoordinates)
    (v : MorseHandle.UnitDisk d.chart.PositiveCoordinates) :
    d.handleMap (d.handleFacePoint u v) = (d.attachingFace (u, v) : M) := rfl

open Classical in
theorem handleMap_core (u : PuncturedHandle.UnitSphere d.chart.NegativeCoordinates) :
    d.handleMap (d.handleFacePoint u ⟨0, by simp⟩) = (d.surgery.attachingSphere u : M) := by
  rw [d.attaching_eq]
  rfl

open Classical in
def transportedHandle (T : M ≃ₜ M) : C(d.HandleDomain, M) :=
  ⟨T ∘ d.handleMap, T.continuous.comp d.handleMap.continuous⟩

open Classical in
theorem transportedHandle_isClosedEmbedding [T2Space M] (T : M ≃ₜ M) :
    IsClosedEmbedding (d.transportedHandle T) :=
  T.isClosedEmbedding.comp (d.chart.attachingHandleMap_isClosedEmbedding
    d.radius d.radius_pos d.block)

open Classical in
theorem attachingFace_injective [T2Space M] : Injective d.attachingFace := by
  intro x y hxy
  have hraw := congrArg (fun z : d.LowerLevel => (z : M)) hxy
  have hhandle : d.handleFacePoint x.1 x.2 = d.handleFacePoint y.1 y.2 :=
    (d.chart.attachingHandleMap_isClosedEmbedding d.radius d.radius_pos d.block).injective hraw
  exact Prod.ext (Subtype.ext (congrArg
    (fun z : d.HandleDomain => (z.1 : d.chart.NegativeCoordinates)) hhandle))
      (congrArg (fun z : d.HandleDomain => z.2) hhandle)

open Classical in
/-- The transported handle meets the new lower sublevel in exactly its whole negative face. -/
theorem transportedHandle_lower_iff (T : M ≃ₜ M) {a : ℝ}
    (hA : ∀ y, f y ≤ f p - d.radius ^ 2 ↔ f (T y) ≤ a) (z : d.HandleDomain) :
    f (d.transportedHandle T z) ≤ a ↔ z ∈ d.handleFace :=
  (hA (d.handleMap z)).symm.trans
    (d.chart.attachingHandleMap_lower_iff d.radius d.radius_pos d.block z)

variable [T2Space M] [CompactSpace M]

open Classical in
/-- The actual upper sublevel is the quotient with the original full attaching face. -/
def attachmentQuotientHomeomorph (hf : Continuous f) :
    ClosedAttachment.Space {y : M | f y ≤ f p - d.radius ^ 2} d.handleFace d.handleMap ≃ₜ
      {y : M // f y ≤ f p + d.radius ^ 2} :=
  (d.chart.attachingHandleUnionHomeomorph hf d.radius d.radius_pos d.block).trans
    d.attachmentHomeomorph

open Classical in
/-- The changed full attachment still realizes the original upper sublevel. -/
def transportedAttachmentHomeomorph (hf : Continuous f) (T : M ≃ₜ M) {a : ℝ}
    (hA : ∀ y, f y ≤ f p - d.radius ^ 2 ↔ f (T y) ≤ a) :
    ClosedAttachment.Space {y : M | f y ≤ a} d.handleFace (d.transportedHandle T) ≃ₜ
      {y : M // f y ≤ f p + d.radius ^ 2} :=
  ClosedAttachment.changedRealization T hA (fun _ _ => rfl) (d.attachmentQuotientHomeomorph hf)

open Classical in
/-- Every new handle coordinate is sent to its original point in the actual upper sublevel. -/
theorem transportedAttachmentHomeomorph_handle (hf : Continuous f) (T : M ≃ₜ M) {a : ℝ}
    (hA : ∀ y, f y ≤ f p - d.radius ^ 2 ↔ f (T y) ≤ a) (z : d.HandleDomain) :
    d.transportedAttachmentHomeomorph hf T hA (Quot.mk _ (Sum.inr z)) =
      d.attachmentHomeomorph ⟨d.handleMap z, Or.inr ⟨z, rfl⟩⟩ :=
  ClosedAttachment.changedRealization_inr T hA (fun _ _ => rfl)
    (d.attachmentQuotientHomeomorph hf) z

open Classical in
/-- The concrete union with the transported embedded handle is homeomorphic
to the upper sublevel. -/
def transportedUnionHomeomorph (hf : Continuous f) (T : M ≃ₜ M) {a : ℝ}
    (hA : ∀ y, f y ≤ f p - d.radius ^ 2 ↔ f (T y) ≤ a) :
    ↥({y : M | f y ≤ a} ∪ range (d.transportedHandle T)) ≃ₜ
      {y : M // f y ≤ f p + d.radius ^ 2} :=
  (ClosedAttachment.unionHomeomorph _ _ _ (isClosed_le hf continuous_const).isCompact
    (d.transportedHandle_isClosedEmbedding T).injective
    (d.transportedHandle_lower_iff T hA)).symm.trans
      (d.transportedAttachmentHomeomorph hf T hA)

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
