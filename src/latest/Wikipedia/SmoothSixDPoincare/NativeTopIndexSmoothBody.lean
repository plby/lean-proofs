import Wikipedia.SmoothSixDPoincare.NativeTopIndexAttachment
import Wikipedia.SmoothSixDPoincare.TopIndexOpenComponents
import Wikipedia.SmoothSixDPoincare.NativeOpenSurgeryExterior
import Wikipedia.SmoothSixDPoincare.NativeSmoothBoundaryBodies
import Wikipedia.SmoothSixDPoincare.SmoothBoundaryBodyCap
import Wikipedia.SmoothSixDPoincare.OpenDiffeomorphCongr
import Wikipedia.SmoothSixDPoincare.CommonBaseAttachmentRealization

/-!
# The native top-index step as an exact smooth-boundary disk cap

The cap uses the original attaching sphere and its whole negative disk.
Its boundary is the open complement of that sphere in the original lower
level. The native smooth common-exterior map identifies this boundary with
the original upper level and commutes with the whole-body realization.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)
  (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = Module.finrank ℝ E)

include hindex in
open Classical in
theorem topIndex_attaching_isOpen : IsOpen (range d.surgery.attachingSphere) := by
  let _ := d.subsingleton_positive_of_top_index hindex
  exact d.surgery.topIndex_attaching_isOpen

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

open Classical in
def topIndexCapBody : SmoothBoundaryBody 𝓘(ℝ, RegularLevel.Model E) :=
  (d.lowerSmoothBody hf).cap d.surgery.attachingSphere d.attaching_isClosedEmbedding
    (d.topIndex_attaching_isOpen hindex)

open Classical in
theorem topIndex_capFaceMap :
    (d.lowerSmoothBody hf).capFaceMap d.surgery.attachingSphere = d.capFaceToSublevel := by
  ext u
  apply Subtype.ext
  exact (d.capFaceToSublevel_attaching (DiskCap.boundaryCoordinates _ u)).symm

open Classical in
def topIndexCapBodyRealization :
    (d.topIndexCapBody hindex hf).body ≃ₜ (d.upperSmoothBody hf).body :=
  (FaceAttachment.congrFaceMap (d.topIndex_capFaceMap hf)).trans
    (d.topIndexCapRealization hf.continuous hindex)

open Classical in
theorem topIndexCapBodyRealization_old (x : (d.lowerSmoothBody hf).body) :
    d.topIndexCapBodyRealization hindex hf
        (FaceAttachment.oldMap ((d.lowerSmoothBody hf).capFaceMap d.surgery.attachingSphere) x) =
      d.attachmentHomeomorph ⟨x.val, Or.inl x.property⟩ := by
  change d.topIndexCapRealization hf.continuous hindex
    (FaceAttachment.congrFaceMap (d.topIndex_capFaceMap hf) _) = _
  exact (congrArg (d.topIndexCapRealization hf.continuous hindex)
    (FaceAttachment.congrFaceMap_old (d.topIndex_capFaceMap hf) x)).trans
      (d.topIndexCapRealization_old hf.continuous hindex x)

open Classical in
theorem topIndexCapBodyRealization_disk (u : MorseHandle.UnitDisk d.chart.NegativeCoordinates) :
    d.topIndexCapBodyRealization hindex hf
        (FaceAttachment.handleMap ((d.lowerSmoothBody hf).capFaceMap d.surgery.attachingSphere) u) =
      d.attachmentHomeomorph ⟨d.handleMap (u, ⟨0, by simp⟩), Or.inr ⟨_, rfl⟩⟩ := by
  change d.topIndexCapRealization hf.continuous hindex
    (FaceAttachment.congrFaceMap (d.topIndex_capFaceMap hf) _) = _
  exact (congrArg (d.topIndexCapRealization hf.continuous hindex)
    (FaceAttachment.congrFaceMap_handle (d.topIndex_capFaceMap hf) u)).trans
      (d.topIndexCapRealization_disk hf.continuous hindex u)

include hindex in
open Classical in
theorem topIndex_capBoundary :
    ((d.lowerSmoothBody hf).capBoundary d.surgery.attachingSphere
      d.attaching_isClosedEmbedding).carrier = (d.surgery.oldOpenExterior : Set d.LowerLevel) := by
  let _ := d.subsingleton_positive_of_top_index hindex
  exact d.surgery.topIndex_oldOpenExterior.symm

variable (hd : d.HasSmoothExterior hf)

open Classical in
def topIndexCapBoundaryDiffeomorph :
    Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
      (d.topIndexCapBody hindex hf).boundary (d.upperSmoothBody hf).boundary ∞ := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ := d.subsingleton_positive_of_top_index hindex
  let B : TopologicalSpace.Opens d.LowerLevel :=
    ⟨(range d.surgery.attachingSphere)ᶜ,
      d.attaching_isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let e := OpenDiffeomorph.setCongr (I := 𝓘(ℝ, RegularLevel.Model E))
    B d.surgery.oldOpenExterior (d.topIndex_capBoundary hindex hf)
  exact (e.trans (d.openExteriorDiffeomorph hf hd)).trans d.surgery.topIndexNewDiffeomorph.symm

open Classical in
theorem topIndexCapBoundaryDiffeomorph_point (x : (d.topIndexCapBody hindex hf).boundary) :
    (d.topIndexCapBoundaryDiffeomorph hindex hf hd x).val = d.exteriorForward x.val := by
  let _ := d.subsingleton_positive_of_top_index hindex
  have hy : x.val ∈ d.surgery.oldOpenExterior := by
    change x.val ∉ range d.surgery.oldPiece
    rw [d.surgery.topIndex_oldPiece_range]
    exact x.property
  let y : d.surgery.oldOpenExterior := ⟨x.val, hy⟩
  exact (d.exteriorForward_openExterior y).symm

open Classical in
def topIndexSmoothBodyEquiv :
    SmoothBoundaryBody.Equiv (d.topIndexCapBody hindex hf) (d.upperSmoothBody hf) := by
  refine {
    body := d.topIndexCapBodyRealization hindex hf
    boundary := d.topIndexCapBoundaryDiffeomorph hindex hf hd
    boundary_point := ?_ }
  intro x
  apply Subtype.ext
  have h := congrArg (fun y : (d.upperSmoothBody hf).body => y.val)
    (d.topIndexCapBodyRealization_old hindex hf ((d.lowerSmoothBody hf).inclusion x.val))
  exact h.trans (d.topIndexCapBoundaryDiffeomorph_point hindex hf hd x).symm

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
