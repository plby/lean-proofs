import Wikipedia.SmoothSixDPoincare.EmptyFaceAttachment
import Wikipedia.SmoothSixDPoincare.MorseFaceAttachment

/-!
# An actual zero-index Morse step is a disjoint disk birth

Zero negative rank makes the original attaching face empty. The existing
whole-attachment realization therefore identifies the actual upper sublevel
with the lower sublevel plus one standard positive-coordinate disk. The
formulas retain the original old-sublevel and whole-handle maps.
-/

noncomputable section

open Set Function Topology Metric
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

open Classical in
theorem isEmpty_handleFace_of_index_zero
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 0) : IsEmpty d.handleFace := by
  let _ : Subsingleton d.chart.NegativeCoordinates := Module.finrank_zero_iff.mp hindex
  refine ⟨fun z => ?_⟩
  have hz : ‖z.val.1.val‖ = 1 := z.property
  rw [Subsingleton.elim z.val.1.val 0, norm_zero] at hz
  exact zero_ne_one hz

open Classical in
def zeroIndexHandleCoordinates
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 0) :
    d.HandleDomain ≃ₜ MorseHandle.UnitDisk d.chart.PositiveCoordinates := by
  let _ : Subsingleton d.chart.NegativeCoordinates := Module.finrank_zero_iff.mp hindex
  exact {
    toFun := Prod.snd
    invFun := fun v => (⟨0, by simp⟩, v)
    left_inv := fun z => Prod.ext (Subsingleton.elim _ _) rfl
    right_inv := fun _ => rfl
    continuous_toFun := continuous_snd
    continuous_invFun := continuous_const.prodMk continuous_id }

open Classical in
theorem zeroIndexHandleCoordinates_apply
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 0) (z : d.HandleDomain) :
    d.zeroIndexHandleCoordinates hindex z = z.2 := rfl

open Classical in
theorem zeroIndexHandleCoordinates_symm
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 0)
    (v : MorseHandle.UnitDisk d.chart.PositiveCoordinates) :
    (d.zeroIndexHandleCoordinates hindex).symm v = (⟨0, by simp⟩, v) := rfl

variable [T2Space M] [CompactSpace M]

open Classical in
def zeroIndexSublevelHomeomorph (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 0) :
    ({y : M // f y ≤ f p - d.radius ^ 2} ⊕ MorseHandle.UnitDisk d.chart.PositiveCoordinates) ≃ₜ
      {y : M // f y ≤ f p + d.radius ^ 2} := by
  let _ := d.isEmpty_handleFace_of_index_zero hindex
  exact ((Homeomorph.refl {y : M // f y ≤ f p - d.radius ^ 2}).sumCongr
    (d.zeroIndexHandleCoordinates hindex).symm).trans
      ((FaceAttachment.emptyFaceHomeomorph d.handleFaceToSublevel).symm.trans
        (d.faceAttachmentRealization hf))

open Classical in
theorem zeroIndexSublevelHomeomorph_old (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 0)
    (x : {y : M // f y ≤ f p - d.radius ^ 2}) :
    d.zeroIndexSublevelHomeomorph hf hindex (Sum.inl x) =
      d.attachmentHomeomorph ⟨x.val, Or.inl x.property⟩ := rfl

open Classical in
theorem zeroIndexSublevelHomeomorph_disk (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 0)
    (v : MorseHandle.UnitDisk d.chart.PositiveCoordinates) :
    d.zeroIndexSublevelHomeomorph hf hindex (Sum.inr v) =
      d.attachmentHomeomorph ⟨d.handleMap (⟨0, by simp⟩, v), Or.inr ⟨_, rfl⟩⟩ := rfl

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
