import Wikipedia.SmoothSixDPoincare.NativeZeroIndexAttachment
import Wikipedia.SmoothSixDPoincare.ZeroIndexBoundaryPair

/-!
# The zero-index disk birth retains its actual boundary inclusion

The old level plus the new positive-coordinate sphere is the original
upper level. Its two maps commute exactly with the constructed disjoint
disk-birth homeomorphism of the actual sublevels.
-/

noncomputable section

open Set Function Topology Metric
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

open Classical in
def zeroIndexBoundaryHomeomorph
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 0) :
    (d.LowerLevel ⊕ PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) ≃ₜ d.UpperLevel := by
  let _ : Subsingleton d.chart.NegativeCoordinates := Module.finrank_zero_iff.mp hindex
  exact d.surgery.zeroIndexBoundaryHomeomorph

open Classical in
theorem zeroIndexBoundaryHomeomorph_belt
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 0)
    (v : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.zeroIndexBoundaryHomeomorph hindex (Sum.inr v) = d.surgery.beltSphere v := rfl

variable [T2Space M] [CompactSpace M]

open Classical in
theorem zeroIndexBoundaryHomeomorph_old_body (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 0) (x : d.LowerLevel) :
    (d.zeroIndexBoundaryHomeomorph hindex (Sum.inl x)).val =
      (d.zeroIndexSublevelHomeomorph hf hindex (Sum.inl ⟨x.val, x.property.le⟩)).val := by
  let _ : Subsingleton d.chart.NegativeCoordinates := Module.finrank_zero_iff.mp hindex
  obtain ⟨r, rfl⟩ := d.surgery.zeroIndex_oldExterior_surjective x
  have hboundary := congrArg (fun y : d.UpperLevel => y.val)
    (d.surgery.zeroIndexBoundaryHomeomorph_old r)
  have hbody := congrArg
    (fun y : {x : M // f x ≤ f p + d.radius ^ 2} => y.val)
    (d.zeroIndexSublevelHomeomorph_old hf hindex
      ⟨(d.surgery.oldExterior r).val, (d.surgery.oldExterior r).property.le⟩)
  apply hboundary.trans
  apply (d.newExterior_eq r).trans
  apply Eq.trans _ hbody.symm
  apply congrArg (fun z => (d.attachmentHomeomorph z).val)
  exact Subtype.ext (d.oldExterior_eq r).symm

open Classical in
theorem zeroIndexBoundaryHomeomorph_disk_body (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 0)
    (v : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    (d.zeroIndexBoundaryHomeomorph hindex (Sum.inr v)).val =
      (d.zeroIndexSublevelHomeomorph hf hindex
        (Sum.inr ⟨v.val, sphere_subset_closedBall v.property⟩)).val := by
  rw [d.zeroIndexBoundaryHomeomorph_belt, d.zeroIndexSublevelHomeomorph_disk]
  exact d.newPiece_eq (PuncturedHandle.ballZero, v)

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
