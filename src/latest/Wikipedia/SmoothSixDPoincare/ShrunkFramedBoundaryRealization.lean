import Wikipedia.SmoothSixDPoincare.ShrunkUpperBodyChange
import Wikipedia.SmoothSixDPoincare.NativeFramedBoundaryRealization

/-!
# Retain the constructed framed boundary under the original shrinking

The whole-body realization is exactly the shrunk native quotient
realization, not a separately chosen homeomorphism. Its boundary restriction
is the recorded shrunk boundary homeomorphism, with the original domain
and all of its framed coordinates unchanged.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData.ShrunkSurgeryRealization

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
  {d : MorseSurgeryData E f p} {s : ℝ} (R : d.ShrunkSurgeryRealization s)
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (m : ℕ)
  [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = m + 1)]

open Classical in
def framedBodyRealization :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    FramedSurgery.AttachedBody (d.attachingSmoothFace hf m) d.lowerBodyInclusion ≃ₜ
      {x : M // f x ≤ f p + d.radius ^ 2} :=
  (d.framedBodyRealization hf m).trans R.upperBodyChange

open Classical in
theorem framedBodyRealization_eq_quotient :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    R.framedBodyRealization hf m =
      (FaceAttachment.congrFaceMap (d.attachingSmoothFace_bodyFace hf m)).trans
        (R.faceQuotientRealization hf.continuous) := rfl

variable (n : ℕ) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]

def framedBoundaryRealization : d.FramedBoundary hf m n ≃ₜ d.UpperLevel :=
  (d.framedBoundaryRealization hf m n).trans R.boundaryHomeomorph

def framedBoundaryBodyMap : C(d.FramedBoundary hf m n,
    {x : M // f x ≤ f p + d.radius ^ 2}) :=
  ⟨fun z => R.upperBodyChange (d.framedBoundaryBodyMap hf m n z),
    R.upperBodyChange.continuous.comp (d.framedBoundaryBodyMap hf m n).continuous⟩

theorem framedBoundaryBodyMap_isClosedEmbedding :
    IsClosedEmbedding (R.framedBoundaryBodyMap hf m n) :=
  R.upperBodyChange.isClosedEmbedding.comp (d.framedBoundaryBodyMap_isClosedEmbedding hf m n)

theorem framedBoundary_realizations_agree (z : d.FramedBoundary hf m n) :
    (R.framedBoundaryBodyMap hf m n z).val = (R.framedBoundaryRealization hf m n z).val := by
  have he : d.framedBoundaryBodyMap hf m n z =
      ⟨(d.framedBoundaryRealization hf m n z).val,
        (d.framedBoundaryRealization hf m n z).property.le⟩ :=
    Subtype.ext (d.framedBoundary_realizations_agree hf m n z)
  change (R.upperBodyChange (d.framedBoundaryBodyMap hf m n z)).val = _
  rw [he]
  exact R.upperBodyChange_on_level (d.framedBoundaryRealization hf m n z)

theorem framedBoundaryBodyMap_range : range (R.framedBoundaryBodyMap hf m n) =
    {x : {x : M // f x ≤ f p + d.radius ^ 2} | f x.val = f p + d.radius ^ 2} := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    change f (R.framedBoundaryBodyMap hf m n z).val = _
    rw [R.framedBoundary_realizations_agree hf m n]
    exact (R.framedBoundaryRealization hf m n z).property
  · intro hx
    let y : d.UpperLevel := ⟨x.val, hx⟩
    refine ⟨(R.framedBoundaryRealization hf m n).symm y, Subtype.ext ?_⟩
    rw [R.framedBoundary_realizations_agree hf m n, Homeomorph.apply_symm_apply]

open Classical in
theorem framedBoundaryBodyMap_eq_wholeRealization (z : d.FramedBoundary hf m n) :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI : CompactSpace d.LowerLevel :=
      isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
    letI : CompactSpace {x : M // f x ≤ f p - d.radius ^ 2} :=
      isCompact_iff_compactSpace.mp (isClosed_le hf.continuous continuous_const).isCompact
    R.framedBoundaryBodyMap hf m n z = R.framedBodyRealization hf m
      (FramedSurgery.boundaryBodyMap (d.attachingSmoothFace hf m) d.lowerBodyInclusion n
        (d.lowerBodyInclusion_isClosedEmbedding hf) z) := rfl

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData.ShrunkSurgeryRealization
