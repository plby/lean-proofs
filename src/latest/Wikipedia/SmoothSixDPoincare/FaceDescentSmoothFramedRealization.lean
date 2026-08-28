import Wikipedia.SmoothSixDPoincare.ShrunkSmoothFramedRealization
import Wikipedia.SmoothSixDPoincare.FaceDescentSmoothExterior

/-!
# The exact smooth boundary realization after native face descent

Compose the belt-corrected native realization with the retained shrinking
and the actual inverse upper-level isotopy. The resulting boundary map
is a native diffeomorphism and is the restriction of the whole-body map.
Compared with the original face-descent realization, only the prescribed
negative-disk handle parameters change; the whole lower body is unchanged.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData.FaceDescent.Realization

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M} {d : MorseSurgeryData E f p}
  {hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f}
  {G H X N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {I : ModelWithCorners ℝ G H} [TopologicalSpace X] [ChartedSpace H X]
  [NormedAddCommGroup N] [InnerProductSpace ℝ N]
  {g : d.UpperSmoothFace hf I X N} {T : d.FaceDescent hf I X N g} (A : T.Realization)

def upperCorrectionSmoothEquiv :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    SmoothBoundaryBodyEquiv (J := 𝓘(ℝ, RegularLevel.Model E))
      d.upperBodyInclusion d.upperBodyInclusion := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  exact {
    body := A.upperCorrection
    boundary := A.boundaryCorrectionDiffeomorph
    boundary_point := fun y => Subtype.ext (A.upperCorrection_on_level y) }

theorem upperCorrectionSmoothEquiv_body :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    A.upperCorrectionSmoothEquiv.body = A.upperCorrection := rfl

theorem upperCorrectionSmoothEquiv_boundary :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    A.upperCorrectionSmoothEquiv.boundary.toHomeomorph = A.boundaryCorrection := rfl

variable [T2Space M] [CompactSpace M] (m n : ℕ)
  [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = m + 1)]
  [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
  (P : letI := RegularLevel.chartedSpace hf d.lower_regular
    FramedSurgery.SmoothBoundaryData (d.attachingSmoothFace hf m) n)
  (hd : d.HasSmoothExterior hf)

open Classical in
def beltFramedSmoothRealization :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI : CompactSpace d.LowerLevel :=
      isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
    letI : CompactSpace {x : M // f x ≤ f p - d.radius ^ 2} :=
      isCompact_iff_compactSpace.mp (isClosed_le hf.continuous continuous_const).isCompact
    letI := P.charted
    SmoothBoundaryBodyEquiv (J := 𝓘(ℝ, RegularLevel.Model E))
      (FramedSurgery.boundaryBodyMap (d.attachingSmoothFace hf m) d.lowerBodyInclusion n
        (d.lowerBodyInclusion_isClosedEmbedding hf)) d.upperBodyInclusion := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ : CompactSpace d.LowerLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : CompactSpace {x : M // f x ≤ f p - d.radius ^ 2} :=
    isCompact_iff_compactSpace.mp (isClosed_le hf.continuous continuous_const).isCompact
  let _ := P.charted
  exact (T.ambient.beltFramedSmoothRealization hf m n P hd).trans A.upperCorrectionSmoothEquiv

open Classical in
theorem beltFramedSmoothRealization_body :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI : CompactSpace d.LowerLevel :=
      isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
    letI : CompactSpace {x : M // f x ≤ f p - d.radius ^ 2} :=
      isCompact_iff_compactSpace.mp (isClosed_le hf.continuous continuous_const).isCompact
    letI := P.charted
    (A.beltFramedSmoothRealization m n P hd).body =
      (FramedSurgery.bodyDiskChange (d.attachingSmoothFace hf m) d.lowerBodyInclusion
        MorseHandle.beltFaceDiskHomeomorph MorseHandle.beltFaceDiskHomeomorph_boundary).trans
          (A.framedBodyRealization m) := rfl

open Classical in
theorem beltFramedSmoothRealization_boundary :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI : CompactSpace d.LowerLevel :=
      isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
    letI : CompactSpace {x : M // f x ≤ f p - d.radius ^ 2} :=
      isCompact_iff_compactSpace.mp (isClosed_le hf.continuous continuous_const).isCompact
    letI := P.charted
    (A.beltFramedSmoothRealization m n P hd).boundary.toHomeomorph =
      (FramedSurgery.boundaryDiskChange (d.attachingSmoothFace hf m) n
        MorseHandle.beltFaceDiskHomeomorph MorseHandle.beltFaceDiskHomeomorph_boundary).trans
          (A.framedBoundaryRealization m n) := rfl

open Classical in
theorem beltFramedSmoothRealization_old (x : {x : M // f x ≤ f p - d.radius ^ 2}) :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI : CompactSpace d.LowerLevel :=
      isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
    letI : CompactSpace {x : M // f x ≤ f p - d.radius ^ 2} :=
      isCompact_iff_compactSpace.mp (isClosed_le hf.continuous continuous_const).isCompact
    letI := P.charted
    (A.beltFramedSmoothRealization m n P hd).body (FaceAttachment.oldMap
      (FramedSurgery.bodyFaceMap (d.attachingSmoothFace hf m) d.lowerBodyInclusion) x) =
      A.framedBodyRealization m (FaceAttachment.oldMap
        (FramedSurgery.bodyFaceMap (d.attachingSmoothFace hf m) d.lowerBodyInclusion) x) := rfl

open Classical in
theorem beltFramedSmoothRealization_handle (z : d.HandleDomain) :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI : CompactSpace d.LowerLevel :=
      isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
    letI : CompactSpace {x : M // f x ≤ f p - d.radius ^ 2} :=
      isCompact_iff_compactSpace.mp (isClosed_le hf.continuous continuous_const).isCompact
    letI := P.charted
    (A.beltFramedSmoothRealization m n P hd).body (FaceAttachment.handleMap
      (FramedSurgery.bodyFaceMap (d.attachingSmoothFace hf m) d.lowerBodyInclusion) z) =
      A.framedBodyRealization m (FaceAttachment.handleMap
        (FramedSurgery.bodyFaceMap (d.attachingSmoothFace hf m) d.lowerBodyInclusion)
          (FramedSurgery.wholeHandleDiskChange MorseHandle.beltFaceDiskHomeomorph z)) := rfl

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData.FaceDescent.Realization
