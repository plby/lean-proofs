import Wikipedia.SmoothSixDPoincare.FaceDescentSmoothFramedRealization
import Wikipedia.SmoothSixDPoincare.FaceDescentRetainedFramedFace

/-!
# The globally smooth realization retains the exact original descended face

The whole lower body is fixed by the belt correction. Consequently its
retained disjoint face still realizes the original upper face, with every
sphere and normal-disk parameter unchanged. The smooth atlas and the
commuting body/boundary equivalence are constructed together.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData.FaceDescent.Realization

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  {f : M → ℝ} {p : M} {d : MorseSurgeryData E f p}
  {hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f}
  {G H X N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {I : ModelWithCorners ℝ G H} [TopologicalSpace X] [ChartedSpace H X]
  [NormedAddCommGroup N] [InnerProductSpace ℝ N] [CompactSpace (X × MorseHandle.UnitDisk N)]
  {g : d.UpperSmoothFace hf I X N} {T : d.FaceDescent hf I X N g} (A : T.Realization)
  (m n : ℕ) [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = m + 1)]
  [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
  (P : letI := RegularLevel.chartedSpace hf d.lower_regular
    FramedSurgery.SmoothBoundaryData (d.attachingSmoothFace hf m) n)
  (hd : d.HasSmoothExterior hf)

open Classical in
theorem beltFramedSmoothRealization_retainedFace (z : X × MorseHandle.UnitDisk N) :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI : CompactSpace d.LowerLevel :=
      isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
    letI : CompactSpace {x : M // f x ≤ f p - d.radius ^ 2} :=
      isCompact_iff_compactSpace.mp (isClosed_le hf.continuous continuous_const).isCompact
    letI := P.charted
    (A.beltFramedSmoothRealization m n P hd).boundary
      ((T.retainedLowerFace m n P).map z) = g.map z := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ : CompactSpace d.LowerLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : CompactSpace {x : M // f x ≤ f p - d.radius ^ 2} :=
    isCompact_iff_compactSpace.mp (isClosed_le hf.continuous continuous_const).isCompact
  let _ := P.charted
  let e := A.beltFramedSmoothRealization m n P hd
  let y := (T.retainedLowerFace m n P).map z
  have hb : FramedSurgery.boundaryBodyMap (d.attachingSmoothFace hf m) d.lowerBodyInclusion n
      (d.lowerBodyInclusion_isClosedEmbedding hf) y =
      FaceAttachment.oldMap
        (FramedSurgery.bodyFaceMap (d.attachingSmoothFace hf m) d.lowerBodyInclusion)
          (d.lowerBodyInclusion (T.lower.map z)) :=
    P.retainClosedDisjointFace_bodyMap d.lowerBodyInclusion
      (d.lowerBodyInclusion_isClosedEmbedding hf) T.lower
        (T.lower_disjoint_nativeFramedFace m) z
  apply (d.upperBodyInclusion_isClosedEmbedding hf).injective
  calc
    d.upperBodyInclusion (e.boundary y) = e.body
        (FramedSurgery.boundaryBodyMap (d.attachingSmoothFace hf m) d.lowerBodyInclusion n
          (d.lowerBodyInclusion_isClosedEmbedding hf) y) := (e.boundary_point y).symm
    _ = e.body (FaceAttachment.oldMap
        (FramedSurgery.bodyFaceMap (d.attachingSmoothFace hf m) d.lowerBodyInclusion)
          (d.lowerBodyInclusion (T.lower.map z))) := congrArg e.body hb
    _ = A.framedBodyRealization m (FaceAttachment.oldMap
        (FramedSurgery.bodyFaceMap (d.attachingSmoothFace hf m) d.lowerBodyInclusion)
          (d.lowerBodyInclusion (T.lower.map z))) :=
      A.beltFramedSmoothRealization_old m n P hd _
    _ = A.faceQuotientRealization (FaceAttachment.oldMap d.handleFaceToSublevel
        (d.lowerBodyInclusion (T.lower.map z))) := rfl
    _ = d.upperBodyInclusion (g.map z) := A.faceQuotientRealization_face z

open Classical in
include hd in
theorem exists_beltFramedSmoothRealization_retainedFace :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI : CompactSpace d.LowerLevel :=
      isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
    letI : CompactSpace {x : M // f x ≤ f p - d.radius ^ 2} :=
      isCompact_iff_compactSpace.mp (isClosed_le hf.continuous continuous_const).isCompact
    ∃ P : FramedSurgery.SmoothBoundaryData (d.attachingSmoothFace hf m) n,
      letI := P.charted
      ∃ e : SmoothBoundaryBodyEquiv (J := 𝓘(ℝ, RegularLevel.Model E))
          (FramedSurgery.boundaryBodyMap (d.attachingSmoothFace hf m) d.lowerBodyInclusion n
            (d.lowerBodyInclusion_isClosedEmbedding hf)) d.upperBodyInclusion,
        e.body = (FramedSurgery.bodyDiskChange (d.attachingSmoothFace hf m) d.lowerBodyInclusion
          MorseHandle.beltFaceDiskHomeomorph MorseHandle.beltFaceDiskHomeomorph_boundary).trans
            (A.framedBodyRealization m) ∧
        ∀ z, e.boundary ((T.retainedLowerFace m n P).map z) = g.map z := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ : CompactSpace d.LowerLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : CompactSpace {x : M // f x ≤ f p - d.radius ^ 2} :=
    isCompact_iff_compactSpace.mp (isClosed_le hf.continuous continuous_const).isCompact
  obtain ⟨P⟩ := d.nonempty_framedSmoothBoundaryData hf m n
  exact ⟨P, A.beltFramedSmoothRealization m n P hd,
    A.beltFramedSmoothRealization_body m n P hd,
    A.beltFramedSmoothRealization_retainedFace m n P hd⟩

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData.FaceDescent.Realization
