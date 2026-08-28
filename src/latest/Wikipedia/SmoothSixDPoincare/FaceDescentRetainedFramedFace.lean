import Wikipedia.SmoothSixDPoincare.FaceDescentFramedBoundary
import Wikipedia.SmoothSixDPoincare.FramedSurgeryRetainedBodyFace

/-!
# The actual descended face in the corrected constructed boundary

The lower framed face avoids the original attaching piece. Its entire
closed face is therefore retained in the constructed smooth boundary.
The literal corrected whole-body realization sends every retained face
coordinate to the original upper face, not merely to an isotoped image.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData.FaceDescent

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  {f : M → ℝ} {p : M} {d : MorseSurgeryData E f p}
  {hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f}
  {G H X N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {I : ModelWithCorners ℝ G H} [TopologicalSpace X] [ChartedSpace H X]
  [NormedAddCommGroup N] [InnerProductSpace ℝ N]
  {g : d.UpperSmoothFace hf I X N} (T : d.FaceDescent hf I X N g)
  (m : ℕ) [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = m + 1)]

open Classical in
omit [CompactSpace M] in
theorem lower_disjoint_nativeFramedFace :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    Disjoint (range T.lower.map) (range (d.attachingSmoothFace hf m).map) := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let e := FramedSurgery.oldFaceCoordinates d.chart.NegativeCoordinates d.chart.PositiveCoordinates
  have hrange : range d.surgery.oldPiece = range (d.attachingSmoothFace hf m).map := by
    calc
      _ = range ((d.attachingSmoothFace hf m).map ∘ e) :=
        congrArg range (funext (d.attachingSmoothFace_oldPiece hf m))
      _ = _ := e.surjective.range_comp _
  rw [← hrange]
  exact T.disjoint

variable (n : ℕ) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
  [CompactSpace (X × MorseHandle.UnitDisk N)]
  (P : letI := RegularLevel.chartedSpace hf d.lower_regular
    FramedSurgery.SmoothBoundaryData (d.attachingSmoothFace hf m) n)

def retainedLowerFace :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := P.charted
    SmoothClosedFace I 𝓘(ℝ, RegularLevel.Model E) X N (d.FramedBoundary hf m n) := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := P.charted
  exact P.retainClosedDisjointFace T.lower (T.lower_disjoint_nativeFramedFace m)

namespace Realization

variable {T} (A : T.Realization)

open Classical in
theorem retainedLowerFace_realized (z : X × MorseHandle.UnitDisk N) :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI := P.charted
    A.framedBoundaryBodyMap m n ((T.retainedLowerFace m n P).map z) =
      ⟨(g.map z).val, (g.map z).property.le⟩ := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ := P.charted
  let _ : CompactSpace d.LowerLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : CompactSpace {x : M // f x ≤ f p - d.radius ^ 2} :=
    isCompact_iff_compactSpace.mp (isClosed_le hf.continuous continuous_const).isCompact
  have he := P.retainClosedDisjointFace_bodyMap d.lowerBodyInclusion
    (d.lowerBodyInclusion_isClosedEmbedding hf) T.lower
    (T.lower_disjoint_nativeFramedFace m) z
  have hQ := FaceAttachment.congrFaceMap_old (d.attachingSmoothFace_bodyFace hf m)
    (d.lowerBodyInclusion (T.lower.map z))
  change A.faceQuotientRealization
    (FaceAttachment.congrFaceMap (d.attachingSmoothFace_bodyFace hf m)
      (FramedSurgery.boundaryBodyMap (d.attachingSmoothFace hf m) d.lowerBodyInclusion n
        (d.lowerBodyInclusion_isClosedEmbedding hf)
          ((P.retainClosedDisjointFace T.lower (T.lower_disjoint_nativeFramedFace m)).map z))) = _
  exact (congrArg A.faceQuotientRealization
    ((congrArg (FaceAttachment.congrFaceMap
      (d.attachingSmoothFace_bodyFace hf m)) he).trans hQ)).trans
      (A.faceQuotientRealization_face z)

open Classical in
theorem retainedLowerFace_boundaryPoint (z : X × MorseHandle.UnitDisk N) :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI := P.charted
    A.framedBoundaryRealization m n ((T.retainedLowerFace m n P).map z) = g.map z := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ := P.charted
  apply Subtype.ext
  exact (A.framedBoundary_realizations_agree m n _).symm.trans
    (congrArg (fun x : {x : M // f x ≤ f p + d.radius ^ 2} => x.val)
      (A.retainedLowerFace_realized m n P z))

open Classical in
theorem exists_retainedLowerFace_realization :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∃ P : FramedSurgery.SmoothBoundaryData (d.attachingSmoothFace hf m) n,
      letI := P.charted
      ∀ z, A.framedBoundaryRealization m n ((T.retainedLowerFace m n P).map z) = g.map z := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  obtain ⟨P⟩ := d.nonempty_framedSmoothBoundaryData hf m n
  exact ⟨P, A.retainedLowerFace_boundaryPoint m n P⟩

end Realization

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData.FaceDescent
