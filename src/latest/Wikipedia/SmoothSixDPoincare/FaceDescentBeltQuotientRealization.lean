import Wikipedia.SmoothSixDPoincare.BeltHandleQuotientChange
import Wikipedia.SmoothSixDPoincare.FaceDescentSmoothRetainedFace

/-!
# The smooth face-descent realization in the original native quotient

The original native attachment quotient is reparametrized by the explicit
belt disk change, fixed on its attaching face. The exact original lower
face is still carried to the original upper face. The constructed smooth
boundary/body realization has precisely this whole quotient realization.
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
  [NormedAddCommGroup N] [InnerProductSpace ℝ N]
  {g : d.UpperSmoothFace hf I X N} {T : d.FaceDescent hf I X N g} (A : T.Realization)

open Classical in
def beltFaceQuotientRealization : FaceAttachment.Space d.handleFaceToSublevel ≃ₜ
    {x : M // f x ≤ f p + d.radius ^ 2} :=
  d.beltFaceQuotientChange.trans A.faceQuotientRealization

open Classical in
theorem beltFaceQuotientRealization_old (x : {x : M // f x ≤ f p - d.radius ^ 2}) :
    A.beltFaceQuotientRealization (FaceAttachment.oldMap d.handleFaceToSublevel x) =
      A.faceQuotientRealization (FaceAttachment.oldMap d.handleFaceToSublevel x) := rfl

open Classical in
theorem beltFaceQuotientRealization_handle (z : d.HandleDomain) :
    A.beltFaceQuotientRealization (FaceAttachment.handleMap d.handleFaceToSublevel z) =
      A.faceQuotientRealization
        (FaceAttachment.handleMap d.handleFaceToSublevel (d.beltHandleChange z)) := rfl

open Classical in
theorem beltFaceQuotientRealization_face :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ z, A.beltFaceQuotientRealization (FaceAttachment.oldMap d.handleFaceToSublevel
        ⟨(T.lower.map z).val, (T.lower.map z).property.le⟩) =
      ⟨(g.map z).val, (g.map z).property.le⟩ := A.faceQuotientRealization_face

variable (m n : ℕ) [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = m + 1)]
  [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
  (P : letI := RegularLevel.chartedSpace hf d.lower_regular
    FramedSurgery.SmoothBoundaryData (d.attachingSmoothFace hf m) n)
  (hd : d.HasSmoothExterior hf)

open Classical in
theorem beltFramedSmoothRealization_body_eq_quotient :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI : CompactSpace d.LowerLevel :=
      isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
    letI : CompactSpace {x : M // f x ≤ f p - d.radius ^ 2} :=
      isCompact_iff_compactSpace.mp (isClosed_le hf.continuous continuous_const).isCompact
    letI := P.charted
    (A.beltFramedSmoothRealization m n P hd).body =
      (FaceAttachment.congrFaceMap (d.attachingSmoothFace_bodyFace hf m)).trans
        A.beltFaceQuotientRealization := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ : CompactSpace d.LowerLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : CompactSpace {x : M // f x ≤ f p - d.radius ^ 2} :=
    isCompact_iff_compactSpace.mp (isClosed_le hf.continuous continuous_const).isCompact
  let _ := P.charted
  apply Homeomorph.ext
  intro z
  refine FaceAttachment.induction_on _ z
    (P := fun w => (A.beltFramedSmoothRealization m n P hd).body w =
      ((FaceAttachment.congrFaceMap (d.attachingSmoothFace_bodyFace hf m)).trans
        A.beltFaceQuotientRealization) w) ?_ ?_
  · intro x
    rfl
  · intro k
    rfl

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData.FaceDescent.Realization
