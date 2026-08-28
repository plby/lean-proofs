import Wikipedia.SmoothSixDPoincare.NativeFramedBoundaryRealization
import Wikipedia.SmoothSixDPoincare.FramedSurgeryBodyDiskChange
import Wikipedia.SmoothSixDPoincare.MorseSurgeryBeltCoordinates

/-!
# Correct the native framed realization to the original smooth belt coordinates

The explicit negative-disk homeomorphism fixes the entire attaching face.
It gives a whole-body correction, unchanged on the original lower body.
The corrected boundary realization agrees with the native belt chart on
the entire closed positive face and with the old realization on the common
exterior. No global smoothness claim is made here.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

section Coordinates

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

open Classical in
theorem beltFaceChangeCoordinates
    (z : FramedSurgery.ClosedNewFace d.chart.NegativeCoordinates d.chart.PositiveCoordinates) :
    (FramedSurgery.newFaceCoordinates d.chart.NegativeCoordinates
      d.chart.PositiveCoordinates).symm
        (FramedSurgery.newFaceDiskChange MorseHandle.beltFaceDiskHomeomorph z) =
    (d.beltFaceCoordinates
      ((FramedSurgery.newFaceCoordinates d.chart.NegativeCoordinates
        d.chart.PositiveCoordinates).symm z).1, z.2) := rfl

end Coordinates

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (m : ℕ)
  [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = m + 1)]

open Classical in
def beltFramedBodyRealization :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    FramedSurgery.AttachedBody (d.attachingSmoothFace hf m) d.lowerBodyInclusion ≃ₜ
      {x : M // f x ≤ f p + d.radius ^ 2} := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  exact (FramedSurgery.bodyDiskChange (d.attachingSmoothFace hf m) d.lowerBodyInclusion
    MorseHandle.beltFaceDiskHomeomorph MorseHandle.beltFaceDiskHomeomorph_boundary).trans
    (d.framedBodyRealization hf m)

open Classical in
theorem beltFramedBodyRealization_old (x : {x : M // f x ≤ f p - d.radius ^ 2}) :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    d.beltFramedBodyRealization hf m (FaceAttachment.oldMap
      (FramedSurgery.bodyFaceMap (d.attachingSmoothFace hf m) d.lowerBodyInclusion) x) =
      d.attachmentHomeomorph ⟨x.val, Or.inl x.property⟩ := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  exact d.framedBodyRealization_old hf m x

open Classical in
theorem beltFramedBodyRealization_handle (z : d.HandleDomain) :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    d.beltFramedBodyRealization hf m (FaceAttachment.handleMap
      (FramedSurgery.bodyFaceMap (d.attachingSmoothFace hf m) d.lowerBodyInclusion) z) =
      d.attachmentHomeomorph
        ⟨d.handleMap (FramedSurgery.wholeHandleDiskChange MorseHandle.beltFaceDiskHomeomorph z),
          Or.inr
            ⟨FramedSurgery.wholeHandleDiskChange MorseHandle.beltFaceDiskHomeomorph z, rfl⟩⟩ := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  exact d.framedBodyRealization_handle hf m
    (FramedSurgery.wholeHandleDiskChange MorseHandle.beltFaceDiskHomeomorph z)

variable (n : ℕ) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]

open Classical in
def beltFramedBoundaryRealization : d.FramedBoundary hf m n ≃ₜ d.UpperLevel := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ : CompactSpace d.LowerLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  exact (FramedSurgery.boundaryDiskChange (d.attachingSmoothFace hf m) n
    MorseHandle.beltFaceDiskHomeomorph MorseHandle.beltFaceDiskHomeomorph_boundary).trans
    (d.framedBoundaryRealization hf m n)

open Classical in
theorem beltFramedBoundaryRealization_exterior :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    ∀ r : FramedSurgery.Exterior (d.attachingSmoothFace hf m),
      d.beltFramedBoundaryRealization hf m n
        (FramedSurgery.exteriorNewMap (d.attachingSmoothFace hf m) n r) =
      d.framedBoundaryRealization hf m n
        (FramedSurgery.exteriorNewMap (d.attachingSmoothFace hf m) n r) := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ : CompactSpace d.LowerLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  intro r
  exact congrArg (d.framedBoundaryRealization hf m n)
    (FramedSurgery.boundaryDiskChange_exterior (d.attachingSmoothFace hf m) n
      MorseHandle.beltFaceDiskHomeomorph MorseHandle.beltFaceDiskHomeomorph_boundary r)

open Classical in
theorem framedBoundaryRealization_newFace :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    ∀ z : FramedSurgery.ClosedNewFace d.chart.NegativeCoordinates d.chart.PositiveCoordinates,
      d.framedBoundaryRealization hf m n
        (FramedSurgery.closedNewMap (d.attachingSmoothFace hf m) n z) =
      d.surgery.newPiece
        ((FramedSurgery.newFaceCoordinates d.chart.NegativeCoordinates
          d.chart.PositiveCoordinates).symm z) := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ : CompactSpace d.LowerLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  exact FramedSurgery.presentationBoundaryHomeomorph_newFace (d.attachingSmoothFace hf m)
    d.surgery (d.attachingSmoothFace_oldPiece hf m) n

open Classical in
theorem beltFramedBoundaryRealization_newFace_raw :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    ∀ z : FramedSurgery.ClosedNewFace d.chart.NegativeCoordinates d.chart.PositiveCoordinates,
      d.beltFramedBoundaryRealization hf m n
        (FramedSurgery.closedNewMap (d.attachingSmoothFace hf m) n z) =
      d.surgery.newPiece
        ((FramedSurgery.newFaceCoordinates d.chart.NegativeCoordinates
          d.chart.PositiveCoordinates).symm
            (FramedSurgery.newFaceDiskChange MorseHandle.beltFaceDiskHomeomorph z)) := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ : CompactSpace d.LowerLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  intro z
  have h₁ := congrArg (d.framedBoundaryRealization hf m n)
    (FramedSurgery.boundaryDiskChange_newFace (d.attachingSmoothFace hf m) n
      MorseHandle.beltFaceDiskHomeomorph MorseHandle.beltFaceDiskHomeomorph_boundary z)
  exact h₁.trans (d.framedBoundaryRealization_newFace hf m n
    (FramedSurgery.newFaceDiskChange MorseHandle.beltFaceDiskHomeomorph z))

open Classical in
theorem beltFramedBoundaryRealization_newFace :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    ∀ z : FramedSurgery.ClosedNewFace d.chart.NegativeCoordinates d.chart.PositiveCoordinates,
      d.beltFramedBoundaryRealization hf m n
        (FramedSurgery.closedNewMap (d.attachingSmoothFace hf m) n z) =
      d.beltClosedDiskMap
        ((FramedSurgery.newFaceCoordinates d.chart.NegativeCoordinates
          d.chart.PositiveCoordinates).symm z) := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  intro z
  exact (d.beltFramedBoundaryRealization_newFace_raw hf m n z).trans
    ((congrArg d.surgery.newPiece (d.beltFaceChangeCoordinates z)).trans
      (d.newPiece_beltFaceCoordinates
        ((FramedSurgery.newFaceCoordinates d.chart.NegativeCoordinates
          d.chart.PositiveCoordinates).symm z).1 z.2))

open Classical in
theorem beltFramed_realizations_agree :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI : CompactSpace d.LowerLevel :=
      isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
    letI : CompactSpace {x : M // f x ≤ f p - d.radius ^ 2} :=
      isCompact_iff_compactSpace.mp (isClosed_le hf.continuous continuous_const).isCompact
    ∀ z : d.FramedBoundary hf m n,
      (d.beltFramedBodyRealization hf m (FramedSurgery.boundaryBodyMap
        (d.attachingSmoothFace hf m) d.lowerBodyInclusion n
          (d.lowerBodyInclusion_isClosedEmbedding hf) z)).val =
        (d.beltFramedBoundaryRealization hf m n z).val := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ : CompactSpace d.LowerLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : CompactSpace {x : M // f x ≤ f p - d.radius ^ 2} :=
    isCompact_iff_compactSpace.mp (isClosed_le hf.continuous continuous_const).isCompact
  intro z
  have he := FramedSurgery.bodyDiskChange_boundaryMap (d.attachingSmoothFace hf m)
    d.lowerBodyInclusion MorseHandle.beltFaceDiskHomeomorph
      MorseHandle.beltFaceDiskHomeomorph_boundary n (d.lowerBodyInclusion_isClosedEmbedding hf) z
  exact (congrArg (fun x => (d.framedBodyRealization hf m x).val) he).symm.trans
    (d.framedBoundary_realizations_agree hf m n _)

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
