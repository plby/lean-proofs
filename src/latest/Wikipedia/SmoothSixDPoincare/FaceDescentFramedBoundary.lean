import Wikipedia.SmoothSixDPoincare.FaceDescentRealization
import Wikipedia.SmoothSixDPoincare.ShrunkFramedBoundaryRealization

/-!
# The constructed boundary under the actual corrected face-descent realization

The correction is the retained inverse upper-level isotopy. Its ambient
extension proves the exact upper-sublevel restriction. Both corrected
realizations still agree on every point of the same constructed boundary.
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

def boundaryCorrection : d.UpperLevel ≃ₜ d.UpperLevel :=
  (A.ambient.toHomeomorph.subtype (fun x => by
    change f x = f p + d.radius ^ 2 ↔ f (A.ambient x) = f p + d.radius ^ 2
    rw [A.height])).symm

theorem boundaryCorrection_eq_upperMap :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    A.boundaryCorrection = T.upperMap.symm.toHomeomorph := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  ext y
  change A.ambient.symm y.val = (T.upperMap.symm y).val
  apply A.ambient.injective
  exact (A.ambient.apply_symm_apply y.val).trans
    ((A.level (T.upperMap.symm y)).trans
      (congrArg Subtype.val (T.upperMap.apply_symm_apply y))).symm

theorem upperCorrection_on_level (y : d.UpperLevel) :
    (A.upperCorrection ⟨y.val, y.property.le⟩).val = (A.boundaryCorrection y).val := rfl

variable [T2Space M] [CompactSpace M] (m : ℕ)
  [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = m + 1)]

open Classical in
def framedBodyRealization :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    FramedSurgery.AttachedBody (d.attachingSmoothFace hf m) d.lowerBodyInclusion ≃ₜ
      {x : M // f x ≤ f p + d.radius ^ 2} :=
  (T.shrunk.framedBodyRealization hf m).trans A.upperCorrection

open Classical in
theorem framedBodyRealization_eq_quotient :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    A.framedBodyRealization m =
      (FaceAttachment.congrFaceMap (d.attachingSmoothFace_bodyFace hf m)).trans
        A.faceQuotientRealization := rfl

variable (n : ℕ) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]

def framedBoundaryRealization : d.FramedBoundary hf m n ≃ₜ d.UpperLevel :=
  (T.shrunk.framedBoundaryRealization hf m n).trans A.boundaryCorrection

def framedBoundaryBodyMap : C(d.FramedBoundary hf m n,
    {x : M // f x ≤ f p + d.radius ^ 2}) :=
  ⟨fun z => A.upperCorrection (T.shrunk.framedBoundaryBodyMap hf m n z),
    A.upperCorrection.continuous.comp (T.shrunk.framedBoundaryBodyMap hf m n).continuous⟩

theorem framedBoundaryBodyMap_isClosedEmbedding :
    IsClosedEmbedding (A.framedBoundaryBodyMap m n) :=
  A.upperCorrection.isClosedEmbedding.comp
    (T.shrunk.framedBoundaryBodyMap_isClosedEmbedding hf m n)

theorem framedBoundary_realizations_agree (z : d.FramedBoundary hf m n) :
    (A.framedBoundaryBodyMap m n z).val = (A.framedBoundaryRealization m n z).val := by
  have he : T.shrunk.framedBoundaryBodyMap hf m n z =
      ⟨(T.shrunk.framedBoundaryRealization hf m n z).val,
        (T.shrunk.framedBoundaryRealization hf m n z).property.le⟩ :=
    Subtype.ext (T.shrunk.framedBoundary_realizations_agree hf m n z)
  change (A.upperCorrection (T.shrunk.framedBoundaryBodyMap hf m n z)).val = _
  rw [he]
  exact A.upperCorrection_on_level (T.shrunk.framedBoundaryRealization hf m n z)

theorem framedBoundaryBodyMap_range : range (A.framedBoundaryBodyMap m n) =
    {x : {x : M // f x ≤ f p + d.radius ^ 2} | f x.val = f p + d.radius ^ 2} := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    change f (A.framedBoundaryBodyMap m n z).val = _
    rw [A.framedBoundary_realizations_agree m n]
    exact (A.framedBoundaryRealization m n z).property
  · intro hx
    let y : d.UpperLevel := ⟨x.val, hx⟩
    refine ⟨(A.framedBoundaryRealization m n).symm y, Subtype.ext ?_⟩
    rw [A.framedBoundary_realizations_agree m n, Homeomorph.apply_symm_apply]

open Classical in
theorem framedBoundaryBodyMap_eq_wholeRealization (z : d.FramedBoundary hf m n) :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI : CompactSpace d.LowerLevel :=
      isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
    letI : CompactSpace {x : M // f x ≤ f p - d.radius ^ 2} :=
      isCompact_iff_compactSpace.mp (isClosed_le hf.continuous continuous_const).isCompact
    A.framedBoundaryBodyMap m n z = A.framedBodyRealization m
      (FramedSurgery.boundaryBodyMap (d.attachingSmoothFace hf m) d.lowerBodyInclusion n
        (d.lowerBodyInclusion_isClosedEmbedding hf) z) := rfl

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData.FaceDescent.Realization
