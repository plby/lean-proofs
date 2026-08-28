import Wikipedia.SmoothSixDPoincare.NativeSmoothBoundaryBodies
import Wikipedia.SmoothSixDPoincare.FaceDescentBeltQuotientRealization
import Wikipedia.SmoothSixDPoincare.OrderedBandSmoothBodyEquiv
import Wikipedia.SmoothSixDPoincare.SmoothHandleChain

/-!
# Original native face-descent and band stages as finite smooth handle chains

The single-handle chain uses the actual corrected face-descent realization.
Its old-body and whole-handle maps are exactly those of the specified native
quotient. A retained regular band is the same smooth boundary/body change
already proved on the original levels and sublevels.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse

namespace MorseSurgeryData.FaceDescent.Realization

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  {f : M → ℝ} {p : M} {d : MorseSurgeryData E f p}
  {hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f}
  {G H X N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {I : ModelWithCorners ℝ G H} [TopologicalSpace X] [ChartedSpace H X]
  [NormedAddCommGroup N] [InnerProductSpace ℝ N]
  {g : d.UpperSmoothFace hf I X N} {T : d.FaceDescent hf I X N g} (A : T.Realization)
  (m n : ℕ) [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = m + 1)]
  [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
  (P : letI := RegularLevel.chartedSpace hf d.lower_regular
    FramedSurgery.SmoothBoundaryData (d.attachingSmoothFace hf m) n)
  (hd : d.HasSmoothExterior hf)

open Classical in
def beltSmoothBodyEquiv :
    SmoothBoundaryBody.Equiv
      ((d.lowerSmoothBody hf).attach (d.attachingSmoothFace hf m) n P) (d.upperSmoothBody hf) :=
  A.beltFramedSmoothRealization m n P hd

open Classical in
theorem beltSmoothBodyEquiv_old (x : {x : M // f x ≤ f p - d.radius ^ 2}) :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    (A.beltSmoothBodyEquiv m n P hd).body
      (FaceAttachment.oldMap
        (FramedSurgery.bodyFaceMap (d.attachingSmoothFace hf m) d.lowerBodyInclusion) x) =
      A.beltFaceQuotientRealization (FaceAttachment.oldMap d.handleFaceToSublevel x) := rfl

open Classical in
theorem beltSmoothBodyEquiv_handle (z : d.HandleDomain) :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    (A.beltSmoothBodyEquiv m n P hd).body
      (FaceAttachment.handleMap
        (FramedSurgery.bodyFaceMap (d.attachingSmoothFace hf m) d.lowerBodyInclusion) z) =
      A.beltFaceQuotientRealization (FaceAttachment.handleMap d.handleFaceToSublevel z) := rfl

open Classical in
def singleSmoothChain :
    SmoothHandleChain 𝓘(ℝ, RegularLevel.Model E) (d.lowerSmoothBody hf) (d.upperSmoothBody hf) 1 :=
  .cons (d.attachingSmoothFace hf m) P (A.beltSmoothBodyEquiv m n P hd)
    (.nil (SmoothBoundaryBodyEquiv.refl (d.upperSmoothBody hf).inclusion))

open Classical in
theorem singleSmoothChain_sourceMap (x : {x : M // f x ≤ f p - d.radius ^ 2}) :
    (A.singleSmoothChain m n P hd).sourceMap x =
      A.beltFaceQuotientRealization (FaceAttachment.oldMap d.handleFaceToSublevel x) := rfl

open Classical in
theorem singleSmoothChain_handle (z : d.HandleDomain) :
    (A.singleSmoothChain m n P hd).piecesMap (Sum.inl z) =
      A.beltFaceQuotientRealization (FaceAttachment.handleMap d.handleFaceToSublevel z) := rfl

open Classical in
include hd in
theorem exists_singleSmoothChain (hmin : 0 < Module.finrank ℝ d.chart.NegativeCoordinates)
    (hmax : Module.finrank ℝ d.chart.NegativeCoordinates < Module.finrank ℝ E) :
    ∃ c : SmoothHandleChain 𝓘(ℝ, RegularLevel.Model E)
        (d.lowerSmoothBody hf) (d.upperSmoothBody hf) 1,
      ∀ x, c.sourceMap x =
        A.beltFaceQuotientRealization (FaceAttachment.oldMap d.handleFaceToSublevel x) := by
  let m := Module.finrank ℝ d.chart.NegativeCoordinates - 1
  let n := Module.finrank ℝ d.chart.PositiveCoordinates - 1
  have hsplit := d.chart.finrank_negative_add_positive
  let _ : Fact (Module.finrank ℝ d.chart.NegativeCoordinates = m + 1) := ⟨by dsimp [m]; omega⟩
  let _ : Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1) := ⟨by dsimp [n]; omega⟩
  obtain ⟨P⟩ := d.nonempty_framedSmoothBoundaryData hf m n
  exact ⟨A.singleSmoothChain m n P hd, A.singleSmoothChain_sourceMap m n P hd⟩

end MorseSurgeryData.FaceDescent.Realization

namespace SurgeryWindows.BandData

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
  {S : SurgeryWindows E f} {i j : Fin S.count} (B : S.BandData i j)
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

def smoothBodyEquiv : SmoothBoundaryBody.Equiv
    ((S.data (S.point i)).upperSmoothBody hf) ((S.data (S.point j)).lowerSmoothBody hf) :=
  B.smoothBoundaryBodyEquiv hf

theorem smoothBodyEquiv_body : (B.smoothBodyEquiv hf).body = B.sublevelHomeomorph := rfl

theorem smoothBodyEquiv_boundary :
    (B.smoothBodyEquiv hf).boundary.toHomeomorph = B.level :=
  B.smoothBoundaryBodyEquiv_boundary hf

end SurgeryWindows.BandData

end Wikipedia.SmoothSixDPoincare.ManifoldMorse
