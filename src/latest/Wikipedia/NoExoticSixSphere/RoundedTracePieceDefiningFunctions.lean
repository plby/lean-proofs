import Wikipedia.NoExoticSixSphere.RoundedTraceOutwardTangentSection

/-! # The three native nonnegative boundary-defining functions -/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel RoundedHandleCorner

@[instance_reducible]
def pieceFintype : Fintype Piece := by
  classical
  exact ⟨{.cylinder, .handle, .collar}, fun i ↦ by cases i <;> simp⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def pieceLevel : ∀ i : Piece, pieceDomain A i → ℝ
  | .cylinder, p => IntervalSuperlevel.level (UnroundedTrace.height A)
      (unchangedCylinderHomeomorph A p).val.val
  | .handle, p => NoExoticSixSphere.HandleSuperlevel.level (UnroundedTrace.handleRadius A)
      (unchangedHandleHomeomorph A p).val.val
  | .collar, p => collarLevel (bump A) (UnroundedTrace.handleRadius A)
      ((collarHomeomorph A).symm p).val

theorem contMDiff_pieceLevel (i : Piece) : letI := pieceAtlas A i;
    ContMDiff (ProductHalfSpace.model (Vector 6)) 𝓘(ℝ, ℝ) ∞ (pieceLevel A i) := by
  cases i with
  | cylinder =>
      let := pieceAtlas A .cylinder
      exact (IntervalSuperlevel.contMDiff_level (I := 𝓡 6) (UnroundedTrace.height A)).comp
        (contMDiff_unchangedCylinder_parameters A)
  | handle =>
      let := pieceAtlas A .handle
      exact (NoExoticSixSphere.HandleSuperlevel.contDiff_level
        (UnroundedTrace.handleRadius A)).contMDiff.comp (contMDiff_unchangedHandle_parameters A)
  | collar =>
      let := pieceAtlas A .collar
      exact (contMDiff_collarLevel (bump A) (UnroundedTrace.handleRadius A)).comp
        (contMDiff_collarParameters A)

omit [IsManifold (𝓡 6) ∞ M] in
theorem pieceLevel_nonneg (i : Piece) (p : pieceDomain A i) : 0 ≤ pieceLevel A i p := by
  cases i with
  | cylinder => exact (unchangedCylinderHomeomorph A p).val.property
  | handle => exact (unchangedHandleHomeomorph A p).val.property
  | collar => exact ((collarHomeomorph A).symm p).property.2.2

theorem pieceLevel_zero_iff (i : Piece) (p : pieceDomain A i) : letI := traceChartedSpace A;
    pieceLevel A i p = 0 ↔ (ProductHalfSpace.model (Vector 6)).IsBoundaryPoint p.val := by
  let := traceChartedSpace A
  let := pieceAtlas A i
  have hz : pieceLevel A i p = 0 ↔ p ∈ pieceBoundary A i := by
    cases i with
    | cylinder => exact IntervalSuperlevel.zero_iff (UnroundedTrace.height A) _
    | handle =>
        exact NoExoticSixSphere.HandleSuperlevel.zero_iff (UnroundedTrace.handleRadius_pos A) _
    | collar => rfl
  exact hz.trans ((piece_isBoundaryPoint_iff A i p).symm.trans
    ((openCover A).isBoundaryPoint_inclusion_iff i p))

theorem pieceLevel_pos_iff (i : Piece) (p : pieceDomain A i) : letI := traceChartedSpace A;
    0 < pieceLevel A i p ↔ ¬(ProductHalfSpace.model (Vector 6)).IsBoundaryPoint p.val := by
  let := traceChartedSpace A
  rw [← pieceLevel_zero_iff]
  exact lt_iff_le_and_ne.trans (and_iff_right (pieceLevel_nonneg A i p)) |>.trans ne_comm

def pieceLevelDifferential (i : Piece) (p : pieceDomain A i) : (ℝ × Vector 6) →L[ℝ] ℝ :=
  letI := pieceAtlas A i
  mvfderiv (ProductHalfSpace.model (Vector 6)) (pieceLevel A i) p

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
