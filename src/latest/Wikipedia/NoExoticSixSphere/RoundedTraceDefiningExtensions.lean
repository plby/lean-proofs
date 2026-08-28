import Wikipedia.NoExoticSixSphere.RoundedTracePieceDefiningDifferential
import Wikipedia.NoExoticSixSphere.SmoothOpenCoverScalarExtension

/-!
# Total extensions of the native defining functions and their outward derivatives

Each extension is smooth on its own actual open piece. The global outward
vector is transferred through the genuine local inclusion differential before
applying the local sign theorem. No global smoothness of an unweighted
zero extension is asserted.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def extendedPieceLevel (i : Piece) : ambientSet A → ℝ :=
  (openCover A).scalarExtension i (pieceLevel A i)

theorem extendedPieceLevel_on_piece (i : Piece) (p : pieceDomain A i) :
    extendedPieceLevel A i p.val = pieceLevel A i p :=
  (openCover A).scalarExtension_on_piece i (pieceLevel A i) p

theorem extendedPieceLevel_nonneg (i : Piece) (p : ambientSet A) :
    0 ≤ extendedPieceLevel A i p :=
  (openCover A).scalarExtension_nonneg i (pieceLevel A i) (pieceLevel_nonneg A i) p

theorem extendedPieceLevel_zero_boundary (i : Piece) (p : Boundary A) :
    extendedPieceLevel A i p.val = 0 := by
  classical
  by_cases hp : p.val ∈ pieceDomain A i
  · exact (extendedPieceLevel_on_piece A i ⟨p.val, hp⟩).trans
      ((pieceLevel_zero_iff A i ⟨p.val, hp⟩).mpr p.property)
  · simp only [extendedPieceLevel, SmoothOpenCover.scalarExtension, dif_neg hp]

theorem contMDiffAt_extendedPieceLevel (i : Piece) (p : pieceDomain A i) :
    letI := traceChartedSpace A;
    ContMDiffAt (ProductHalfSpace.model (Vector 6)) 𝓘(ℝ, ℝ) ∞ (extendedPieceLevel A i) p.val :=
  (openCover A).contMDiffAt_scalarExtension i (pieceLevel A i) (contMDiff_pieceLevel A i) p

def extendedPieceLevelDifferential (i : Piece) (p : ambientSet A) :
    (ℝ × Vector 6) →L[ℝ] ℝ :=
  letI := traceChartedSpace A
  mvfderiv (ProductHalfSpace.model (Vector 6)) (extendedPieceLevel A i) p

theorem extendedPieceLevelDifferential_comp (i : Piece) (p : pieceDomain A i) :
    letI := traceChartedSpace A; letI := pieceAtlas A i;
    (extendedPieceLevelDifferential A i p.val).comp
      (show (ℝ × Vector 6) →L[ℝ] (ℝ × Vector 6) from
        mfderiv (ProductHalfSpace.model (Vector 6)) (ProductHalfSpace.model (Vector 6))
          (Subtype.val : pieceDomain A i → ambientSet A) p) = pieceLevelDifferential A i p := by
  let := traceChartedSpace A
  let := pieceAtlas A i
  have he : extendedPieceLevel A i ∘ (Subtype.val : pieceDomain A i → ambientSet A) =
      pieceLevel A i := funext (extendedPieceLevel_on_piece A i)
  have hd := mfderiv_comp p ((contMDiffAt_extendedPieceLevel A i p).mdifferentiableAt (by simp))
    (((openCover A).contMDiff_inclusion i).mdifferentiableAt (by simp))
  rw [he] at hd
  exact hd.symm

theorem extendedPieceLevelDifferential_outward (i : Piece) (p : Boundary A)
    (hp : p.val ∈ pieceDomain A i) :
    extendedPieceLevelDifferential A i p.val (outwardTraceVector A p) < 0 := by
  let := traceChartedSpace A
  let := pieceAtlas A i
  let q : pieceDomain A i := ⟨p.val, hp⟩
  let qb : boundaryPieceDomain A i := ⟨p, hp⟩
  let L : (ℝ × Vector 6) ≃L[ℝ] (ℝ × Vector 6) :=
    ((openCover A).isLocalDiffeomorphAt_inclusion i q).mfderivToContinuousLinearEquiv (by simp)
  let w := L.symm (outwardTraceVector A p)
  have hw : L w = outwardTraceVector A p := L.apply_symm_apply _
  have hd : pieceAmbientDerivative A i q = (traceAmbientDerivative A p.val).comp
      L.toContinuousLinearMap :=
    mfderiv_comp q ((trace_contMDiff_ambient A).mdifferentiableAt (by simp))
      (((openCover A).contMDiff_inclusion i).mdifferentiableAt (by simp))
  have ha : pieceAmbientDerivative A i q w = outwardNormal A p := by
    rw [hd]
    change traceAmbientDerivative A p.val (L w) = _
    rw [hw, traceDerivative_outwardTraceVector]
  have hn := pieceLevelDifferential_outward_negative A i qb w ha
  have ht := congrArg (fun D : (ℝ × Vector 6) →L[ℝ] ℝ ↦ D w)
    (extendedPieceLevelDifferential_comp A i q)
  change extendedPieceLevelDifferential A i p.val (L w) = pieceLevelDifferential A i q w at ht
  rw [hw] at ht
  rw [ht]
  exact hn

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
