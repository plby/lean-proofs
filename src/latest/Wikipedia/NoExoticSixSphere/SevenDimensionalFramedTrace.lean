import Wikipedia.NoExoticSixSphere.SevenDimensionalRoundedAttachment
import Wikipedia.NoExoticSixSphere.RoundedTraceNormalFrame

/-!
# A genuine smooth normally framed eight-dimensional rounded trace

The original seven-manifold embedding, its normal frame, and a smooth
embedded immersive three-sphere construct the actual rounded ambient set.
Its constructed global half-space atlas retains the ambient subtype
topology. The actual inclusion is smooth, immersive, and closed embedded.
A global smooth orthonormal frame spans its actual normal space, including
at boundary points, and agrees exactly with all three prescribed piece frames.

The original manifold need not be compact. Identifying the induced end
framings and proving the surgery's effects on homology and connectivity
remain separate obligations. The six-sphere classification is not asserted.
-/

noncomputable section

open Function Set Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel FramedAttachingProduct.RoundedTrace

universe u

theorem exists_framedTrace_of_dimension_seven {M : Type u}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 7) M]
    [IsManifold (𝓡 7) ∞ M] (e : EuclideanEmbedding 7 M)
    (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
    (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f)
    (hi : Injective f) (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 7) f s)) :
    ∃ A : FramedAttachingProduct e a f, letI := traceChartedSpace A;
      IsManifold (ProductHalfSpace.model (Vector 7)) ∞ (ambientSet A) ∧
      IsClosedEmbedding ((↑) : ambientSet A → Vector (e.ambientDimension + 6)) ∧
      ContMDiff (ProductHalfSpace.model (Vector 7)) (𝓡 (e.ambientDimension + 6)) ∞
        ((↑) : ambientSet A → Vector (e.ambientDimension + 6)) ∧
      (∀ p : ambientSet A, Injective (traceAmbientDerivative A p)) ∧
      ∃ G : ambientSet A → Vector ((e.ambientDimension - 7) + 5) →L[ℝ]
          Vector (e.ambientDimension + 6),
        ContMDiff (ProductHalfSpace.model (Vector 7))
          𝓘(ℝ, Vector ((e.ambientDimension - 7) + 5) →L[ℝ]
            Vector (e.ambientDimension + 6)) ∞ G ∧
        (∀ p w, ‖G p w‖ = ‖w‖) ∧
        (∀ p, (G p).range = (traceAmbientDerivative A p).rangeᗮ) ∧
        ∀ i : Piece, ∀ p : pieceDomain A i, G p.val = pieceNormalFrame A i p := by
  obtain ⟨A⟩ := e.nonempty_framedAttachingProduct_of_dimension_seven a f hf hi hd
  refine ⟨A, ?_⟩
  let := traceChartedSpace A
  exact ⟨trace_isManifold A, (isClosed_ambientSet A).isClosedEmbedding_subtypeVal,
    trace_contMDiff_ambient A, injective_traceAmbientDerivative A,
    traceNormalFrame A, contMDiff_traceNormalFrame A, traceNormalFrame_norm A,
    traceNormalFrame_range A, traceNormalFrame_on_piece A⟩

end NoExoticSixSphere.EuclideanEmbedding
