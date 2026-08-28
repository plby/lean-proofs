import Wikipedia.NoExoticSixSphere.SevenDimensionalFramedAttachingProduct
import Wikipedia.NoExoticSixSphere.UnroundedTraceOriginalSlices

/-!
# The actual unrounded framed attachment to the original seven-manifold

Starting with the original embedding, its normal frame, and the embedded
three-sphere, construct the attaching product and the actual closed ambient
union of its handle with a short original-manifold cylinder. The union has
the specified attachment-quotient topology. Its continuous orthonormal trace
columns retain both piece frames and span their actual normal spaces.
Positive-height original slices are closed embedded and miss the handle.

No compactness of the original manifold is assumed. A smooth rounded
eight-dimensional boundary atlas and the induced boundary framing are not
asserted here; neither is the surgery's effect on homology.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel StabilizedSpanningDisk
open FramedAttachingProduct.UnroundedTrace
open Wikipedia.SmoothSixDPoincare

universe u

theorem exists_unroundedTrace_of_dimension_seven {M : Type u}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 7) M]
    [IsManifold (𝓡 7) ∞ M] (e : EuclideanEmbedding 7 M)
    (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
    (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f)
    (hi : Injective f) (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 7) f s)) :
    ∃ A : FramedAttachingProduct e a f,
      IsClosed (ambientSet A) ∧
      Nonempty (ClosedAttachment.Space (range (cylinderMap A)) (attachingFace A) (handleMap A)
        ≃ₜ ambientSet A) ∧
      (∀ t : Icc (0 : ℝ) (height A), IsClosedEmbedding (cylinderSlice A t)) ∧
      (∀ t : Icc (0 : ℝ) (height A), 0 < t.val → ∀ m : M,
        (cylinderSlice A t m).val ∉ range (handleMap A)) ∧
      ∃ G : C(ambientSet A,
          Vector ((e.ambientDimension - 7) + 5) →L[ℝ] Vector (e.ambientDimension + 6)),
        (∀ p w, ‖G p w‖ = ‖w‖) ∧
        (∀ p : Cylinder A, G ⟨cylinderMap A p, Or.inl ⟨p, rfl⟩⟩ =
          boundaryFrameOperator (a.orthonormal p.1).val) ∧
        (∀ p : Handle A, G ⟨handleMap A p, Or.inr ⟨p, rfl⟩⟩ =
          A.normalFrame (p.1.val, p.2.val)) ∧
        (∀ p : Cylinder A, (G ⟨cylinderMap A p, Or.inl ⟨p, rfl⟩⟩).range =
          (e.heightCylinderDerivative (p.1, p.2.val)).rangeᗮ) ∧
        ∀ p : Handle A, (G ⟨handleMap A p, Or.inr ⟨p, rfl⟩⟩).range =
          (fderiv ℝ A.map (p.1.val, p.2.val)).rangeᗮ := by
  obtain ⟨A⟩ := e.nonempty_framedAttachingProduct_of_dimension_seven a f hf hi hd
  exact ⟨A, isClosed_ambientSet A, ⟨attachmentHomeomorph A⟩,
    closedEmbedding_cylinderSlice A, cylinderSlice_not_mem_handle A, columns A,
    columns_norm A, columns_cylinder A, columns_handle A,
    columns_cylinder_range A, columns_handle_range A⟩

end NoExoticSixSphere.EuclideanEmbedding
