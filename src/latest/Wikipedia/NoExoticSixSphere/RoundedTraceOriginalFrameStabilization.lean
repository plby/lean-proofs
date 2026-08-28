import Wikipedia.NoExoticSixSphere.RoundedTraceCylinderOutwardNormal

/-!
# Exact original-end stabilization, including the fixed column permutation

The induced convention lists the original normal columns, the five graph
axes, then the positive height axis. Ordinary block stabilization lists the
height axis before the five graph axes. The following explicit isometric
coordinate permutation accounts for this difference.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.StabilizedSpanningDisk

open GLOrthonormalization

def endColumnCoordinates (k : ℕ) : Vector ((k + 5) + 1) ≃L[ℝ] Vector (k + 6) :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := k + 5) (m := 1)).trans
    (((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := k) (m := 5)).prodCongr
      EuclideanTailCoordinates.scalar.symm.toContinuousLinearEquiv).trans
        ((ContinuousLinearEquiv.prodAssoc ℝ (Vector k) (Vector 5) ℝ).trans
          (((ContinuousLinearEquiv.refl ℝ (Vector k)).prodCongr
            ((ContinuousLinearEquiv.prodComm ℝ (Vector 5) ℝ).trans
              (DiskGraph.extraCoordinates 5))).trans EuclideanSpace.finAddEquivProd.symm)))

theorem endColumnCoordinates_apply (k : ℕ) (w : Vector ((k + 5) + 1)) :
    endColumnCoordinates k w = EuclideanSpace.finAddEquivProd.symm
      ((EuclideanSpace.finAddEquivProd (EuclideanSpace.finAddEquivProd w).1).1,
        DiskGraph.extraCoordinates 5
          (EuclideanTailCoordinates.scalar.symm (EuclideanSpace.finAddEquivProd w).2,
            (EuclideanSpace.finAddEquivProd (EuclideanSpace.finAddEquivProd w).1).2)) := rfl

theorem inner_endColumnCoordinates (k : ℕ) (u v : Vector ((k + 5) + 1)) :
    inner ℝ (endColumnCoordinates k u) (endColumnCoordinates k v) = inner ℝ u v := by
  rw [endColumnCoordinates_apply, endColumnCoordinates_apply, inner_finAdd_symm,
    DiskGraph.inner_extraCoordinates]
  rw [EuclideanTailCoordinates.scalar.symm.inner_map_map]
  rw [inner_finAdd_split u v,
    inner_finAdd_split (EuclideanSpace.finAddEquivProd u).1
      (EuclideanSpace.finAddEquivProd v).1]
  ring

def endColumnPermutation (k : ℕ) : Vector ((k + 5) + 1) ≃ₗᵢ[ℝ] Vector (k + 6) where
  toLinearEquiv := (endColumnCoordinates k).toLinearEquiv
  norm_map' w := by
    change ‖endColumnCoordinates k w‖ = ‖w‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simpa only [real_inner_self_eq_norm_sq] using inner_endColumnCoordinates k w w

theorem endColumnPermutation_apply (k : ℕ) (w : Vector ((k + 5) + 1)) :
    endColumnPermutation k w = endColumnCoordinates k w := rfl

theorem append_heightUnit_apply {N k : ℕ} (B : Vector k →L[ℝ] Vector N)
    (w : Vector ((k + 5) + 1)) :
    OrthogonalFrameAppend.operator (boundaryFrameOperator B) (heightUnit N) w =
      coordinates N 4
        ((B (EuclideanSpace.finAddEquivProd (EuclideanSpace.finAddEquivProd w).1).1,
          EuclideanTailCoordinates.scalar.symm (EuclideanSpace.finAddEquivProd w).2),
          (DiskGraph.extraCoordinates 4).symm
            (EuclideanSpace.finAddEquivProd (EuclideanSpace.finAddEquivProd w).1).2) := by
  rw [OrthogonalFrameAppend.operator_apply, boundaryFrameOperator_apply, smul_heightUnit,
    ← map_add]
  congr 1
  simp

theorem append_heightUnit_eq_block {N k : ℕ} (B : Vector k →L[ℝ] Vector N) :
    OrthogonalFrameAppend.operator (boundaryFrameOperator B) (heightUnit N) =
      (Stiefel.BlockSum.operator 6 B).comp (endColumnPermutation k).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro w
  change OrthogonalFrameAppend.operator (boundaryFrameOperator B) (heightUnit N) w =
    Stiefel.BlockSum.operator 6 B (endColumnPermutation k w)
  rw [append_heightUnit_apply, endColumnPermutation_apply, endColumnCoordinates_apply,
    Stiefel.BlockSum.operator_apply, ContinuousLinearEquiv.apply_symm_apply]
  change EuclideanSpace.finAddEquivProd.symm
    (_, DiskGraph.extraCoordinates 5 (_, DiskGraph.extraCoordinates 4
      ((DiskGraph.extraCoordinates 4).symm _))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rfl

end NoExoticSixSphere.StabilizedSpanningDisk

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem inducedBoundaryFrame_original_stabilization (m : M) :
    letI := boundaryChartedSpace A;
    inducedBoundaryFrame A (originalBoundaryDiffeomorph A m).val =
      (BlockSum.operator 6 (a.orthonormal m).val).comp
        (endColumnPermutation (e.ambientDimension - 6)).toContinuousLinearMap := by
  let := boundaryChartedSpace A
  rw [inducedBoundaryFrame_originalBoundary, append_heightUnit_eq_block]

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
