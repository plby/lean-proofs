import Wikipedia.HopfProblem.DegreeCollapseLowHeightUnit
import Wikipedia.NoExoticSixSphere.OrthogonalFrameAppend

/-!

# The exact low-dimensional original-end column permutation

The induced frame lists the original normal columns, the graph axes, and
then the height axis. This explicit isometric permutation compares it with
ordinary block stabilization while retaining every coordinate and sign.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

open NoExoticSixSphere GLOrthonormalization StabilizedSpanningDisk

variable (d : ℕ)

def endColumnCoordinates (k : ℕ) : Vector ((k + (1 + (d + 1))) + 1) ≃L[ℝ]
    Vector (k + (1 + (1 + (d + 1)))) :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := k + (1 + (d + 1))) (m := 1)).trans
    (((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := k) (m := 1 + (d + 1))).prodCongr
      EuclideanTailCoordinates.scalar.symm.toContinuousLinearEquiv).trans
        ((ContinuousLinearEquiv.prodAssoc ℝ (Vector k) (Vector (1 + (d + 1))) ℝ).trans
          (((ContinuousLinearEquiv.refl ℝ (Vector k)).prodCongr
            ((ContinuousLinearEquiv.prodComm ℝ (Vector (1 + (d + 1))) ℝ).trans
              (DiskGraph.extraCoordinates (1 + (d + 1))))).trans
                EuclideanSpace.finAddEquivProd.symm)))

theorem endColumnCoordinates_apply (k : ℕ) (w : Vector ((k + (1 + (d + 1))) + 1)) :
    endColumnCoordinates d k w = EuclideanSpace.finAddEquivProd.symm
      ((EuclideanSpace.finAddEquivProd (EuclideanSpace.finAddEquivProd w).1).1,
        DiskGraph.extraCoordinates (1 + (d + 1))
          (EuclideanTailCoordinates.scalar.symm (EuclideanSpace.finAddEquivProd w).2,
            (EuclideanSpace.finAddEquivProd (EuclideanSpace.finAddEquivProd w).1).2)) := rfl

theorem inner_endColumnCoordinates (k : ℕ) (u v : Vector ((k + (1 + (d + 1))) + 1)) :
    inner ℝ (endColumnCoordinates d k u) (endColumnCoordinates d k v) = inner ℝ u v := by
  rw [endColumnCoordinates_apply d, endColumnCoordinates_apply d, inner_finAdd_symm,
    DiskGraph.inner_extraCoordinates]
  rw [EuclideanTailCoordinates.scalar.symm.inner_map_map]
  rw [inner_finAdd_split u v,
    inner_finAdd_split (EuclideanSpace.finAddEquivProd u).1
      (EuclideanSpace.finAddEquivProd v).1]
  ring

def endColumnPermutation (k : ℕ) : Vector ((k + (1 + (d + 1))) + 1) ≃ₗᵢ[ℝ]
    Vector (k + (1 + (1 + (d + 1)))) where
  toLinearEquiv := (endColumnCoordinates d k).toLinearEquiv
  norm_map' w := by
    change ‖endColumnCoordinates d k w‖ = ‖w‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simpa only [real_inner_self_eq_norm_sq] using inner_endColumnCoordinates d k w w

theorem endColumnPermutation_apply (k : ℕ) (w : Vector ((k + (1 + (d + 1))) + 1)) :
    endColumnPermutation d k w = endColumnCoordinates d k w := rfl

theorem append_heightUnit_apply {N k : ℕ} (B : Vector k →L[ℝ] Vector N)
    (w : Vector ((k + (1 + (d + 1))) + 1)) :
    OrthogonalFrameAppend.operator (boundaryFrameOperator d B) (heightUnit d N) w =
      coordinates N (d + 1)
        ((B (EuclideanSpace.finAddEquivProd (EuclideanSpace.finAddEquivProd w).1).1,
          EuclideanTailCoordinates.scalar.symm (EuclideanSpace.finAddEquivProd w).2),
          (DiskGraph.extraCoordinates (d + 1)).symm
            (EuclideanSpace.finAddEquivProd (EuclideanSpace.finAddEquivProd w).1).2) := by
  rw [OrthogonalFrameAppend.operator_apply, boundaryFrameOperator_apply, smul_heightUnit,
    ← map_add]
  congr 1
  simp

theorem append_heightUnit_eq_block {N k : ℕ} (B : Vector k →L[ℝ] Vector N) :
    OrthogonalFrameAppend.operator (boundaryFrameOperator d B) (heightUnit d N) =
      (Stiefel.BlockSum.operator (1 + (1 + (d + 1))) B).comp
        (endColumnPermutation d k).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro w
  change OrthogonalFrameAppend.operator (boundaryFrameOperator d B) (heightUnit d N) w =
    Stiefel.BlockSum.operator (1 + (1 + (d + 1))) B (endColumnPermutation d k w)
  rw [append_heightUnit_apply d, endColumnPermutation_apply d, endColumnCoordinates_apply d,
    Stiefel.BlockSum.operator_apply, ContinuousLinearEquiv.apply_symm_apply]
  change EuclideanSpace.finAddEquivProd.symm
    (_, DiskGraph.extraCoordinates (1 + (d + 1)) (_, DiskGraph.extraCoordinates (d + 1)
      ((DiskGraph.extraCoordinates (d + 1)).symm _))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rfl

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery
