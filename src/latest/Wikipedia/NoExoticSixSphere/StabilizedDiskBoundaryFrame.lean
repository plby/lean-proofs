import Wikipedia.NoExoticSixSphere.EuclideanBlockInner

/-!
# The partial boundary frame of the stabilized four-disk

The old normal columns and the five graph-coordinate axes form an actual
orthonormal partial frame. The height coordinate is excluded: it supplies
the disk's radial tangent direction at the boundary.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.StabilizedSpanningDisk

open GLOrthonormalization Stiefel

def boundaryFrameOperator {N k : ℕ} (a : Vector k →L[ℝ] Vector N) :
    Vector (k + 5) →L[ℝ] Vector (N + 6) :=
  (coordinates N 4).toContinuousLinearMap.comp
    ((((ContinuousLinearMap.inl ℝ (Vector N) ℝ).comp a).prodMap
      (DiskGraph.extraCoordinates 4).symm.toContinuousLinearMap).comp
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := k) (m := 5)).toContinuousLinearMap)

theorem boundaryFrameOperator_apply {N k : ℕ} (a : Vector k →L[ℝ] Vector N)
    (w : Vector (k + 5)) :
    boundaryFrameOperator a w = coordinates N 4
      ((a (EuclideanSpace.finAddEquivProd w).1, 0),
        (DiskGraph.extraCoordinates 4).symm (EuclideanSpace.finAddEquivProd w).2) := rfl

theorem inner_boundaryFrameOperator {N k : ℕ} (a : Space N k) (u v : Vector (k + 5)) :
    inner ℝ (boundaryFrameOperator a.val u) (boundaryFrameOperator a.val v) =
      inner ℝ u v := by
  rw [boundaryFrameOperator_apply, boundaryFrameOperator_apply, inner_coordinates]
  simp only [inner_zero_left, zero_add]
  rw [← DiskGraph.inner_extraCoordinates 4,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
  have ha := (toIsometry a).inner_map_map
    (EuclideanSpace.finAddEquivProd u).1 (EuclideanSpace.finAddEquivProd v).1
  change inner ℝ (a.val _) (a.val _) = _ at ha
  rw [ha]
  exact (inner_finAdd_split u v).symm

theorem norm_boundaryFrameOperator {N k : ℕ} (a : Space N k) (w : Vector (k + 5)) :
    ‖boundaryFrameOperator a.val w‖ = ‖w‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simpa only [real_inner_self_eq_norm_sq] using inner_boundaryFrameOperator a w w

def boundaryFrame {N k : ℕ} (a : Space N k) : Space (N + 6) (k + 5) :=
  ⟨boundaryFrameOperator a.val, norm_boundaryFrameOperator a⟩

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem contMDiff_boundaryFrameOperator {N k : ℕ} {a : M → Vector k →L[ℝ] Vector N}
    (ha : ContMDiff I 𝓘(ℝ, Vector k →L[ℝ] Vector N) ∞ a) :
    ContMDiff I 𝓘(ℝ, Vector (k + 5) →L[ℝ] Vector (N + 6)) ∞
      (fun x ↦ boundaryFrameOperator (a x)) := by
  exact contMDiff_const.clm_comp
    (((contMDiff_const.clm_comp ha).clm_prodMap contMDiff_const).clm_comp contMDiff_const)

end NoExoticSixSphere.StabilizedSpanningDisk
