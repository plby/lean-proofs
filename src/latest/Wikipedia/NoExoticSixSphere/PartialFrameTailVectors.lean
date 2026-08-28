import Wikipedia.NoExoticSixSphere.PartialFrameColumnFiber

/-!
# Actual complement vectors in the column-fiber coordinates

The complement coordinate is an actual ambient vector orthogonal to the
specified unit column. Reconstruction carries such source vectors to the
corresponding target complement vectors, with no atlas or basis replacement.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.ColumnFiber

open GLOrthonormalization ColumnCoordinates FixedColumnBlock

variable {n r : ℕ}

local instance vectorDimension (m : ℕ) :
    Fact (Module.finrank ℝ (Vector (m + 1)) = m + 1) := ⟨finrank_euclideanSpace_fin⟩

def tailVector (v : UnitSphere (Vector (r + 1))) (z : Vector r) : Vector (r + 1) :=
  (complement v).symm z

theorem tailVector_inner (v : UnitSphere (Vector (r + 1))) (z : Vector r) :
    inner ℝ v.val (tailVector v z) = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_right.mp ((complement v).symm z).property

theorem tailVector_norm (v : UnitSphere (Vector (r + 1))) (z : Vector r) :
    ‖tailVector v z‖ = ‖z‖ := (complement v).symm.norm_map z

theorem split_tailVector (v : UnitSphere (Vector (r + 1))) (z : Vector r) :
    split v (tailVector v z) = tailInclusion z := by
  apply (split v).symm.injective
  rw [LinearIsometryEquiv.symm_apply_apply, split_symm_apply]
  simp [tailInclusion, tailVector]

theorem reconstruct_tailVector (v : UnitSphere (Vector (r + 1)))
    (c : UnitSphere (Vector (n + 1))) (q : Stiefel.Space n r) (z : Vector r) :
    (reconstruct v c q).val (tailVector v z) = tailVector c (q.val z) := by
  rw [reconstruct_apply, split_tailVector, RectangularColumnBlock.block_apply, split_symm_apply]
  simp [tailInclusion, tailVector]

end NoExoticSixSphere.Stiefel.ColumnFiber
