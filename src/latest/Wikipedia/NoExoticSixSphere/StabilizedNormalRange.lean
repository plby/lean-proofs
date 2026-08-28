import Wikipedia.NoExoticSixSphere.PartialFrameBlockRanges

/-!
# Actual normal spaces after adding zero coordinates

The orthogonal complement of a stabilized derivative is the old normal
space plus the full added coordinate block. In particular, block-stabilizing
an actual full normal frame still spans exactly that orthogonal complement.
-/

noncomputable section

namespace NoExoticSixSphere

open GLOrthonormalization Stiefel

theorem inner_appendZero_left {N m : ℕ} (x : Vector N) (y : Vector (N + m)) :
    inner ℝ (appendZeroMap N m x) y =
      inner ℝ x (EuclideanSpace.finAddEquivProd y).1 := by
  rw [inner_finAdd_split (n := N) (m := m)]
  change inner ℝ (EuclideanSpace.finAddEquivProd
    (EuclideanSpace.finAddEquivProd.symm (x, (0 : Vector m)))).1 _ +
    inner ℝ (EuclideanSpace.finAddEquivProd
      (EuclideanSpace.finAddEquivProd.symm (x, (0 : Vector m)))).2 _ = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  simp

theorem mem_normal_appendZero {d N : ℕ} (m : ℕ) (D : Vector d →L[ℝ] Vector N)
    (y : Vector (N + m)) :
    y ∈ ((appendZeroMap N m).comp D).rangeᗮ ↔
      (EuclideanSpace.finAddEquivProd y).1 ∈ D.rangeᗮ := by
  rw [Submodule.mem_orthogonal, Submodule.mem_orthogonal]
  constructor
  · intro h u hu
    obtain ⟨v, rfl⟩ := hu
    have hv := h ((appendZeroMap N m).comp D v) ⟨v, rfl⟩
    exact (inner_appendZero_left (D v) y).symm.trans hv
  · intro h u hu
    obtain ⟨v, rfl⟩ := hu
    change inner ℝ (appendZeroMap N m (D v)) y = 0
    rw [inner_appendZero_left]
    exact h (D v) ⟨v, rfl⟩

theorem range_blockFrame_normal {d N k : ℕ} (m : ℕ) (D : Vector d →L[ℝ] Vector N)
    (a : Space N k) (ha : a.val.range ≤ D.rangeᗮ) :
    (BlockSum.frame m a).val.range ≤ ((appendZeroMap N m).comp D).rangeᗮ := by
  intro y hy
  exact (mem_normal_appendZero m D y).mpr (ha ((BlockSum.mem_range_frame m a y).mp hy))

theorem range_blockFrame_eq_normal {d N k : ℕ} (m : ℕ) (D : Vector d →L[ℝ] Vector N)
    (a : Space N k) (ha : a.val.range = D.rangeᗮ) :
    (BlockSum.frame m a).val.range = ((appendZeroMap N m).comp D).rangeᗮ := by
  ext y
  rw [BlockSum.mem_range_frame, mem_normal_appendZero, ha]

end NoExoticSixSphere
