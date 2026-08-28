import Wikipedia.HopfProblem.TrianglePeriodFamilyLatticeLinear

/-!
# The actual triangle representation preserves the γ coordinate

The first real coordinate is fixed by the two original matrices.
Generation by those two elements extends that identity to the entire
actual triangle group, including inverses.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.GammaZero

open SpecialPeriods
open scoped Matrix

/-- The first original dual generator preserves the literal real γ coordinate. -/
theorem triangleRealEquiv_generator₁_gamma (x : RealPlane₄) :
    triangleRealEquiv triangleGenerator₁ x 0 = x 0 := by
  rw [triangleRealEquiv_apply, triangleDualRepresentation_generator₁_matrix]
  simp [A₁, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- The second original dual generator preserves the same literal coordinate. -/
theorem triangleRealEquiv_generator₂_gamma (x : RealPlane₄) :
    triangleRealEquiv triangleGenerator₂ x 0 = x 0 := by
  rw [triangleRealEquiv_apply, triangleDualRepresentation_generator₂_matrix]
  simp [A₂, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- Every actual triangle deck transformation fixes the real γ coordinate. -/
theorem triangleRealEquiv_gamma (g : TriangleGroup) (x : RealPlane₄) :
    triangleRealEquiv g x 0 = x 0 := by
  have hg : g ∈ Subgroup.closure
      ({triangleGenerator₁, triangleGenerator₂} : Set TriangleGroup) := by
    rw [triangle_generators_generate]
    exact Subgroup.mem_top g
  have h : ∀ x : RealPlane₄, triangleRealEquiv g x 0 = x 0 := by
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
        rcases Set.mem_insert_iff.mp hg with rfl | hg
        · exact triangleRealEquiv_generator₁_gamma
        · have he : g = triangleGenerator₂ := Set.mem_singleton_iff.mp hg
          subst g
          exact triangleRealEquiv_generator₂_gamma
    | one =>
        intro y
        rw [triangleRealEquiv_one]
        rfl
    | mul g h _ _ ihg ihh =>
        intro y
        rw [triangleRealEquiv_mul_apply, ihg, ihh]
    | inv g _ ihg =>
        intro y
        have hy := ihg (triangleRealEquiv g⁻¹ y)
        rw [← triangleRealEquiv_mul_apply, mul_inv_cancel, triangleRealEquiv_one] at hy
        exact hy.symm
  exact h x

end Wikipedia.HopfProblem.TrianglePeriodFamily.GammaZero
