import Wikipedia.HopfProblem.DegreeCollapsePathPostcomposition

/-!
# Smooth nonlinear postcomposition on continuous path spaces

Induction on finite differentiability order uses the proved Fréchet
derivative, the same assertion for the original derivative map, and the
bounded linear coefficient-path operator. Passing to all finite orders
gives full smoothness in the Banach-space sup norm.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SmoothODE

universe u v

variable {K : Type v} [TopologicalSpace K] [CompactSpace K]
  {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- All finite smoothness orders for nonlinear postcomposition, uniformly over the codomain. -/
theorem contDiff_pathPostcomposition_nat (n : ℕ) :
    ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F],
      ∀ (f : C(E, F)), ContDiff ℝ ∞ f →
        ContDiff ℝ n (fun w : C(K, E) => f.comp w) := by
  induction n with
  | zero =>
    intro F _ _ f _
    exact contDiff_zero.mpr f.continuous_postcomp
  | succ n ih =>
    intro F _ _ f hf
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv]
    refine ⟨fun w => (hasFDerivAt_pathPostcomposition f hf w).differentiableAt, by simp, ?_⟩
    let df : C(E, E →L[ℝ] F) := ⟨fderiv ℝ f, hf.continuous_fderiv (by simp)⟩
    have hdf : ContDiff ℝ ∞ df := hf.fderiv_right (by simp)
    have hi := ih df hdf
    have heq : fderiv ℝ (fun w : C(K, E) => f.comp w) =
        fun w => pathOperator (df.comp w) := by
      funext w
      rw [fderiv_pathPostcomposition f hf w]
      rfl
    rw [heq]
    exact (pathOperatorCLM (K := K) (E := E) (F := F)).contDiff.comp hi

/-- Smoothness of the actual nonlinear path-space postcomposition map. -/
theorem contDiff_pathPostcomposition {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : C(E, F)) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun w : C(K, E) => f.comp w) :=
  contDiff_infty.mpr (fun n => contDiff_pathPostcomposition_nat n f hf)

end Wikipedia.HopfProblem.DegreeCollapse.SmoothODE
