import ErdosProblems.Erdos1038.EmpiricalPotential

/-!
# Boundary finiteness of polynomial sublevel sets

Every finite boundary point of `{x : |f x| < 1}` is a zero of `f^2 - 1`.
For an admissible nonconstant polynomial that auxiliary polynomial is
nonzero, so the boundary is finite.  This is the first topological input to
the simultaneous component-atomization argument.
-/

open Set Polynomial

namespace Erdos1038

noncomputable section

theorem frontier_sublevelSet_abs_eval_eq_one (f : Polynomial ℝ) :
    frontier (sublevelSet f) ⊆ {x | |f.eval x| = 1} := by
  intro x hx
  rw [frontier, (isOpen_sublevelSet f).interior_eq] at hx
  have hclosed : IsClosed {y : ℝ | |f.eval y| ≤ 1} :=
    isClosed_le f.continuous.abs continuous_const
  have hsubset : sublevelSet f ⊆ {y : ℝ | |f.eval y| ≤ 1} := by
    intro y hy
    change |f.eval y| < 1 at hy
    exact le_of_lt hy
  have hxle : |f.eval x| ≤ 1 := closure_minimal hsubset hclosed hx.1
  have hxge : 1 ≤ |f.eval x| := by
    apply le_of_not_gt
    intro h
    exact hx.2 h
  exact le_antisymm hxle hxge

theorem sq_sub_one_ne_zero {f : Polynomial ℝ} (hf : IsAdmissible f) :
    f ^ 2 - 1 ≠ 0 := by
  intro hzero
  have heq : f ^ 2 = 1 := sub_eq_zero.mp hzero
  have hdegree : (f ^ 2).natDegree = 2 * f.natDegree :=
    hf.monic.natDegree_pow 2
  rw [heq] at hdegree
  have hpos := hf.monic.natDegree_pos.mpr hf.ne_one
  simp at hdegree
  omega

theorem frontier_sublevelSet_subset_rootSet_sq_sub_one
    {f : Polynomial ℝ} (hf : IsAdmissible f) :
    frontier (sublevelSet f) ⊆ rootSet (f ^ 2 - 1) := by
  intro x hx
  have habs := frontier_sublevelSet_abs_eval_eq_one f hx
  rw [mem_rootSet_iff, Polynomial.mem_roots (sq_sub_one_ne_zero hf)]
  change (f ^ 2 - 1).eval x = 0
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_one]
  have hsquare : (f.eval x) ^ 2 = 1 := by
    rw [← sq_abs, habs]
    norm_num
  linarith

/-- The sublevel set has finitely many finite boundary points. -/
theorem finite_frontier_sublevelSet {f : Polynomial ℝ}
    (hf : IsAdmissible f) :
    (frontier (sublevelSet f)).Finite :=
  (rootSet_finite (f ^ 2 - 1)).subset
    (frontier_sublevelSet_subset_rootSet_sq_sub_one hf)

end

end Erdos1038
