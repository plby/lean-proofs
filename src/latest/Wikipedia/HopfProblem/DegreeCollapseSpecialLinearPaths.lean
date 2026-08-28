import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Connected.PathConnected

/-!
# Elementary paths for matching transverse frames

Transvections have literal scalar-parameter paths. The diagonal determinant-one
generators decompose into transvections, giving a path to identity by the
matrix special-linear induction theorem.
-/

noncomputable section

open Matrix Set
open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.LinearFramePaths

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem diag2n_decompose {i j : ι} (hij : i ≠ j) (a : ℝ) (ha : a ≠ 0) :
    SpecialLinearGroup.diag2n hij a ha =
      SpecialLinearGroup.transvection hij a *
      SpecialLinearGroup.transvection hij.symm (-a⁻¹) *
      SpecialLinearGroup.transvection hij a *
      SpecialLinearGroup.transvection hij (-1) *
      SpecialLinearGroup.transvection hij.symm 1 *
      SpecialLinearGroup.transvection hij (-1) := by
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul, SpecialLinearGroup.diag2n_coe,
    SpecialLinearGroup.transvection_coe]
  ext k l
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
    by_cases hli : l = i <;> by_cases hlj : l = j <;>
    simp_all [mul_add, add_mul, diagonal_apply,
      Matrix.one_apply, Matrix.single_apply, eq_comm]

/-- Every real transvection is joined to the identity by scaling its off-diagonal entry. -/
theorem joined_one_transvection {i j : ι} (hij : i ≠ j) (a : ℝ) :
    Joined (1 : SpecialLinearGroup ι ℝ) (SpecialLinearGroup.transvection hij a) := by
  refine ⟨{
    toFun := fun t => SpecialLinearGroup.transvection hij ((t : ℝ) * a)
    continuous_toFun := ?_
    source' := by simp
    target' := by simp }⟩
  apply Continuous.subtype_mk
  change Continuous (fun t : unitInterval => (1 : Matrix ι ι ℝ) + Matrix.single i j ((t : ℝ) * a))
  apply continuous_pi
  intro k
  apply continuous_pi
  intro l
  simp only [Matrix.add_apply, Matrix.single_apply]
  by_cases h : i = k ∧ j = l
  · simp only [h, and_self, ite_true]
    fun_prop
  · simp only [h, ite_false]
    fun_prop

/-- Every real special-linear matrix in positive rank at least two is joined to identity. -/
theorem joined_one_specialLinear [Nontrivial ι] (A : SpecialLinearGroup ι ℝ) :
    Joined (1 : SpecialLinearGroup ι ℝ) A := by
  apply SpecialLinearGroup.diagonal_transvection_induction'
    (fun A => Joined (1 : SpecialLinearGroup ι ℝ) A) A
  · intro i j hij a ha
    rw [diag2n_decompose hij a ha]
    have hmul {A B : SpecialLinearGroup ι ℝ} (hA : Joined 1 A) (hB : Joined 1 B) :
        Joined 1 (A * B) := by simpa only [one_mul] using hA.mul hB
    exact hmul (hmul (hmul (hmul (hmul (joined_one_transvection hij a)
      (joined_one_transvection hij.symm (-a⁻¹))) (joined_one_transvection hij a))
      (joined_one_transvection hij (-1))) (joined_one_transvection hij.symm 1))
      (joined_one_transvection hij (-1))
  · exact fun i j hij a => joined_one_transvection hij a
  · intro A B hA hB
    simpa only [one_mul] using hA.mul hB

end Wikipedia.HopfProblem.DegreeCollapse.LinearFramePaths
