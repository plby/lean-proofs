/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularDecoratedRenewalKernel

/-!
# Row bounds for recursively decorated renewals

The pathwise erased-parent construction inserts a refined child return
between the inward hit and the remaining parent spine.  For upper bounds it
is enough to control the *row sum* of every refined child return.  No
pointwise division by the unrestricted return kernel is needed.

This is the algebra used by the recursive profile assembler: one inward-row
factor is paid for every child, the child row costs are each paid exactly
once, and the final escape row is paid once.
-/

open scoped BigOperators ENNReal

namespace Erdos1165.AnnularDecoratedRenewalRow

open AnnularDecoratedRenewalKernel

noncomputable section

/-- Summing one composed cycle over its return endpoint uses only the inward
row and the row sum of the decorated child return. -/
theorem sum_composedCycleKernel_le_mul
    {Middle Inner : Type*} [Fintype Middle] [Fintype Inner]
    (inward : Middle → Inner → ℝ≥0∞)
    (childKernel : Inner → Middle → ℝ≥0∞)
    (inwardUpper childUpper : ℝ≥0∞)
    (hinward : ∀ u, ∑ z, inward u z ≤ inwardUpper)
    (hchild : ∀ z, ∑ v, childKernel z v ≤ childUpper)
    (u : Middle) :
    ∑ v, composedCycleKernel inward childKernel u v ≤
      inwardUpper * childUpper := by
  calc
    ∑ v, composedCycleKernel inward childKernel u v =
        ∑ z, inward u z * ∑ v, childKernel z v := by
      unfold composedCycleKernel
      calc
        ∑ v, ∑ z, inward u z * childKernel z v =
            ∑ z, ∑ v, inward u z * childKernel z v := Finset.sum_comm
        _ = ∑ z, inward u z * ∑ v, childKernel z v := by
          apply Finset.sum_congr rfl
          intro z _
          rw [Finset.mul_sum]
    _ ≤ ∑ z, inward u z * childUpper := by
      apply Finset.sum_le_sum
      intro z _
      exact mul_le_mul' le_rfl (hchild z)
    _ = (∑ z, inward u z) * childUpper := by rw [Finset.sum_mul]
    _ ≤ inwardUpper * childUpper := by
      exact mul_le_mul' (hinward u) le_rfl

/-- Row-sum upper bound for a chronologically decorated renewal.

Unlike a pointwise comparison with an unrestricted return kernel, this
statement remains valid when a refined child row has zeros at some exit
points.  This is the weakest sound input needed for the profile recursion. -/
theorem sum_decoratedRenewalKernel_le_rowProduct
    {Middle Inner Exit Child : Type*}
    [Fintype Middle] [Fintype Inner] [Fintype Exit]
    (inward : Middle → Inner → ℝ≥0∞)
    (childKernel : Child → Inner → Middle → ℝ≥0∞)
    (escape : Middle → Exit → ℝ≥0∞)
    (inwardUpper escapeUpper : ℝ≥0∞)
    (childUpper : Child → ℝ≥0∞)
    (hinward : ∀ u, ∑ z, inward u z ≤ inwardUpper)
    (hchild : ∀ child z, ∑ v, childKernel child z v ≤ childUpper child)
    (hescape : ∀ u, ∑ w, escape u w ≤ escapeUpper) :
    ∀ (children : List Child) (u : Middle),
      ∑ w, decoratedRenewalKernel inward childKernel escape children u w ≤
        (children.map childUpper).prod *
          inwardUpper ^ children.length * escapeUpper := by
  intro children
  induction children with
  | nil =>
      intro u
      simpa using hescape u
  | cons child children ih =>
      intro u
      change (∑ w, ∑ v,
        composedCycleKernel inward (childKernel child) u v *
          decoratedRenewalKernel inward childKernel escape children v w) ≤ _
      let tailUpper := (children.map childUpper).prod *
        inwardUpper ^ children.length * escapeUpper
      calc
        ∑ w, ∑ v,
            composedCycleKernel inward (childKernel child) u v *
              decoratedRenewalKernel inward childKernel escape children v w =
            ∑ v, composedCycleKernel inward (childKernel child) u v *
              ∑ w, decoratedRenewalKernel inward childKernel escape
                children v w := by
          calc
            ∑ w, ∑ v,
                composedCycleKernel inward (childKernel child) u v *
                  decoratedRenewalKernel inward childKernel escape children v w =
                ∑ v, ∑ w,
                  composedCycleKernel inward (childKernel child) u v *
                    decoratedRenewalKernel inward childKernel escape children v w :=
              Finset.sum_comm
            _ = _ := by
              apply Finset.sum_congr rfl
              intro v _
              rw [Finset.mul_sum]
        _ ≤ ∑ v, composedCycleKernel inward (childKernel child) u v *
              tailUpper := by
          apply Finset.sum_le_sum
          intro v _
          exact mul_le_mul' le_rfl (ih v)
        _ = (∑ v, composedCycleKernel inward (childKernel child) u v) *
              tailUpper := by rw [Finset.sum_mul]
        _ ≤ (inwardUpper * childUpper child) * tailUpper := by
          exact mul_le_mul'
            (sum_composedCycleKernel_le_mul inward (childKernel child)
              inwardUpper (childUpper child) hinward (hchild child) u) le_rfl
        _ = ((child :: children).map childUpper).prod *
              inwardUpper ^ (child :: children).length * escapeUpper := by
          simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ,
            tailUpper]
          ac_rfl

end

end Erdos1165.AnnularDecoratedRenewalRow
