import Wikipedia.SmoothSixDPoincare.IntegerPresentation
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.Matrix.Mul

/-!
# The actual integer matrix of the retained relation columns

Matrix multiplication is precisely their finite linear combination.
Its image is the kernel of the original presentation map. If the presented
group vanishes, this actual integer matrix is surjective.
-/

noncomputable section

open Set Function

namespace Wikipedia.SmoothSixDPoincare.IntegerPresentation

variable {B : Type*} [AddCommGroup B] [Module ℤ B] {r c : ℕ}
  (P : IntegerPresentation B r c)

def matrix : Matrix (Fin r) (Fin c) ℤ := fun i j => P.columns j i

theorem columns_sum_eq_mulVec (z : Fin c → ℤ) :
    (∑ j, z j • P.columns j) = P.matrix.mulVec z := by
  funext i
  simp [matrix, Matrix.mulVec, dotProduct, mul_comm]

theorem mem_range_matrix_iff (v : Fin r → ℤ) :
    v ∈ range P.matrix.mulVec ↔ v ∈ Submodule.span ℤ (range P.columns) := by
  rw [Submodule.mem_span_range_iff_exists_fun ℤ]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, (P.columns_sum_eq_mulVec z).trans hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, (P.columns_sum_eq_mulVec z).symm.trans hz⟩

theorem matrix_image_eq_kernel :
    range P.matrix.mulVec = (LinearMap.ker P.map : Set (Fin r → ℤ)) := by
  ext v
  rw [P.mem_range_matrix_iff, P.kernel_eq]
  rfl

theorem matrix_relation (z : Fin c → ℤ) : P.map (P.matrix.mulVec z) = 0 := by
  have h : P.matrix.mulVec z ∈ range P.matrix.mulVec := ⟨z, rfl⟩
  rw [P.matrix_image_eq_kernel] at h
  exact h

theorem columns_span_of_subsingleton [Subsingleton B] :
    Submodule.span ℤ (range P.columns) = ⊤ := by
  apply top_unique
  intro v _
  rw [← P.kernel_eq]
  exact Subsingleton.elim _ _

theorem matrix_surjective_of_subsingleton [Subsingleton B] : Surjective P.matrix.mulVec := by
  intro v
  apply (P.mem_range_matrix_iff v).mpr
  rw [P.columns_span_of_subsingleton]
  trivial

end Wikipedia.SmoothSixDPoincare.IntegerPresentation
