import ErdosProblems.Erdos1148.PrimitiveLatticeVectors

/-! # One bounded primitive vector controls the cusp height of the whole lattice -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem not_mem_cusp_of_primitive_lengthSq_bounds (g : SL(2, ℝ)) {u v : ℤ}
    (huv : IsCoprime u v) {R H : ℝ} (hlower : R ≤ modularVectorLengthSq g u v)
    (hupper : modularVectorLengthSq g u v ≤ 1) (hscale : (H ^ 2)⁻¹ ≤ R) :
    modularMk g ∉ modularCusp H := by
  intro hcusp
  obtain ⟨w, z, hwz, hshort⟩ := (mem_modularCusp_iff_representative g H).mp hcusp
  have hwshort : modularVectorLengthSq g w z < R := hshort.trans_le hscale
  have hprod : modularVectorLengthSq g u v * modularVectorLengthSq g w z < 1 := by
    calc
      _ ≤ 1 * modularVectorLengthSq g w z :=
        mul_le_mul_of_nonneg_right hupper (by dsimp [modularVectorLengthSq]; positivity)
      _ < 1 := by rw [one_mul]; exact hwshort.trans_le (hlower.trans hupper)
  have hdet := int_pair_determinant_eq_zero_of_short_product g u v w z hprod
  have hle := primitive_vector_lengthSq_le g huv hwz hdet
  exact (not_lt_of_ge (hlower.trans hle)) hwshort

end Erdos1148.DukeArithmetic
