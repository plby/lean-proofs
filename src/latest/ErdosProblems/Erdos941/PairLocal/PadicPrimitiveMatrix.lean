/- Adapted from the checked repository proof in Erdos1148/PadicPrimitiveMatrix.lean. -/
import ErdosProblems.Erdos941.PairLocal.BaseChange

/-!
# Primitive representatives of p-adic projective matrices

Divide a matrix by an entry of largest norm. All entries become integral,
and the selected entry becomes one. No denominator or gcd estimate is needed.
-/

namespace Erdos941.PairLocal

lemma exists_padic_primitive_matrix (p : ℕ) [Fact p.Prime]
    (M : Matrix (Fin 2) (Fin 2) (Padic p)) (hM : M.det ≠ 0) :
    ∃ (c : Padic p) (A : Matrix (Fin 2) (Fin 2) (PadicInt p)), c ≠ 0 ∧
      A.map (algebraMap (PadicInt p) (Padic p)) = c • M ∧
      ∃ i j, A i j = 1 := by
  classical
  obtain ⟨ij, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 2 × Fin 2))
    (fun ij => ‖M ij.1 ij.2‖) Finset.univ_nonempty
  have hpivot : M ij.1 ij.2 ≠ 0 := by
    intro hpivot
    have hzero : M = 0 := by
      ext i j
      have hle := hmax (i, j) (Finset.mem_univ _)
      rw [hpivot, norm_zero] at hle
      exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
    exact hM (by simp [hzero])
  have hnorm (i j : Fin 2) : ‖M i j / M ij.1 ij.2‖ ≤ 1 := by
    rw [norm_div, div_le_one (norm_pos_iff.mpr hpivot)]
    exact hmax (i, j) (Finset.mem_univ _)
  let A : Matrix (Fin 2) (Fin 2) (PadicInt p) := fun i j => ⟨M i j / M ij.1 ij.2, hnorm i j⟩
  refine ⟨(M ij.1 ij.2)⁻¹, A, inv_ne_zero hpivot, ?_, ij.1, ij.2, ?_⟩
  · ext i j
    change M i j / M ij.1 ij.2 = (M ij.1 ij.2)⁻¹ * M i j
    rw [div_eq_mul_inv, mul_comm]
  · apply PadicInt.ext
    change M ij.1 ij.2 / M ij.1 ij.2 = 1
    exact div_self hpivot

end Erdos941.PairLocal
