import ErdosProblems.Erdos1148.CuspExcursionSeparation
import Mathlib.Topology.Connected.Basic

/-! # A connected cusp excursion has a common primitive short vector -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma continuous_modularVectorLengthSq_flow (g : SL(2, ℝ)) (u v : ℤ) :
    Continuous (fun t => modularVectorLengthSq (g * diagonalFlow t) u v) := by
  simp_rw [modularVectorLengthSq_flow]
  fun_prop

theorem primitive_short_vector_on_preconnected_cusp (g : SL(2, ℝ)) {H : ℝ} (hH : 1 ≤ H)
    {E : Set ℝ} (hE : IsPreconnected E) {a : ℝ} (ha : a ∈ E) {u v : ℤ}
    (huv : IsCoprime u v) (hshort : modularVectorLengthSq (g * diagonalFlow a) u v < (H ^ 2)⁻¹)
    (hcusp : ∀ t ∈ E, modularMk (g * diagonalFlow t) ∈ modularCusp H) :
    ∀ t ∈ E, modularVectorLengthSq (g * diagonalFlow t) u v < (H ^ 2)⁻¹ := by
  let U : Set ℝ := {t | modularVectorLengthSq (g * diagonalFlow t) u v < (H ^ 2)⁻¹}
  let V : Set ℝ := ⋃ (w : ℤ) (z : ℤ) (_ : u * z - v * w ≠ 0),
    {t | modularVectorLengthSq (g * diagonalFlow t) w z < (H ^ 2)⁻¹}
  have hU : IsOpen U := isOpen_lt (continuous_modularVectorLengthSq_flow g u v) continuous_const
  have hV : IsOpen V := isOpen_iUnion (fun w => isOpen_iUnion (fun z => isOpen_iUnion
    (fun _ => isOpen_lt (continuous_modularVectorLengthSq_flow g w z) continuous_const)))
  have hR : (H ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
  have hdisj : Disjoint U V := by
    apply Set.disjoint_left.mpr
    intro t htU htV
    obtain ⟨w, z, hdet, hwz⟩ := by
      simpa only [V, Set.mem_iUnion, Set.mem_setOf_eq] using htV
    have hprod : modularVectorLengthSq (g * diagonalFlow t) u v *
        modularVectorLengthSq (g * diagonalFlow t) w z < 1 := by
      calc
        _ ≤ modularVectorLengthSq (g * diagonalFlow t) u v * 1 :=
          mul_le_mul_of_nonneg_left (hwz.le.trans hR) (by dsimp [modularVectorLengthSq]; positivity)
        _ < 1 := by rw [mul_one]; exact htU.trans_le hR
    exact hdet (int_pair_determinant_eq_zero_of_short_product _ u v w z hprod)
  have hcover : E ⊆ U ∪ V := by
    intro t ht
    by_cases htu : t ∈ U
    · exact Or.inl htu
    · right
      obtain ⟨w, z, hwz, hshortw⟩ := (mem_modularCusp_iff_primitive _ H).mp (hcusp t ht)
      have hdet : u * z - v * w ≠ 0 := by
        intro hzero
        exact htu ((primitive_vector_lengthSq_le _ huv hwz.ne_zero_or_ne_zero hzero).trans_lt hshortw)
      exact Set.mem_iUnion.mpr ⟨w, Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hdet, hshortw⟩⟩⟩
  exact hE.subset_left_of_subset_union hU hV hdisj hcover ⟨a, ha, hshort⟩

theorem exists_common_primitive_cusp_vector (g : SL(2, ℝ)) {H a b : ℝ}
    (hH : 1 ≤ H) (hab : a ≤ b)
    (hcusp : ∀ t ∈ Set.Icc a b, modularMk (g * diagonalFlow t) ∈ modularCusp H) :
    ∃ u v : ℤ, IsCoprime u v ∧
      ∀ t ∈ Set.Icc a b, modularVectorLengthSq (g * diagonalFlow t) u v < (H ^ 2)⁻¹ := by
  obtain ⟨u, v, huv, hshort⟩ := (mem_modularCusp_iff_primitive _ H).mp (hcusp a ⟨le_rfl, hab⟩)
  exact ⟨u, v, huv, primitive_short_vector_on_preconnected_cusp g hH isPreconnected_Icc
    ⟨le_rfl, hab⟩ huv hshort hcusp⟩

end Erdos1148.DukeArithmetic
