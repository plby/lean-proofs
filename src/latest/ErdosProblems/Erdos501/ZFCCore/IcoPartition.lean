/-
  The half-open unit intervals `Ico m (m+1)`, `m : ℤ`, partition `ℝ`.
  Used to turn the per-block distribution hypothesis (P2) into
  `∑' m, volume (W ∩ Ico m (m+1)) = volume W`.
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Set

namespace Erdos501

/-- The integer unit intervals cover `ℝ`. -/
theorem iUnion_Ico_int : ⋃ m : ℤ, Set.Ico (m : ℝ) ((m : ℝ) + 1) = univ := by
  apply eq_univ_of_forall
  intro r
  rw [mem_iUnion]
  refine ⟨⌊r⌋, ?_, ?_⟩
  · exact Int.floor_le r
  · have := Int.lt_floor_add_one r
    linarith

/-- The integer unit intervals are pairwise disjoint. -/
theorem pairwise_disjoint_Ico_int :
    Pairwise (Function.onFun Disjoint fun m : ℤ => Set.Ico (m : ℝ) ((m : ℝ) + 1)) := by
  intro m n hmn
  rw [Function.onFun, Set.disjoint_left]
  intro r hrm hrn
  rw [mem_Ico] at hrm hrn
  -- m ≤ r < m+1 and n ≤ r < n+1 force m = n
  have h1 : (m : ℝ) < (n : ℝ) + 1 := lt_of_le_of_lt hrm.1 hrn.2
  have h2 : (n : ℝ) < (m : ℝ) + 1 := lt_of_le_of_lt hrn.1 hrm.2
  have h1' : m < n + 1 := by exact_mod_cast h1
  have h2' : n < m + 1 := by exact_mod_cast h2
  omega

end Erdos501
