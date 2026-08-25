import ErdosProblems.Erdos964.ScalarPrimeIntegrand
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# A global bound for the nonnegative scalar face
-/

namespace Erdos964

theorem exists_scalarSieveFace_bound :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ z : ℝ, 0 ≤ z → |scalarSieveFace z| ≤ G := by
  obtain ⟨G, hG⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    continuous_scalarSieveFace.continuousOn
  refine ⟨|G|, abs_nonneg _, ?_⟩
  intro z hz
  by_cases hz1 : z ≤ 1
  · exact (show |scalarSieveFace z| ≤ G by
      simpa only [Real.norm_eq_abs] using hG z ⟨hz, hz1⟩).trans (le_abs_self G)
  · have heq : scalarSieveFace z = scalarSieveFace 1 := by
      rw [scalarSieveFace_eq_large z (by linarith), scalarSieveFace_eq_small 1 le_rfl]
    rw [heq]
    exact (show |scalarSieveFace 1| ≤ G by
      simpa only [Real.norm_eq_abs] using hG 1 (by norm_num)).trans (le_abs_self G)

end Erdos964
