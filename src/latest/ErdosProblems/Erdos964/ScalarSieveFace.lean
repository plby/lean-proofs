import ErdosProblems.Erdos964.ScalarKernelFacePrimitive

/-!
# The scalar face extended to the large-prime range
-/

namespace Erdos964

noncomputable def scalarSieveFace (z : ℝ) : ℝ :=
  if z ≤ 1 then truncatedSieveFace z else truncatedSieveFace 1

theorem scalarSieveFace_eq_small (z : ℝ) (hz : z ≤ 1) :
    scalarSieveFace z = truncatedSieveFace z := if_pos hz

theorem scalarSieveFace_eq_large (z : ℝ) (hz : 1 ≤ z) :
    scalarSieveFace z = truncatedSieveFace 1 := by
  by_cases h : z ≤ 1
  · have heq : z = 1 := le_antisymm h hz
    simp only [scalarSieveFace, heq, le_refl, ite_true]
  · exact if_neg h

theorem scalarSieveFace_nonneg (z : ℝ) (hz : 0 ≤ z) : 0 ≤ scalarSieveFace z := by
  rw [scalarSieveFace]
  split_ifs with hz1
  · rw [truncatedSieveFace_eq]
    exact mul_nonneg hz (sieveFaceKernel_nonneg ⟨hz, hz1⟩)
  · rw [truncatedSieveFace_eq]
    norm_num [sieveFaceKernel]

theorem scalarSieveFace_one : scalarSieveFace 1 = 41 / 60 := by
  rw [scalarSieveFace_eq_small 1 le_rfl, truncatedSieveFace_eq]
  norm_num [sieveFaceKernel]

end Erdos964
