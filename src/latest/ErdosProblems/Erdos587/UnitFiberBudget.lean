import ErdosProblems.Erdos587.LocatorBudget

/-! Clearing the square-root locator budget on a middle quarter of a fiber. -/

namespace Erdos587

theorem unit_fiber_locator_budget {K u H M n T : ℝ}
    (hu : 0 < u) (hH : 0 < H) (hM : 0 ≤ M) (hT : 0 < T) (hn : M / 8 ≤ n)
    (hbudget : K * 8 ^ 10 * T ^ 4 < u * H ^ 7 * M ^ 3) :
    K * (Real.sqrt T / u) < n ^ 3 * (H / (8 * Real.sqrt T)) ^ 7 := by
  have hroot : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hroot8 : (Real.sqrt T) ^ 8 = T ^ 4 := by
    calc
      _ = ((Real.sqrt T) ^ 2) ^ 4 := by ring
      _ = _ := by rw [Real.sq_sqrt hT.le]
  have hbudget' : K * 8 ^ 10 * (Real.sqrt T) ^ 8 < u * H ^ 7 * M ^ 3 := by rwa [hroot8]
  have hden : 0 < u * 8 ^ 10 * (Real.sqrt T) ^ 7 := by positivity
  have hsmall : K * (Real.sqrt T / u) < (M / 8) ^ 3 * (H / (8 * Real.sqrt T)) ^ 7 := by
    apply (mul_lt_mul_iff_left₀ hden).mp
    have hleft : K * (Real.sqrt T / u) * (u * 8 ^ 10 * (Real.sqrt T) ^ 7) =
        K * 8 ^ 10 * (Real.sqrt T) ^ 8 := by field_simp
    have hright : ((M / 8) ^ 3 * (H / (8 * Real.sqrt T)) ^ 7) *
        (u * 8 ^ 10 * (Real.sqrt T) ^ 7) = u * H ^ 7 * M ^ 3 := by field_simp
    rwa [hleft, hright]
  apply hsmall.trans_le
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hn 3) (by positivity)

end Erdos587
