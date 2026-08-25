import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-! Elementary coordinate bounds for the diameter of the unit square. -/

namespace Puzzling139335

theorem sub_sq_le_one_of_mem_Icc {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    (x - y) ^ 2 ≤ 1 := by
  have h₁ : 0 ≤ 1 - (x - y) := by linarith [hx.2, hy.1]
  have h₂ : 0 ≤ 1 + (x - y) := by linarith [hx.1, hy.2]
  nlinarith [mul_nonneg h₁ h₂]

theorem add_eq_one_of_mem_Icc_of_sub_sq_eq_one {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (h : (x - y) ^ 2 = 1) : x + y = 1 := by
  rcases sq_eq_one_iff.mp h with h | h
  · linarith [hx.2, hy.1]
  · linarith [hx.1, hy.2]

theorem endpoints_of_mem_Icc_of_sub_sq_eq_one {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (h : (x - y) ^ 2 = 1) :
    (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) := by
  rcases sq_eq_one_iff.mp h with h | h
  · right
    constructor <;> linarith [hx.2, hy.1]
  · left
    constructor <;> linarith [hx.1, hy.2]

end Puzzling139335
