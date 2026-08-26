import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-! Positive distinct integer coefficients at three scalene outer angles. -/

namespace Erdos633b

theorem three_distinct_positive_sum_ge_six (c : Fin 3 → ℕ)
    (hp : ∀ i, 0 < c i) (hinj : Function.Injective c) : 6 ≤ ∑ i, c i := by
  have hp0 := hp 0
  have hp1 := hp 1
  have hp2 := hp 2
  have h01 := hinj.ne (by decide : (0 : Fin 3) ≠ 1)
  have h02 := hinj.ne (by decide : (0 : Fin 3) ≠ 2)
  have h12 := hinj.ne (by decide : (1 : Fin 3) ≠ 2)
  rw [Fin.sum_univ_three]
  omega

theorem unit_double_of_three_distinct_sum_six (c : Fin 3 → ℕ)
    (hp : ∀ i, 0 < c i) (hinj : Function.Injective c) (hs : ∑ i, c i = 6) :
    ∃ i j : Fin 3, i ≠ j ∧ c i = 1 ∧ c j = 2 := by
  have hp0 := hp 0
  have hp1 := hp 1
  have hp2 := hp 2
  have h01 := hinj.ne (by decide : (0 : Fin 3) ≠ 1)
  have h02 := hinj.ne (by decide : (0 : Fin 3) ≠ 2)
  have h12 := hinj.ne (by decide : (1 : Fin 3) ≠ 2)
  rw [Fin.sum_univ_three] at hs
  have hc : (c 0 = 1 ∧ c 1 = 2) ∨ (c 0 = 1 ∧ c 2 = 2) ∨
      (c 1 = 1 ∧ c 0 = 2) ∨ (c 1 = 1 ∧ c 2 = 2) ∨
      (c 2 = 1 ∧ c 0 = 2) ∨ (c 2 = 1 ∧ c 1 = 2) := by omega
  rcases hc with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact ⟨0, 1, by decide, ha, hb⟩
  · exact ⟨0, 2, by decide, ha, hb⟩
  · exact ⟨1, 0, by decide, ha, hb⟩
  · exact ⟨1, 2, by decide, ha, hb⟩
  · exact ⟨2, 0, by decide, ha, hb⟩
  · exact ⟨2, 1, by decide, ha, hb⟩

end Erdos633b
