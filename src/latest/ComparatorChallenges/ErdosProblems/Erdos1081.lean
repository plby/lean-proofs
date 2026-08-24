/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1081

def IsSquarefull (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

def IsSumOfTwoSquarefull (n : ℕ) : Prop :=
  ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ IsSquarefull a ∧ IsSquarefull b ∧ n = a + b

noncomputable def A (N : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 N).filter IsSumOfTwoSquarefull).card

noncomputable def landauScale (N : ℕ) : ℝ :=
  (N : ℝ) / Real.sqrt (Real.log (N : ℝ))

noncomputable def normalizedCount (N : ℕ) : ℝ :=
  (A N : ℝ) / landauScale N

theorem not_erdos_1081 :
    ¬ (∃ c : ℝ, 0 < c ∧ Filter.Tendsto Erdos1081.normalizedCount Filter.atTop (nhds c)) := by
  sorry

end Erdos1081
