/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1081

noncomputable section

open Filter Finset Set
open scoped nonZeroDivisors

def IsSquarefull (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

def IsSumOfTwoSquarefull (n : ℕ) : Prop :=
  ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ IsSquarefull a ∧ IsSquarefull b ∧ n = a + b

noncomputable def A (N : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 N).filter IsSumOfTwoSquarefull).card

local instance isSumOfTwoSquarefullDecidable :
    DecidablePred IsSumOfTwoSquarefull := Classical.decPred _

noncomputable def landauScale (N : ℕ) : ℝ :=
  (N : ℝ) / Real.sqrt (Real.log (N : ℝ))

noncomputable def normalizedCount (N : ℕ) : ℝ :=
  (A N : ℝ) / landauScale N

def ErdosConjecture : Prop :=
  ∃ c : ℝ, 0 < c ∧ Tendsto normalizedCount atTop (nhds c)

theorem not_erdosConjecture : ¬ ErdosConjecture := by
  sorry

end

end Erdos1081
