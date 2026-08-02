import Util.ListSorted

namespace MO420333

structure Strategy where
  x : ℕ → ℝ
  nonneg : ∀ n, 0 ≤ x n
  one_le : 1 ≤ x 0
  mono : Monotone x
  hits : ∀ {y : ℝ}, 1 ≤ y → ∃ n, y ≤ x n

noncomputable def hitIndex (s : Strategy) (y : {y : ℝ // 1 ≤ y}) : ℕ :=
  Nat.find (s.hits y.property)

noncomputable def partialSum (s : Strategy) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), s.x i

noncomputable def score (s : Strategy) (y : {y : ℝ // 1 ≤ y}) : ENNReal :=
  ENNReal.ofReal ((partialSum s (hitIndex s y)) / y.1)

noncomputable def worstCaseScore (s : Strategy) : ENNReal :=
  ⨆ y : {y : ℝ // 1 ≤ y}, score s y

noncomputable def gameValue : ENNReal :=
  ⨅ s : Strategy, worstCaseScore s

theorem unbounded_value_eq_four : gameValue = 4 := by
  sorry

end MO420333
