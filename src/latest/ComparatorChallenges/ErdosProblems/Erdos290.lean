import Mathlib

namespace Erdos290

def harmonicSum (a b : ℕ) : ℚ := ∑ i ∈ Finset.Icc a b, (1 : ℚ) / i
def v (a b : ℕ) : ℕ := (harmonicSum a b).den
end Erdos290

attribute [local instance] Classical.propDecidable

namespace Erdos290

theorem main (a : ℕ) (ha : a > 0) : ∃ b, a < b ∧ b ≤ 6 * a ∧ v a b < v a (b - 1) := by
  sorry

end Erdos290
