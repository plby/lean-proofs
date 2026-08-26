import ErdosProblems.Erdos118.Ordinal
import ErdosProblems.Erdos118.Reused591.PositiveEndpoint

/-! The exact positive hypothesis, from the isolated and rebuilt complete
successor-index game proof. Both partition definitions use red order type. -/

namespace Erdos118

/-- The concrete ordinal satisfies the red-copy/blue-triangle relation. -/
theorem positive_three : Partition lambda lambda 3 := by
  rw [lambda_eq_natural_inner_power]
  exact Reused591.Erdos591.schipperus_two

end Erdos118
