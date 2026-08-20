/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos909.ClosedSum

/-!
# Closed-sum theorem in every finite dimension

This file closes the induction established in `ClosedSum`: the checked
rank-one base and successor step imply the countable closed-sum theorem at
every positive strict dimension bound.
-/

namespace Erdos909.ClosedSum

universe u

/-- The countable closed-sum theorem at every positive strict dimension
bound. -/
theorem countableClosedSumAt_of_pos (r : ℕ) (hr : 0 < r) :
    CountableClosedSumAt.{u} r := by
  cases r with
  | zero => omega
  | succ r =>
      induction r with
      | zero =>
          simpa using (countableClosedSumAt_one : CountableClosedSumAt.{u} 1)
      | succ r ih =>
          simpa [Nat.add_assoc] using
            (countableClosedSumAt_succ (ih (Nat.succ_pos r)))

end Erdos909.ClosedSum
