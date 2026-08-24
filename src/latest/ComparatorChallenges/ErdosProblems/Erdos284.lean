/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

/-!
# Erdős Problem 284

For a positive number `k` of terms, let `f(k)` be the greatest possible
first denominator in a strictly increasing `k`-term representation of one
as a sum of unit fractions.  This file states that definition literally and
proves

`f(k) / k → 1 / (exp 1 - 1)`.
-/

namespace Erdos284

/-- The representation appearing verbatim in the problem, with exactly `k`
terms. -/
def OriginalRepresentation (k : ℕ) (n : Fin k → ℕ) : Prop :=
  StrictMono n ∧ 0 ∉ Set.range n ∧ 1 = ∑ i, (1 : ℝ) / n i

/-- The possible values of the first denominator in a `k`-term
representation.  For `k = 0` this set is empty. -/
def OriginalFirstDenominators (k : ℕ) : Set ℕ :=
  {m | ∃ (hk : 0 < k) (n : Fin k → ℕ),
    OriginalRepresentation k n ∧ n ⟨0, hk⟩ = m}

/-- The extremal function `f(k)` in the statement of Erdős Problem 284. -/
noncomputable def originalErdosF (k : ℕ) : ℕ :=
  sSup (OriginalFirstDenominators k)

theorem erdos_284 :
    Tendsto (fun k : ℕ ↦ (originalErdosF k : ℝ) / (k : ℝ))
      atTop (nhds (1 / (Real.exp 1 - 1))) := by
  sorry

end Erdos284
