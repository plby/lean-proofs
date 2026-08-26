import ErdosProblems.Erdos788.Definitions

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact quantified theorem statements

The displayed quantitative theorem uses explicit constants and an explicit
eventual threshold.  `HasExponentOneHalf` records the paper's stated
`n^(1/2+o(1))` consequence with its full epsilon quantifiers.
-/

namespace Erdos788

/-- The exponent correction in the quantitatively strong paper. -/
noncomputable def exponentCorrection (n : ℕ) : ℝ :=
  (Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) ^ (1 / 3 : ℝ)

/-- The explicit lower-bound constant stated in the strong paper. -/
noncomputable def finalLowerBoundConstant : ℝ :=
  1 / 2000

/-- The fully quantified two-sided conclusion of the main theorem. -/
def QuantitativeMainTheorem : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      c * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤ (f n : ℝ) ∧
        (f n : ℝ) ≤
          (n : ℝ) ^ ((1 / 2 : ℝ) + C * exponentCorrection n)

/-- Explicit epsilon quantifiers for `f(n) = n^(1/2+o(1))`. -/
def HasExponentOneHalf : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
    (n : ℝ) ^ ((1 / 2 : ℝ) - ε) ≤ (f n : ℝ) ∧
      (f n : ℝ) ≤ (n : ℝ) ^ ((1 / 2 : ℝ) + ε)

/-- The precise epsilon-quantified upper-bound question on the original
Erdős Problems page. -/
def AnswersOriginalUpperQuestion : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
    (f n : ℝ) ≤ (n : ℝ) ^ ((1 / 2 : ℝ) + ε)

/-- The theorem stated in the strong paper: the explicit lower bound holds
for every `n ≥ 3`, the quantitative upper bound holds for all sufficiently
large positive integers, and the resulting exponent is one half. -/
def PaperMainTheorem : Prop :=
  (∀ n : ℕ, 3 ≤ n →
    finalLowerBoundConstant * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
      (f n : ℝ)) ∧
  (∃ C : ℝ, 0 < C ∧
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      finalLowerBoundConstant *
          Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤ (f n : ℝ) ∧
        (f n : ℝ) ≤
          (n : ℝ) ^ ((1 / 2 : ℝ) + C * exponentCorrection n)) ∧
  HasExponentOneHalf

/-- The complete final statement: the strong paper theorem together with the
original upper-bound question in its exact epsilon-quantified form. -/
def MainTheorem : Prop :=
  PaperMainTheorem ∧ AnswersOriginalUpperQuestion

end Erdos788
