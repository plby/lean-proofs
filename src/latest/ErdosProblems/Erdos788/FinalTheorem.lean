import ErdosProblems.Erdos788.LowerFinal
import ErdosProblems.Erdos788.UpperFinal
import ErdosProblems.Erdos788.ExponentConsequences

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Final theorem for Erdős Problem 788

This module combines the explicit lower and upper estimates and then invokes
the already proved exponent-consequence theorem.
-/

namespace Erdos788

theorem finalLowerBoundConstant_pos : 0 < finalLowerBoundConstant := by
  norm_num [finalLowerBoundConstant]

/-- The complete quantitative two-sided estimate. -/
theorem quantitativeMainTheorem : QuantitativeMainTheorem := by
  obtain ⟨nLower, hnLower, hLower⟩ := exists_lowerBound_threshold
  obtain ⟨nUpper, hnUpper, hUpper⟩ := exists_upperBound_threshold
  refine ⟨finalLowerBoundConstant, upperExponentConstant,
    finalLowerBoundConstant_pos, upperExponentConstant_pos,
    max nLower nUpper, ?_, ?_⟩
  · exact hnLower.trans (le_max_left _ _)
  · intro n hn
    constructor
    · simpa only [finalLowerBoundConstant] using!
        hLower n ((le_max_left nLower nUpper).trans hn)
    · exact hUpper n ((le_max_right nLower nUpper).trans hn)

/-- The explicit epsilon formulation of the exponent-one-half conclusion. -/
theorem hasExponentOneHalf : HasExponentOneHalf :=
  quantitativeMainTheorem_implies_hasExponentOneHalf quantitativeMainTheorem

/-- The strong paper's statement, including its fixed lower constant and the
fact that the lower estimate holds for every `n ≥ 3`. -/
theorem paperMainTheorem : PaperMainTheorem := by
  refine ⟨?_, ?_, hasExponentOneHalf⟩
  · intro n hn
    simpa only [finalLowerBoundConstant] using! cast_f_lower hn
  · obtain ⟨nUpper, hnUpper, hUpper⟩ := exists_upperBound_threshold
    refine ⟨upperExponentConstant, upperExponentConstant_pos,
      max 3 nUpper, by omega, ?_⟩
    intro n hn
    constructor
    · simpa only [finalLowerBoundConstant] using!
        cast_f_lower ((le_max_left 3 nUpper).trans hn)
    · exact hUpper n ((le_max_right 3 nUpper).trans hn)

/-- The original website's question `f(n) ≤ n^(1/2+o(1))`, with all
epsilon and eventual quantifiers made explicit. -/
theorem answersOriginalUpperQuestion : AnswersOriginalUpperQuestion := by
  intro ε hε
  obtain ⟨n₀, hn₀, hbound⟩ := hasExponentOneHalf ε hε
  exact ⟨n₀, hn₀, fun n hn ↦ (hbound n hn).2⟩

/-- Erdős Problem 788, preserving both the strong paper statement and the
exact quantifier form of the original upper-bound question. -/
theorem erdos788 : MainTheorem :=
  ⟨paperMainTheorem, answersOriginalUpperQuestion⟩

end Erdos788
