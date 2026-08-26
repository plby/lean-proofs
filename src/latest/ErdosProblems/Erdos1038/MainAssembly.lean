import ErdosProblems.Erdos1038.Statement
import ErdosProblems.Erdos1038.SoftEdgePackage
import ErdosProblems.Erdos1038.ExteriorPackage

/-!
# Exact assembly of the complete theorem

This module verifies the conjunction bookkeeping in `MainTheorem`.  The
soft-edge and exterior clauses are already unconditional.  The three
arguments below are precisely the remaining minimizer, lower-extremum, and
upper-extremum packages; no statement is weakened or reordered.
-/

open scoped ENNReal
open Polynomial

namespace Erdos1038

noncomputable section

theorem mainTheorem_of_exact_clauses
    (hLambda :
      (∃! q : ℝ, IsLambdaMinimizer q) ∧
      IsLambdaMinimizer qStar ∧
      (25715536866527 / 10 ^ 15 : ℝ) < qStar ∧
      qStar < (25715536866528 / 10 ^ 15 : ℝ) ∧
      (1834430475762661 / 10 ^ 15 : ℝ) < L ∧
      L < (1834430475762662 / 10 ^ 15 : ℝ))
    (hLower :
      infimumLength = ENNReal.ofReal L ∧
      ∀ f : Polynomial ℝ, IsAdmissible f →
        ENNReal.ofReal L < sublevelVolume f)
    (hUpper :
      supremumLength = ENNReal.ofReal (2 * Real.sqrt 2) ∧
      (∀ m : ℕ, 0 < m →
        IsAdmissible ((Polynomial.X ^ 2 - 1 : Polynomial ℝ) ^ m) ∧
        sublevelVolume ((Polynomial.X ^ 2 - 1 : Polynomial ℝ) ^ m) =
          ENNReal.ofReal (2 * Real.sqrt 2)) ∧
      (∀ f : Polynomial ℝ, IsAdmissible f →
        (sublevelVolume f = ENNReal.ofReal (2 * Real.sqrt 2) ↔
          ∃ m : ℕ, 0 < m ∧ f = (Polynomial.X ^ 2 - 1) ^ m))) :
    MainTheorem := by
  rcases mainTheorem_softEdge_clause with
    ⟨hSoftUnique, hSoft, hSoftLower, hSoftUpper⟩
  rcases hLambda with
    ⟨hLambdaUnique, hLambdaMin, hQStarLower, hQStarUpper,
      hLLower, hLUpper⟩
  rcases hLower with ⟨hInfimum, hStrictLower⟩
  rcases hUpper with ⟨hSupremum, hExamples, hUpperEquality⟩
  exact ⟨hSoftUnique, hSoft, hSoftLower, hSoftUpper,
    mainTheorem_exterior_clause, hLambdaUnique, hLambdaMin,
    hQStarLower, hQStarUpper, hLLower, hLUpper,
    hInfimum, hSupremum, hStrictLower, hExamples, hUpperEquality⟩

end

end Erdos1038
