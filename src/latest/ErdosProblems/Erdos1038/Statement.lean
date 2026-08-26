import ErdosProblems.Erdos1038.Definitions

/-!
# Exact formal target for Erdős problem 1038

`MainTheorem` is a proposition rather than an assumed theorem.  Its fields
record all assertions of the manuscript's main theorem and its equality
characterizations.  The final module will prove this proposition without
additional hypotheses.
-/

open scoped ENNReal Real
open MeasureTheory Set Polynomial

namespace Erdos1038

noncomputable section

/-- The complete statement to be proved. -/
def MainTheorem : Prop :=
  (∃! q : ℝ, IsSoftRoot q) ∧
  IsSoftRoot qSoft ∧
  (123630684649383 / 10 ^ 15 : ℝ) < qSoft ∧
  qSoft < (123630684649384 / 10 ^ 15 : ℝ) ∧
  (∀ q ∈ Set.Ioc 0 qSoft,
      (∃! u : ℝ, q⁻¹ < u ∧ exteriorEquation q u) ∧
      (q = qSoft → uPlus q = 1) ∧
      (q < qSoft →
        ∃! u : ℝ, 1 < u ∧ u < q⁻¹ ∧ exteriorEquation q u)) ∧
  (∃! q : ℝ, IsLambdaMinimizer q) ∧
  IsLambdaMinimizer qStar ∧
  (25715536866527 / 10 ^ 15 : ℝ) < qStar ∧
  qStar < (25715536866528 / 10 ^ 15 : ℝ) ∧
  (1834430475762661 / 10 ^ 15 : ℝ) < L ∧
  L < (1834430475762662 / 10 ^ 15 : ℝ) ∧
  infimumLength = ENNReal.ofReal L ∧
  supremumLength = ENNReal.ofReal (2 * Real.sqrt 2) ∧
  (∀ f : Polynomial ℝ, IsAdmissible f →
      ENNReal.ofReal L < sublevelVolume f) ∧
  (∀ m : ℕ, 0 < m →
      IsAdmissible ((Polynomial.X ^ 2 - 1 : Polynomial ℝ) ^ m) ∧
      sublevelVolume ((Polynomial.X ^ 2 - 1 : Polynomial ℝ) ^ m) =
        ENNReal.ofReal (2 * Real.sqrt 2)) ∧
  (∀ f : Polynomial ℝ, IsAdmissible f →
      (sublevelVolume f = ENNReal.ofReal (2 * Real.sqrt 2) ↔
        ∃ m : ℕ, 0 < m ∧ f = (Polynomial.X ^ 2 - 1) ^ m))

end

end Erdos1038
