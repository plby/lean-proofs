/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos920.Bridge
import ErdosProblems.Erdos920.Construction
import ErdosProblems.Erdos920.Inversion
import ErdosProblems.Erdos920.RamseyPackaging

/-!
# Erdős Problem 920

The graph-theoretic Ramsey bridge is in `Bridge`, the finite-geometric Ramsey
construction is packaged in `RamseyPackaging`, and the asymptotic inversion is
in `Inversion`.
-/

open Real Filter

syntax (name := answerSyntax920) "answer(" term ")" : term
macro_rules
  | `(answer($t)) => `($t)

/-- `g ≫ h` means that `h` is big-O of `g` at infinity. -/
notation:50 g " ≫ " h => Asymptotics.IsBigO Filter.atTop h g

namespace Erdos920

/--
The final implication, isolated from the construction of Bradač's Ramsey
lower bound.  This is the narrow assembly interface used by the main theorem.
-/

theorem erdos_920_of_dStarFamilies
    (families : ∀ u : ℕ, 1 ≤ u → RamseyPackaging.DStarFamily u) :
    answer(True) ↔ ∀ k : ℕ, k ≥ 4 → ∃ c > 0,
      (fun n : ℕ ↦ (f k n : ℝ)) ≫
        (fun n : ℕ ↦ (n : ℝ) ^ (1 - 1 / ((k : ℝ) - 1)) / (log n) ^ c) := by
  sorry

theorem erdos_920 :
    answer(True) ↔ ∀ k : ℕ, k ≥ 4 → ∃ c > 0,
      (fun n : ℕ ↦ (f k n : ℝ)) ≫
        (fun n : ℕ ↦ (n : ℝ) ^ (1 - 1 / ((k : ℝ) - 1)) / (log n) ^ c) := by
  sorry

