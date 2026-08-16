import Mathlib

/-!
# Erdős Problem 987

*References:*
- [erdosproblems.com/987](https://www.erdosproblems.com/987)
- [APSSV26b] B. Alexeev, M. Putterman, M. Sawhney, M. Sellke, and G. Valiant,
  [Short proofs in combinatorics, probability, and number theory II](https://arxiv.org/abs/2604.06609).
  arXiv:2604.06609 (2026).
- [Cl67] Clunie, J., On a problem of Erdős. J. London Math. Soc. (1967), 133--136.
- [Er64b] Erdős, P., Problems and results on diophantine approximations. Compositio Math. (1964),
  52-65.
- [Er65b] Erdős, P., Some remarks on number theory. Israel J. Math. (the actual reference
  cited by Clunie 1967 as [2]; the erdosproblems.com bibliography points to a different
  Erdős 1965 paper, "Some recent advances and current problems in number theory" (Lectures
  on Modern Mathematics III, 1965, 196-244), which does not appear to contain the
  exponential-sum log-bound proof).
- [Ha74] Hayman, W. K., Research problems in function theory: new problems. (1974), 155--180.
- [Li69] Lindström, B., An inequality for $B_2$-sequences. J. Combinatorial Theory (1969), 211-212.
-/

open Filter Finset Asymptotics

/- The upstream `answer(True)` wrapper is documentary; completed Erdős
problem files in this repository represent it by the wrapped proposition. -/
syntax (name := answerSyntax987) "answer(" term ")" : term
macro_rules
  | `(answer($t)) => `($t)

namespace Erdos987

/-! Indices are zero-based, so `range n` represents `j < n`. -/

/- ## API for the additive character `e(x) = e^{2πi x}` -/

/-- Shorthand for the additive character $e(x) = e^{2 \pi i x}$.
(Matches `Real.fourierChar` / `𝐞` from `Mathlib/Analysis/Complex/Circle.lean`, but
kept as a local definition for readability across the many sites that use it.) -/
noncomputable def e (x : ℝ) : ℂ := Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)

noncomputable def A (x : ℕ → ℝ) (k : ℕ) : EReal :=
  atTop.limsup fun n : ℕ => (‖∑ j ∈ range n, e (k * x j)‖ : EReal)

theorem erdos_987.parts.i :
    answer(True) ↔ ∀ (x : ℕ → ℝ) (_ : ∀ j : ℕ, x j ∈ Set.Ioo (0 : ℝ) 1),
      atTop.limsup (fun k : ℕ => A x k) = ⊤ := by
  sorry

theorem erdos_987.variants.sqrt_log_upper_bound :
    ∃ (x : ℕ → ℝ) (_ : ∀ j : ℕ, x j ∈ Set.Ioo (0 : ℝ) 1) (C : ℝ) (_ : 0 < C),
      ∀ k n : ℕ, 2 ≤ k → ‖∑ j ∈ range n, e (k * x j)‖ ≤ C * Real.sqrt (k * Real.log k) := by
  sorry

theorem erdos_987.parts.ii :
    answer(True) ↔ ∃ (x : ℕ → ℝ) (_ : ∀ j : ℕ, x j ∈ Set.Ioo (0 : ℝ) 1) (b : ℕ → ℝ),
      b =o[atTop] (fun k : ℕ => (k : ℝ)) ∧ ∀ᶠ k : ℕ in atTop, A x k ≤ ((b k : ℝ) : EReal) := by
  sorry
