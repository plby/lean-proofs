import Mathlib

open Filter
open scoped BigOperators Topology

namespace Erdos239

syntax (name := answerSyntax239Challenge) "answer(" term ")" : term
macro_rules
  | `(answer($t)) => `($t)

theorem erdos_239 :
    answer(True) ↔ ∀ f : ℕ → ℝ,
    (∀ n ≥ 1, f n = 1 ∨ f n = -1) ∧
    (∀ m n, m.Coprime n → f (m * n) = f m * f n) ∧
    f 1 = 1 →
    ∃ L, Tendsto (fun N ↦ (∑ n ∈ Finset.Icc 1 N, f n) / N)
      atTop (𝓝 L) := by
  sorry

end Erdos239
