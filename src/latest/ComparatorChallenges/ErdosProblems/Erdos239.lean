import Mathlib

open Filter
open scoped BigOperators Topology

namespace Erdos239

theorem erdos_239 :
    ∀ f : ℕ → ℝ,
    (∀ n ≥ 1, f n = 1 ∨ f n = -1) ∧
    (∀ m n, m.Coprime n → f (m * n) = f m * f n) ∧
    f 1 = 1 →
    ∃ L, Tendsto (fun N ↦ (∑ n ∈ Finset.Icc 1 N, f n) / N)
      atTop (𝓝 L) := by
  sorry

end Erdos239
