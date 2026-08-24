/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter
open scoped Topology

namespace Erdos1096

theorem erdos_1096 :
    ∃ ε > 0, ∀ q, 1 < q → q < 1 + ε →
    ∀ x : ℕ → ℝ, StrictMono x → Set.range x = { ∑ i ∈ S, q ^ i | S : Finset ℕ } →
    Tendsto (fun k => x (k + 1) - x k) atTop (𝓝 0) := by
  sorry

end Erdos1096
