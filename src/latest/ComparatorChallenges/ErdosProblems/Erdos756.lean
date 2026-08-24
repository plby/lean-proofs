/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos756

noncomputable def distance_count (P : Finset ℂ) (d : ℝ) : ℕ :=
  (P.offDiag.filter (fun (x, y) => dist x y = d)).card / 2

theorem erdos_756 (n : ℕ) :
  ∃ P : Finset ℂ, P.card = n ∧
    ∃ S ⊆ (P.offDiag.image (fun (x, y) => dist x y)),
      S.card = n / 4 ∧ ∀ d ∈ S, distance_count P d ≥ n + 1 := by
  sorry

end Erdos756
