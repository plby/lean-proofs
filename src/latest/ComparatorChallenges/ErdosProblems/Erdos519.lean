/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos519

noncomputable def powerSum {n : ℕ} (z : Fin n → ℂ) (k : ℕ) : ℂ :=
  ∑ m : Fin n, z m ^ k

theorem erdos_519 {n : ℕ} (hn : 0 < n) (z : Fin n → ℂ)
    (hz1 : z ⟨0, hn⟩ = 1) :
    ∃ k : Fin n, 1 / 6 < ‖powerSum z (k.val + 1)‖ := by
  sorry

end Erdos519
