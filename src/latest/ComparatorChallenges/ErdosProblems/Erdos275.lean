/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Set

namespace Erdos275

theorem erdos_275 (r : ℕ) (a : Fin r → ℤ) (n : Fin r → ℕ)
    (H : ∃ k : ℤ, ∀ x ∈ Ico k (k + 2 ^ r), ∃ i, x ≡ a i [ZMOD n i]) (x : ℤ) :
    ∃ i, x ≡ a i [ZMOD n i] := by
  sorry

end Erdos275
