import Mathlib


open Set

namespace Erdos275

open scoped Classical in
theorem erdos_275 (r : ℕ) (a : Fin r → ℤ) (n : Fin r → ℕ)
    (H : ∃ k : ℤ, ∀ x ∈ Ico k (k + 2 ^ r), ∃ i, x ≡ a i [ZMOD n i]) (x : ℤ) :
    ∃ i, x ≡ a i [ZMOD n i] := by
  sorry

end Erdos275
