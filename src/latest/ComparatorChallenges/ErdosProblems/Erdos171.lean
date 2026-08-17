import Mathlib

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace Erdos171

abbrev Word (t n : ℕ) := Fin n → Fin t

end Erdos171

namespace Erdos171

def ContainsLine {t n : ℕ} (A : Set (Word t n)) : Prop :=
  ∃ l : Combinatorics.Line (Fin t) (Fin n), Set.range l ⊆ A

end Erdos171

namespace Erdos171

def Erdos171Statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ t : ℕ, 1 ≤ t →
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A : Finset (Word t N),
      ε * (t : ℝ) ^ N ≤ (A.card : ℝ) →
        ContainsLine (A : Set (Word t N))

end Erdos171

namespace Erdos171

theorem erdos_171 : Erdos171Statement := by
  sorry

end Erdos171

end
