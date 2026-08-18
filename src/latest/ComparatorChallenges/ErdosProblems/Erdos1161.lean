import Mathlib

open Filter Asymptotics

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos1161

noncomputable def possibleOrders (n : ℕ) : Finset ℕ :=
  Finset.univ.image (fun σ : Equiv.Perm (Fin n) ↦ orderOf σ)

end Erdos1161

namespace Erdos1161

noncomputable def orderCount (n m : ℕ) : ℕ :=
  Fintype.card {σ : Equiv.Perm (Fin n) // orderOf σ = m}

end Erdos1161

namespace Erdos1161

noncomputable def maxOrderCount (n : ℕ) : ℕ :=
  (possibleOrders n).sup (orderCount n)

end Erdos1161

namespace Erdos1161

def BekerCandidate (n m : ℕ) : Prop :=
  0 < m ∧ Nat.lcmUpto (n - m) ∣ m

end Erdos1161

namespace Erdos1161

def IsMode (n m : ℕ) : Prop :=
  ∀ j : ℕ, orderCount n j ≤ orderCount n m

end Erdos1161

namespace Erdos1161

theorem erdos_1161 :
    ((fun n : ℕ ↦ (maxOrderCount n : ℝ)) ~[atTop]
      (fun n : ℕ ↦ ((n - 1).factorial : ℝ))) ∧
    (∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
      (n - 1).factorial ≤ orderCount n m →
        m ≤ n ∧ BekerCandidate n m) ∧
    (∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
      IsMode n m ↔ IsLeast {k : ℕ | BekerCandidate n k} m) := by
  sorry

end Erdos1161

end
