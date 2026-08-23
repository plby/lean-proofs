/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter Asymptotics

noncomputable section

namespace Erdos1161

open scoped Classical in
noncomputable def possibleOrders (n : ℕ) : Finset ℕ :=
  Finset.univ.image (fun σ : Equiv.Perm (Fin n) ↦ orderOf σ)

end Erdos1161

namespace Erdos1161

open scoped Classical in
noncomputable def orderCount (n m : ℕ) : ℕ :=
  Fintype.card {σ : Equiv.Perm (Fin n) // orderOf σ = m}

end Erdos1161

namespace Erdos1161

open scoped Classical in
noncomputable def maxOrderCount (n : ℕ) : ℕ :=
  (possibleOrders n).sup (orderCount n)

end Erdos1161

namespace Erdos1161

open scoped Classical in
def BekerCandidate (n m : ℕ) : Prop :=
  0 < m ∧ Nat.lcmUpto (n - m) ∣ m

end Erdos1161

namespace Erdos1161

open scoped Classical in
def IsMode (n m : ℕ) : Prop :=
  ∀ j : ℕ, orderCount n j ≤ orderCount n m

end Erdos1161

namespace Erdos1161

open scoped Classical in
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
