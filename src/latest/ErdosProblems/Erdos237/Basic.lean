import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace Erdos237

/-- The number of representations of `n` as a prime plus an element of `A`. -/
noncomputable def repCount (A : Set ℕ) (n : ℕ) : ℕ :=
  Set.ncard {a ∈ A | a ≤ n ∧ (n - a).Prime}

/-- Enlarging the set of allowed summands cannot decrease the count. -/
theorem repCount_mono {A B : Set ℕ} (h : A ⊆ B) (n : ℕ) :
    repCount A n ≤ repCount B n :=
  Set.ncard_le_ncard (fun _ hx ↦ ⟨h hx.1, hx.2.1, hx.2.2⟩) <|
    Set.finite_iff_bddAbove.2 ⟨n, fun _ hx ↦ hx.2.1⟩

end Erdos237
