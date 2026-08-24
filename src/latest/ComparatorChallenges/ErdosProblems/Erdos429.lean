/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos429

noncomputable instance instFintypeSetInterIccNat (B : Set ℕ) (a b : ℕ) :
    Fintype ↑(B ∩ Set.Icc a b) :=
  ((Set.finite_Icc a b).subset (by
    intro x hx
    exact hx.2)).fintype
def Admissible (B : Set ℕ) : Prop :=
  ∀ p, p.Prime → ∃ (a : ZMod p), ∀ b ∈ B, (b : ZMod p) ≠ a

theorem erdos_429 (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) :
    ∃ B : Set ℕ, B.Infinite ∧
    (∀ N, (B ∩ Set.Icc 1 N).toFinset.card ≤ f N) ∧
    Admissible B ∧
    (∀ n : ℤ, ∃ b ∈ B, ¬ Nat.Prime (Int.toNat (b + n))) := by
  sorry

end Erdos429
