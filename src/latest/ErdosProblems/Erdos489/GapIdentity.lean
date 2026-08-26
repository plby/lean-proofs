import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

open scoped BigOperators

/-- The number of empty subwindows, summed over all positive lengths, inside a
gap of length `g` is the triangular sum `0 + ... + (g-1)`. -/
def emptyWindowMass (g : ℕ) : ℕ := ∑ h ∈ Finset.range g, h

/-- Exact layer-cake identity for one squared gap. -/
theorem gap_square_eq_gap_add_twice_emptyWindowMass (g : ℕ) :
    (g : ℤ) ^ 2 = (g : ℤ) + 2 * (emptyWindowMass g : ℤ) := by
  induction g with
  | zero => simp [emptyWindowMass]
  | succ g ih =>
      rw [emptyWindowMass, Finset.sum_range_succ]
      rw [emptyWindowMass] at ih
      push_cast at ih ⊢
      nlinarith

/-- Summed layer-cake identity for any finite family of gap lengths. -/
theorem sum_gap_squares_eq_sum_gaps_add_twice_emptyWindowMass
    (s : Finset ℕ) (gap : ℕ → ℕ) :
    (∑ i ∈ s, (gap i : ℤ) ^ 2) =
      (∑ i ∈ s, (gap i : ℤ)) + 2 * ∑ i ∈ s, (emptyWindowMass (gap i) : ℤ) := by
  calc
    (∑ i ∈ s, (gap i : ℤ) ^ 2) =
        ∑ i ∈ s, ((gap i : ℤ) + 2 * (emptyWindowMass (gap i) : ℤ)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact gap_square_eq_gap_add_twice_emptyWindowMass (gap i)
    _ = (∑ i ∈ s, (gap i : ℤ)) +
        2 * ∑ i ∈ s, (emptyWindowMass (gap i) : ℤ) := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum]

end Erdos489
