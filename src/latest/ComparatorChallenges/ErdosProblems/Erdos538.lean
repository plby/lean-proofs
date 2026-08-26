import Mathlib

namespace Erdos538

/-- The prime-multiple representations of a natural number. For positive
members of the family, every representing prime is at most that number. -/
def representations (A : Finset ℕ) (m : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (m + 1)).product A).filter
    (fun pa => Nat.Prime pa.1 ∧ m = pa.1 * pa.2)

def Admissible (r N : ℕ) (A : Finset ℕ) : Prop :=
  (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧
    ∀ m : ℕ, (representations A m).card ≤ r

/-- The exact reciprocal sum. -/
def reciprocalMass (A : Finset ℕ) : ℚ :=
  ∑ a ∈ A, (1 : ℚ) / a

/-- An explicit universal upper estimate and matching admissible witnesses. -/
theorem erdos_538 (r N : ℕ) (hr : 2 ≤ r) (hN : 2 ≤ N) :
    (∀ A : Finset ℕ, Admissible r N A →
      Real.log (Real.log (N + 1)) * (reciprocalMass A : ℝ) ≤
        2 * r * (1 + Real.log (N * N))) ∧
    (∃ A : Finset ℕ, Admissible r N A ∧
      Real.log (N + 1) ≤
        4 + (8192 * (Nat.log 2 (Nat.log 2 N) + 1) : ℕ) *
          (reciprocalMass A : ℝ)) := by
  sorry

end Erdos538
