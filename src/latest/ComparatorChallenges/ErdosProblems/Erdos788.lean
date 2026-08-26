import Mathlib

namespace Erdos788

def I (n : ℕ) : Finset ℕ :=
  Finset.Ioo n (2 * n)

def J (n : ℕ) : Finset ℕ :=
  Finset.Ioo (2 * n) (4 * n)

/-- No two distinct members of the inner interval have their sum in the forbidden set. -/
def Admissible (n : ℕ) (B C : Finset ℕ) : Prop :=
  C ⊆ I n ∧
    ∀ ⦃c⦄, c ∈ C → ∀ ⦃c'⦄, c' ∈ C → c ≠ c' → c + c' ∉ B

def Guarantees (n t : ℕ) : Prop :=
  ∀ B : Finset ℕ, B ⊆ J n →
    ∃ C : Finset ℕ, Admissible n B C ∧ t ≤ B.card + C.card

def scoreBound (n : ℕ) : ℕ :=
  (J n).card + (I n).card

noncomputable def fNat (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (Guarantees n) (scoreBound n)

/-- The greatest integer that can be guaranteed for every forbidden set. -/
noncomputable def f (n : ℕ) : ℤ :=
  (fNat n : ℤ)

theorem erdos_788 :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      (n : ℝ) ^ ((1 / 2 : ℝ) - ε) ≤ (f n : ℝ) ∧
        (f n : ℝ) ≤ (n : ℝ) ^ ((1 / 2 : ℝ) + ε) := by
  sorry

theorem erdos_788_quantitative :
    (∀ n : ℕ, 3 ≤ n →
      (1 / 2000 : ℝ) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤ (f n : ℝ)) ∧
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      (f n : ℝ) ≤ (n : ℝ) ^ ((1 / 2 : ℝ) + C *
        (Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) ^ (1 / 3 : ℝ)) := by
  sorry

end Erdos788
