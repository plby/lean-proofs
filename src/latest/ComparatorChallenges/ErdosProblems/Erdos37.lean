/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped Pointwise

namespace Erdos37

def positivePart (A : Set ℕ) : Set ℕ :=
  {n | 0 < n ∧ n ∈ A}

def IsLacunary (A : Set ℕ) : Prop :=
  (positivePart A).Infinite ∧
    ∃ q : ℝ, 1 < q ∧
      ∀ i : ℕ,
        q * (Nat.nth (· ∈ positivePart A) i : ℝ) ≤
          (Nat.nth (· ∈ positivePart A) (i + 1) : ℝ)

noncomputable abbrev sd (A : Set ℕ) : ℝ :=
  @schnirelmannDensity A (fun n => Classical.propDecidable (n ∈ A))

def IsEssentialComponent (A : Set ℕ) : Prop :=
  ∀ B : Set ℕ,
    0 < sd B →
    sd B < 1 →
    sd B < sd (A + B)

theorem not_erdos_37 :
    ∀ A : Set ℕ, IsLacunary A → ¬ IsEssentialComponent A := by
  sorry

end Erdos37
