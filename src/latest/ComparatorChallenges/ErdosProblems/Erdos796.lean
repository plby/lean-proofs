import Mathlib

namespace Erdos796

def positiveIcc (n : ℕ) : Finset ℕ := Finset.Icc 1 n

/-- Each product representation uses two distinct terms, ordered increasingly. -/
def strictProductRepCount (A : Finset ℕ) (m : ℕ) : ℕ :=
  ((A ×ˢ A).filter fun ab => ab.1 < ab.2 ∧ ab.1 * ab.2 = m).card

def Admissible (n : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ positiveIcc n ∧ ∀ m : ℕ, strictProductRepCount A m ≤ 2

/-- The largest size among all admissible subsets of the finite interval. -/
noncomputable def g3 (n : ℕ) : ℕ := by
  classical
  exact ((positiveIcc n).powerset.filter (Admissible n)).sup Finset.card

/-- The second-order constant exists and is less than fifteen. -/
theorem erdos_796_upper :
    ∃ c : ℝ, c < 15 ∧ Filter.Tendsto
      (fun n : ℕ =>
        ((g3 n : ℝ) - (n : ℝ) * Real.log (Real.log n) / Real.log n) /
          ((n : ℝ) / Real.log n))
      Filter.atTop (nhds c) := by
  sorry

/-- The normalized second-order residual has a finite limit. -/
theorem erdos_796 :
    ∃ c : ℝ, Filter.Tendsto
      (fun n : ℕ =>
        ((g3 n : ℝ) - (n : ℝ) * Real.log (Real.log n) / Real.log n) /
          ((n : ℝ) / Real.log n))
      Filter.atTop (nhds c) := by
  sorry

end Erdos796
