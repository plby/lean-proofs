import Mathlib

namespace Erdos336

/-- Repeated summands are permitted. -/
def RepresentsExactly (A : Set ℕ) (k n : ℕ) : Prop :=
  ∃ xs : List ℕ, xs.length = k ∧ (∀ x ∈ xs, x ∈ A) ∧ xs.sum = n

def EventuallyExactly (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → RepresentsExactly A k n

/-- The number of summands may vary with the integer represented. -/
def EventuallyAtMost (A : Set ℕ) (r : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ k : ℕ, k ≤ r ∧ RepresentsExactly A k n

/-- Exact order is the least eventual exact number of summands. -/
def HasExactOrder (A : Set ℕ) (k : ℕ) : Prop :=
  EventuallyExactly A k ∧ ∀ j : ℕ, j < k → ¬ EventuallyExactly A j

def Admissible (r k : ℕ) : Prop :=
  ∃ A : Set ℕ, EventuallyAtMost A r ∧ HasExactOrder A k

/-- Each maximum must be both attained and an upper bound for every example. -/
def IsExtremalFunction (h : ℕ → ℕ) : Prop :=
  ∀ r : ℕ, 2 ≤ r →
    Admissible r (h r) ∧ ∀ k : ℕ, Admissible r k → k ≤ h r

/-- The finite attained maxima exist, and their normalized limit is one third. -/
theorem erdos_336 :
    (∃ h : ℕ → ℕ, IsExtremalFunction h) ∧
    ∀ h : ℕ → ℕ, IsExtremalFunction h →
      Filter.Tendsto (fun r : ℕ => (h r : ℝ) / (r : ℝ) ^ 2)
        Filter.atTop (nhds (1 / 3 : ℝ)) := by
  sorry

end Erdos336
