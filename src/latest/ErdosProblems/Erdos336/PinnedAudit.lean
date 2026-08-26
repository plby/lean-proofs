import ErdosProblems.Erdos336.Problem336Solution

/-!
Independent acceptance statement for Erdős Problem 336.
The definitions below deliberately duplicate, rather than alias, the research
formalization.  The final theorem must typecheck against this pinned copy.
-/

namespace Erdos336.Checker

/-- `n` is a sum of exactly `k` members of `A`, with repetition allowed. -/
def RepresentsExactly (A : Set ℕ) (k n : ℕ) : Prop :=
  ∃ xs : List ℕ,
    xs.length = k ∧
    (∀ x ∈ xs, x ∈ A) ∧
    xs.sum = n

/-- Every sufficiently large natural has an exact `k`-term representation. -/
def EventuallyExactly (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → RepresentsExactly A k n

/-- Every sufficiently large natural uses a number of terms at most `r`. -/
def EventuallyAtMost (A : Set ℕ) (r : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ k : ℕ, k ≤ r ∧ RepresentsExactly A k n

/-- `k` is the least eventual exact order of `A`. -/
def HasExactOrder (A : Set ℕ) (k : ℕ) : Prop :=
  EventuallyExactly A k ∧
    ∀ j : ℕ, j < k → ¬ EventuallyExactly A j

/-- Exact order `k` is attainable by a basis of variable order at most `r`. -/
def Admissible (r k : ℕ) : Prop :=
  ∃ A : Set ℕ, EventuallyAtMost A r ∧ HasExactOrder A k

/-- `h(r)` is attained and dominates every attainable exact order for `r≥2`. -/
def IsExtremalFunction (h : ℕ → ℕ) : Prop :=
  ∀ r : ℕ, 2 ≤ r →
    Admissible r (h r) ∧ ∀ k : ℕ, Admissible r k → k ≤ h r

/-- An extremal function exists, and `h(r)/r²` converges to `c` for
every extremal function. -/
def HasProblem336Value (c : ℝ) : Prop :=
  (∃ h : ℕ → ℕ, IsExtremalFunction h) ∧
    ∀ h : ℕ → ℕ, IsExtremalFunction h →
      Filter.Tendsto (fun r : ℕ => (h r : ℝ) / (r : ℝ) ^ 2)
        Filter.atTop (nhds c)

/-- Acceptance theorem for the independently pinned statement. -/
theorem problem336_pinned : HasProblem336Value (1 / 3 : ℝ) := by
  exact Erdos336.problem336

end Erdos336.Checker
