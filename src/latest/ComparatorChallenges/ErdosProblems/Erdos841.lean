import Mathlib

open scoped BigOperators symmDiff

namespace Erdos841

noncomputable section

attribute [local instance] Classical.propDecidable

def Admissible (n T : ℕ) : Prop :=
  ∃ J : Finset ℕ, J ⊆ Finset.Icc 1 T ∧
    IsSquare (n * ∏ j ∈ J, (n + j))

lemma exists_admissible (n : ℕ) : ∃ T, Admissible n T := by
  sorry

noncomputable def t (n : ℕ) : ℕ := Nat.find (exists_admissible n)

noncomputable def largestPrimeFactor (n : ℕ) : ℕ :=
  if h : n.primeFactors.Nonempty then n.primeFactors.max' h else 1

def powerThreshold (c : ℝ) (x : ℕ) : ℕ :=
  ⌊(x : ℝ) ^ c⌋₊

def manySmallUpTo (x : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter fun n ↦
    (t n : ℝ) ≤ Real.exp
      (20 * Real.sqrt (Real.log n * Real.log (Real.log n)))

def movingSmallTUpTo (x : ℕ) (c : ℝ) : Finset ℕ :=
  (Finset.Icc 1 x).filter fun n ↦ t n ≤ powerThreshold c n

def movingSmoothUpTo (x : ℕ) (c : ℝ) : Finset ℕ :=
  (Finset.Icc 1 x).filter fun n ↦ largestPrimeFactor n ≤ powerThreshold c n

theorem erdos841_comparator_resolution :
    (∀ n : ℕ, 1 < n →
      Real.sqrt (2 * (n : ℝ)) + 1 < (largestPrimeFactor n : ℝ) →
        t n = largestPrimeFactor n) ∧
    (∀ n : ℕ,
      (largestPrimeFactor n : ℝ) ≤ Real.sqrt (2 * (n : ℝ)) + 1 →
        (t n : ℝ) ≤ 40 * Real.sqrt (n : ℝ)) ∧
    (∀ c : ℝ, 0 < c → c ≤ 1 →
      Filter.Tendsto
        (fun x : ℕ ↦
          (((movingSmallTUpTo x c).card : ℝ) -
            ((movingSmoothUpTo x c).card : ℝ)) / (x : ℝ))
        Filter.atTop (nhds 0)) ∧
    (Filter.Tendsto
        (fun x : ℕ ↦ Real.log ((manySmallUpTo x).card : ℝ) /
          Real.log (x : ℝ))
        Filter.atTop (nhds 1) ∧
      ∀ x n : ℕ, n ∈ manySmallUpTo x ↔
        1 ≤ n ∧ n ≤ x ∧
          (t n : ℝ) ≤ Real.exp
            (20 * Real.sqrt (Real.log n * Real.log (Real.log n)))) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in Filter.atTop, ¬IsSquare n →
      C *
          (Real.log (Real.log (n : ℝ)) ^ ((6 : ℝ) / 5) *
            Real.log (Real.log (Real.log (n : ℝ))) ^ (-((1 : ℝ) / 5))) ≤
        (t n : ℝ)) := by
  sorry

end

end Erdos841
