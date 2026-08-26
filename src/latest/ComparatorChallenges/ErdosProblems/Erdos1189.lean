import Mathlib

open Filter Finset
open scoped BigOperators Topology

namespace Erdos1189

def Covers (D : Finset ℕ) (a : ℕ → ℤ) : Prop :=
  ∀ z : ℤ, ∃ d ∈ D, z ≡ a d [ZMOD d]

def IsCoveringSet (D : Finset ℕ) : Prop :=
  (∀ d ∈ D, 1 < d) ∧ ∃ a : ℕ → ℤ, Covers D a

def IsIrreducibleCoveringSet (D : Finset ℕ) : Prop :=
  IsCoveringSet D ∧ ∀ E ⊂ D, ¬ IsCoveringSet E

def nontrivialDivisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter (1 < ·)

def reciprocalSum (D : Finset ℕ) : ℚ :=
  ∑ d ∈ D, (d : ℚ)⁻¹

def irreducibleSetsOfSize (k : ℕ) : Set (Finset ℕ) :=
  {D | IsIrreducibleCoveringSet D ∧ D.card = k}

noncomputable def irreducibleCount (k : ℕ) : ℕ :=
  (irreducibleSetsOfSize k).ncard

noncomputable def tau : ℝ :=
  ∑' t : ℕ, (Real.log (1 + 1 / ((t : ℝ) + 1))) ^ 2

def CountingAsymptotic : Prop :=
  (∀ k : ℕ, (irreducibleSetsOfSize k).Finite) ∧
    Tendsto (fun k : ℕ =>
      Real.log (irreducibleCount k) * Real.sqrt (Real.log k) /
        ((k : ℝ) * Real.sqrt k)) atTop (nhds (4 * Real.sqrt tau / 3))

def MaximumLargestModulusClaim : Prop :=
  ∀ k : ℕ, 5 ≤ k →
    (∀ D ∈ irreducibleSetsOfSize k, D.sup id ≤ 3 * 2 ^ (k - 3)) ∧
    ∃ D ∈ irreducibleSetsOfSize k, D.sup id = 3 * 2 ^ (k - 3)

def MinimumLargestModulusClaim : Prop :=
  (∀ D : Finset ℕ, IsCoveringSet D → D.card + 1 ≤ D.sup id) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 5 ≤ k →
      ∃ D ∈ irreducibleSetsOfSize k, ∀ d ∈ D,
        (d : ℝ) ≤ C * k * (Real.log k) ^ 2

def MaximumReciprocalSumClaim : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ k : ℕ in atTop,
    (∀ D ∈ irreducibleSetsOfSize k, (reciprocalSum D : ℝ) ≤ C * Real.log k) ∧
    ∃ D ∈ irreducibleSetsOfSize k, c * Real.log k ≤ (reciprocalSum D : ℝ)

def DivisorFamilyClaim : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 →
    IsIrreducibleCoveringSet (nontrivialDivisors (2 ^ (p - 1) * p))

def Erdos1189Statement : Prop :=
  (∀ D : Finset ℕ, IsCoveringSet D → 5 ≤ D.card) ∧
    CountingAsymptotic ∧ MaximumLargestModulusClaim ∧ MinimumLargestModulusClaim ∧
    MaximumReciprocalSumClaim ∧ DivisorFamilyClaim ∧
    {n : ℕ | IsIrreducibleCoveringSet (nontrivialDivisors n)}.Infinite

theorem erdos_1189 : Erdos1189Statement := by
  sorry

end Erdos1189
