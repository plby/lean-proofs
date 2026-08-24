/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos202

def residueClass (q : ℕ) (a : ℤ) : Set ℤ :=
  {n : ℤ | n ≡ a [ZMOD (q : ℤ)]}

abbrev ResidueAssignment (Q : Finset ℕ) : Type :=
  {q : ℕ // q ∈ Q} → ℤ

def PairwiseDisjointResidues
    (Q : Finset ℕ) (a : ResidueAssignment Q) : Prop :=
  ∀ i j : {q : ℕ // q ∈ Q}, i ≠ j →
    Disjoint (residueClass i.1 (a i)) (residueClass j.1 (a j))

def Admissible (N : ℕ) (Q : Finset ℕ) : Prop :=
  (∀ q ∈ Q, 1 ≤ q ∧ q ≤ N) ∧
  ∃ a : ResidueAssignment Q, PairwiseDisjointResidues Q a

def PossibleCard (N r : ℕ) : Prop :=
  ∃ Q : Finset ℕ, Admissible N Q ∧ Q.card = r

noncomputable def f (N : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (PossibleCard N) N

noncomputable def Zscale (N : ℕ) : ℝ :=
  Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)))

noncomputable def Lscale (α : ℝ) (N : ℕ) : ℝ :=
  Real.exp (α * Zscale N)

def HasErdos202Asymptotic (F : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    (N : ℝ) * Lscale (-(1 + ε)) N ≤ (F N : ℝ) ∧
    (F N : ℝ) ≤ (N : ℝ) * Lscale (-(1 - ε)) N

end Erdos202

theorem Erdos202.erdos_202 :
    Erdos202.HasErdos202Asymptotic Erdos202.f := by
  sorry
