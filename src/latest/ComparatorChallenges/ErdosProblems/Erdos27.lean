/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos27

structure ResidueSystem where
  moduli : Finset ℕ
  residue : (n : ℕ) → ZMod n
  modulus_pos : ∀ n ∈ moduli, 0 < n

def ResidueSystem.InWindow (A : ResidueSystem) (C : ℝ) (N : ℕ) : Prop :=
  ∀ n ∈ A.moduli, N ≤ n ∧ (n : ℝ) ≤ C * N

def ResidueSystem.period (A : ResidueSystem) : ℕ := A.moduli.lcm id

def ResidueSystem.uncovered (A : ResidueSystem) : Set ℤ :=
  {z | ∀ n ∈ A.moduli, (z : ZMod n) ≠ A.residue n}

open scoped Classical in
noncomputable def ResidueSystem.uncoveredMod (A : ResidueSystem) : Finset ℕ :=
  (Finset.range A.period).filter fun x => (x : ℤ) ∈ A.uncovered

noncomputable def ResidueSystem.uncoveredDensity (A : ResidueSystem) : ℝ :=
  (A.uncoveredMod.card : ℝ) / A.period

def IsEpsilonAlmostCovering (C : ℝ) (N : ℕ) (ε : ℝ) : Prop :=
  ∃ A : ResidueSystem, A.InWindow C N ∧ A.uncoveredDensity ≤ ε

theorem not_erdos_27 :
    ¬ (∃ C : ℝ, 1 < C ∧
      ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, 1 ≤ N →
        IsEpsilonAlmostCovering C N ε) := by
  sorry

end Erdos27
