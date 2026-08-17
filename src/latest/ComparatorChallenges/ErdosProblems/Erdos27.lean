import Mathlib

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace Erdos27

structure ResidueSystem where
  moduli : Finset ℕ
  residue : (n : ℕ) → ZMod n
  modulus_pos : ∀ n ∈ moduli, 0 < n

end Erdos27

namespace Erdos27

def ResidueSystem.InWindow (A : ResidueSystem) (C : ℝ) (N : ℕ) : Prop :=
  ∀ n ∈ A.moduli, N ≤ n ∧ (n : ℝ) ≤ C * N

end Erdos27

namespace Erdos27

def ResidueSystem.period (A : ResidueSystem) : ℕ := A.moduli.lcm id

end Erdos27

namespace Erdos27

def ResidueSystem.uncovered (A : ResidueSystem) : Set ℤ :=
  {z | ∀ n ∈ A.moduli, (z : ZMod n) ≠ A.residue n}

end Erdos27

namespace Erdos27

def ResidueSystem.uncoveredMod (A : ResidueSystem) : Finset ℕ :=
  (Finset.range A.period).filter fun x => (x : ℤ) ∈ A.uncovered

end Erdos27

namespace Erdos27

def ResidueSystem.uncoveredDensity (A : ResidueSystem) : ℝ :=
  (A.uncoveredMod.card : ℝ) / A.period

end Erdos27

namespace Erdos27

def IsEpsilonAlmostCovering (C : ℝ) (N : ℕ) (ε : ℝ) : Prop :=
  ∃ A : ResidueSystem, A.InWindow C N ∧ A.uncoveredDensity ≤ ε

end Erdos27

namespace Erdos27

def Erdos27Question : Prop :=
  ∃ C : ℝ, 1 < C ∧
    ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, 1 ≤ N →
      IsEpsilonAlmostCovering C N ε

end Erdos27

namespace Erdos27

theorem erdos_27 : False ↔ Erdos27Question := by
  sorry

end Erdos27

end
