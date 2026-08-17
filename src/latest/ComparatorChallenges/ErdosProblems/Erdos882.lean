import Mathlib

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos882

def IsPrimitive (B : Finset ℕ) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, x ∣ y → x = y

end Erdos882

namespace Erdos882

def nonemptySubsetSums (A : Finset ℕ) : Finset ℕ :=
  ((A.powerset.filter fun S ↦ S.Nonempty).image fun S ↦ ∑ a ∈ S, a)

end Erdos882

namespace Erdos882

noncomputable def maximumSize (n : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 n).powerset.filter fun A ↦
    IsPrimitive (nonemptySubsetSums A)).sup Finset.card

end Erdos882

namespace Erdos882

theorem erdos_882 (n : ℕ) (hn : 0 < n) :
    Real.logb 2 (n : ℝ) - 1 < (maximumSize n : ℝ) := by
  sorry

end Erdos882

end
