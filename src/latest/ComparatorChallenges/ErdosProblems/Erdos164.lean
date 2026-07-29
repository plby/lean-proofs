import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Std.Tactic.BVDecide.LRAT.Internal.Clause

open scoped Topology

noncomputable section

namespace Erdos164

noncomputable def erdosWeight (n : ℕ) : ℝ :=
  1 / ((n : ℝ) * Real.log n)
def primeSet : Set ℕ :=
  { p | p.Prime }
def PrimitiveSet (A : Set ℕ) : Prop :=
  (∀ ⦃a : ℕ⦄, a ∈ A → 2 ≤ a) ∧
    ∀ ⦃a b : ℕ⦄, a ∈ A → b ∈ A → a ∣ b → a = b
noncomputable def primitiveWeightSum (A : Set ℕ) : ℝ :=
  ∑' a : A, erdosWeight (a : ℕ)
noncomputable def primeWeightSum : ℝ :=
  primitiveWeightSum primeSet
open Filter Asymptotics
open scoped Nat.Prime

def IsPRough (p m : ℕ) : Prop :=
  ∀ q : ℕ, q.Prime → q ∣ m → p ≤ q
def erdos_strong (n : ℕ) : Prop :=
  ∀ ⦃A : Set ℕ⦄, PrimitiveSet A →
    A ⊆ {m : ℕ | n ∣ m ∧ IsPRough n (m / n)} →
    primitiveWeightSum A ≤ erdosWeight n
end Erdos164

attribute [local instance] Classical.propDecidable

theorem Erdos164.erdos164 :
    And (Erdos164.PrimitiveSet Erdos164.primeSet)
      (And (@Eq.{1} Real (Erdos164.primitiveWeightSum Erdos164.primeSet) Erdos164.primeWeightSum)
        (∀ (A : Set.{0} Nat),
          Erdos164.PrimitiveSet A →
            @LE.le.{0} Real Real.instLE (Erdos164.primitiveWeightSum A)
              (Erdos164.primitiveWeightSum Erdos164.primeSet)))
  := by
  sorry
theorem Erdos164.erdos_strong_of_two :
    Erdos164.erdos_strong (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
  := by
  sorry
theorem Erdos164.erdos_strong_of_prime :
    ∀ {p : Nat}, Nat.Prime p → Erdos164.erdos_strong p
  := by
  sorry
theorem Erdos164.erdos164_alt :
    And (Erdos164.PrimitiveSet Erdos164.primeSet)
      (And (@Eq.{1} Real (Erdos164.primitiveWeightSum Erdos164.primeSet) Erdos164.primeWeightSum)
        (∀ (A : Set.{0} Nat),
          Erdos164.PrimitiveSet A →
            @LE.le.{0} Real Real.instLE (Erdos164.primitiveWeightSum A)
              (Erdos164.primitiveWeightSum Erdos164.primeSet)))
  := by
  sorry
