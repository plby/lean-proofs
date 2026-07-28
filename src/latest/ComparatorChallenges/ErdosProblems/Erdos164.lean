import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Defs

attribute [local instance] Classical.propDecidable

noncomputable def Erdos164.primeSet :
    Set.{0} Nat
  := by
  sorry

noncomputable def Erdos164.PrimitiveSet :
    Set.{0} Nat → Prop
  := by
  sorry

noncomputable def Erdos164.primitiveWeightSum :
    Set.{0} Nat → Real
  := by
  sorry

noncomputable def Erdos164.primeWeightSum :
    Real
  := by
  sorry

theorem Erdos164.erdos164 :
    And (Erdos164.PrimitiveSet Erdos164.primeSet)
      (And (@Eq.{1} Real (Erdos164.primitiveWeightSum Erdos164.primeSet) Erdos164.primeWeightSum)
        (∀ (A : Set.{0} Nat),
          Erdos164.PrimitiveSet A →
            @LE.le.{0} Real Real.instLE (Erdos164.primitiveWeightSum A)
              (Erdos164.primitiveWeightSum Erdos164.primeSet)))
  := by
  sorry

noncomputable def Erdos164.erdos_strong :
    Nat → Prop
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
