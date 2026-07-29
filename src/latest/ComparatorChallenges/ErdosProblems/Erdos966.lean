import Mathlib.Data.Real.Basic

namespace Erdos966

open scoped Real
open scoped Nat

set_option relaxedAutoImplicit false
set_option autoImplicit false

def HasAP (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, d ≠ 0 ∧ ∀ i : Fin k, a + i * d ∈ A
def HasMonochromaticAP (A : Set ℕ) (k : ℕ) {r : ℕ} (c : ℕ → Fin r) : Prop :=
  ∃ a d : ℕ,
    d ≠ 0 ∧ (∀ i : Fin k, a + i * d ∈ A) ∧
      ∃ y : Fin r, ∀ i : Fin k, c (a + i * d) = y
end Erdos966

attribute [local instance] Classical.propDecidable

theorem Erdos966.existence_of_AP_free_Ramsey_set :
    ∀ (k r : Nat),
      @GE.ge.{0} Nat instLENat k (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
        @GE.ge.{0} Nat instLENat r (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
          @Exists.{1} (Set.{0} Nat) fun (A : Set.{0} Nat) ↦
            And
              (Not
                (Erdos966.HasAP A
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (∀ (c : Nat → Fin r), @Erdos966.HasMonochromaticAP A k r c)
  := by
  sorry
