import Mathlib.Data.Finset.Card

open Finset Nat

namespace Erdos1193

open scoped Classical in
noncomputable def conv_ind (A : Set ℕ) (n : ℕ) : ℕ :=
  ((range (n + 1)).filter (fun k => k ∈ A ∧ (n - k) ∈ A)).card
end Erdos1193

attribute [local instance] Classical.propDecidable

theorem Erdos1193.erdos_convolution_counterexample :
    ∀ (n : Nat),
      @Eq.{1} Nat (Erdos1193.conv_ind (@Set.univ.{0} Nat) n)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
  := by
  sorry
