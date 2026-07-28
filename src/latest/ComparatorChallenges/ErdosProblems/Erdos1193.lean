import Mathlib.Data.Set.Defs

attribute [local instance] Classical.propDecidable

noncomputable def Erdos1193.conv_ind :
    Set.{0} Nat → Nat → Nat
  := by
  sorry

theorem Erdos1193.erdos_convolution_counterexample :
    ∀ (n : Nat),
      @Eq.{1} Nat (Erdos1193.conv_ind (@Set.univ.{0} Nat) n)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
  := by
  sorry
