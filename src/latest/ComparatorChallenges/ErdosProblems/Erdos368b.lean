import Mathlib.Order.Filter.AtTopBot.Defs

attribute [local instance] Classical.propDecidable

noncomputable def Erdos368b.P_plus :
    Nat → Nat
  := by
  sorry

theorem Erdos368b.n_n_plus_one_inf :
    @Filter.Tendsto.{0, 0} Nat Nat
      (fun (n : Nat) ↦
        Erdos368b.P_plus
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@Filter.atTop.{0} Nat Nat.instPreorder) (@Filter.atTop.{0} Nat Nat.instPreorder)
  := by
  sorry
