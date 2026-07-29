import Mathlib.Data.Nat.Squarefree

namespace Erdos844

set_option linter.style.setOption false
set_option linter.flexible false

open Finset Nat

noncomputable def erdosSarkozySet (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun k => 2 ∣ k ∨ ¬ Squarefree k)
end Erdos844

attribute [local instance] Classical.propDecidable

theorem Erdos844.erdos_sarkozy :
    ∀ (N : Nat) (A : Finset.{0} Nat),
      @LE.le.{0} (Finset.{0} Nat)
          (@Preorder.toLE.{0} (Finset.{0} Nat)
            (@PartialOrder.toPreorder.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat)))
          A
          (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) N) →
        (∀ (a : Nat),
            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) A
                a →
              ∀ (b : Nat),
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                    A b →
                  Not
                    (@Squarefree.{0} Nat Nat.instMonoid
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) a b))) →
          @LE.le.{0} Nat instLENat (@Finset.card.{0} Nat A)
            (@Finset.card.{0} Nat (Erdos844.erdosSarkozySet N))
  := by
  sorry
