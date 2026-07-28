import Mathlib.Order.LiminfLimsup
import Mathlib.Data.ENat.Lattice

attribute [local instance] Classical.propDecidable

noncomputable def Erdos379.S :
    Nat → Nat
  := by
  sorry

theorem Erdos379.erdos_379 :
    @Eq.{1} ENat
      (@Filter.limsup.{0, 0} ENat Nat
        (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENat
          (@ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENat
            (@CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENat
              instCompleteLinearOrderENat)))
        (fun (n : Nat) ↦ @Nat.cast.{0} ENat ENat.instNatCast (Erdos379.S n))
        (@Filter.atTop.{0} Nat Nat.instPreorder))
      (@Top.top.{0} ENat instTopENat)
  := by
  sorry
