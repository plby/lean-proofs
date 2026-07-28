import Mathlib.Data.Nat.ModEq
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Order.Filter.AtTopBot.Defs

attribute [local instance] Classical.propDecidable

noncomputable def Erdos1056b.erdos_1056 :
    Prop
  := by
  sorry

theorem Erdos1056b.noll_simmons :
    Erdos1056b.erdos_1056 →
      @Filter.Eventually.{0} Nat
        (fun (k : Nat) ↦
          @Exists.{1} Nat fun (p : Nat) ↦
            @Exists.{0} (Nat.Prime p) fun (x : Nat.Prime p) ↦
              @Exists.{1} (Fin k → Nat) fun (Q : Fin k → Nat) ↦
                @Exists.{0}
                  (@StrictMono.{0, 0} (Fin k) Nat
                    (@PartialOrder.toPreorder.{0} (Fin k) (@Fin.instPartialOrder k)) Nat.instPreorder Q)
                  fun
                    (x :
                      @StrictMono.{0, 0} (Fin k) Nat
                        (@PartialOrder.toPreorder.{0} (Fin k) (@Fin.instPartialOrder k))
                        Nat.instPreorder Q) ↦
                  @Exists.{0} (∀ (i : Fin k), @LT.lt.{0} Nat instLTNat (Q i) p)
                    fun (x : ∀ (i : Fin k), @LT.lt.{0} Nat instLTNat (Q i) p) ↦
                    ∀ (i j : Fin k), p.ModEq (Q i).factorial (Q j).factorial)
        (@Filter.atTop.{0} Nat Nat.instPreorder)
  := by
  sorry
