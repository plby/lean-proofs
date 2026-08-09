import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

open Nat

namespace Erdos1056b

def AllModProdEqualsOne (p : ℕ) {k : ℕ} (boundaries : Fin (k + 1) → ℕ) : Prop :=
  ∀ i : Fin k,
    (∏ n ∈ Finset.Ico (boundaries i.castSucc) (boundaries (i.castSucc + 1)), n) ≡ 1 [MOD p]

def erdos_1056 : Prop :=
    (∀ k ≥ 2, ∃ (p : ℕ) (_ : p.Prime) (boundaries : Fin (k + 1) → ℕ) (_ : StrictMono boundaries),
    AllModProdEqualsOne p boundaries)
end Erdos1056b

attribute [local instance] Classical.propDecidable

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
