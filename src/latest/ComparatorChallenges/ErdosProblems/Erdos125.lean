import Mathlib.Order.LiminfLimsup
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Std.Tactic.BVDecide.LRAT.Internal.Clause

open Filter

open scoped Topology

namespace Set

@[inline]
noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

noncomputable def lowerDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : ℝ :=
  atTop.liminf fun (b : β) ↦ S.partialDensity A b

def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => S.partialDensity A b) atTop (𝓝 α)

def HasPosDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : Prop :=
  ∃ α > 0, S.HasDensity α A
namespace HasDensity

end HasDensity

end Set

open scoped Pointwise

attribute [local instance] Classical.propDecidable

universe u_1

theorem Erdos125.erdos_125 :
    Iff False
      (@Set.HasPosDensity.{0} Nat Nat.instPreorder
        (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
          Nat.instOrderBot)
        (@HAdd.hAdd.{0, 0, 0} (Set.{0} Nat) (Set.{0} Nat) (Set.{0} Nat)
          (@instHAdd.{0} (Set.{0} Nat) (@Set.add.{0} Nat instAddNat))
          (@setOf.{0} Nat fun (x : Nat) ↦
            @LE.le.{0} (Finset.{0} Nat)
              (@Preorder.toLE.{0} (Finset.{0} Nat)
                (@PartialOrder.toPreorder.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat)))
              (@List.toFinset.{0} Nat instDecidableEqNat
                (Nat.digits (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) x))
              (@Insert.insert.{0, 0} Nat (Finset.{0} Nat)
                (@Finset.instInsert.{0} Nat instDecidableEqNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@Singleton.singleton.{0, 0} Nat (Finset.{0} Nat) (@Finset.instSingleton.{0} Nat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (@setOf.{0} Nat fun (x : Nat) ↦
            @LE.le.{0} (Finset.{0} Nat)
              (@Preorder.toLE.{0} (Finset.{0} Nat)
                (@PartialOrder.toPreorder.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat)))
              (@List.toFinset.{0} Nat instDecidableEqNat
                (Nat.digits (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) x))
              (@Insert.insert.{0, 0} Nat (Finset.{0} Nat)
                (@Finset.instInsert.{0} Nat instDecidableEqNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@Singleton.singleton.{0, 0} Nat (Finset.{0} Nat) (@Finset.instSingleton.{0} Nat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
        (@Set.univ.{0} Nat))
  := by
  sorry
theorem Erdos125.erdos_125.variants.positive_lower_density :
    Iff False
      (@LT.lt.{0} Real Real.instLT
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@Set.lowerDensity.{0} Nat Nat.instPreorder
          (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder
            Nat.instLocallyFiniteOrder Nat.instOrderBot)
          (@HAdd.hAdd.{0, 0, 0} (Set.{0} Nat) (Set.{0} Nat) (Set.{0} Nat)
            (@instHAdd.{0} (Set.{0} Nat) (@Set.add.{0} Nat instAddNat))
            (@setOf.{0} Nat fun (x : Nat) ↦
              @LE.le.{0} (Finset.{0} Nat)
                (@Preorder.toLE.{0} (Finset.{0} Nat)
                  (@PartialOrder.toPreorder.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat)))
                (@List.toFinset.{0} Nat instDecidableEqNat
                  (Nat.digits (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) x))
                (@Insert.insert.{0, 0} Nat (Finset.{0} Nat)
                  (@Finset.instInsert.{0} Nat instDecidableEqNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@Singleton.singleton.{0, 0} Nat (Finset.{0} Nat) (@Finset.instSingleton.{0} Nat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            (@setOf.{0} Nat fun (x : Nat) ↦
              @LE.le.{0} (Finset.{0} Nat)
                (@Preorder.toLE.{0} (Finset.{0} Nat)
                  (@PartialOrder.toPreorder.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat)))
                (@List.toFinset.{0} Nat instDecidableEqNat
                  (Nat.digits (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) x))
                (@Insert.insert.{0, 0} Nat (Finset.{0} Nat)
                  (@Finset.instInsert.{0} Nat instDecidableEqNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@Singleton.singleton.{0, 0} Nat (Finset.{0} Nat) (@Finset.instSingleton.{0} Nat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
          (@Set.univ.{0} Nat)))
  := by
  sorry
