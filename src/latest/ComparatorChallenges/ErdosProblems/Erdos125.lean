import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Group.Pointwise.Set.Basic

open scoped Pointwise

attribute [local instance] Classical.propDecidable

universe u_1

noncomputable def Set.lowerDensity :
    {β : Type u_1} →
      [inst : Preorder.{u_1} β] →
        [@LocallyFiniteOrderBot.{u_1} β inst] →
          Set.{u_1} β → optParam.{u_1 + 1} (Set.{u_1} β) (@Set.univ.{u_1} β) → Real
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry

noncomputable def Set.HasPosDensity :
    {β : Type u_1} →
      [inst : Preorder.{u_1} β] →
        [@LocallyFiniteOrderBot.{u_1} β inst] →
          Set.{u_1} β → optParam.{u_1 + 1} (Set.{u_1} β) (@Set.univ.{u_1} β) → Prop
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry

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
