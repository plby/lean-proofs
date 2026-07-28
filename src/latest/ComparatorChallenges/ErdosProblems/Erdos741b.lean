import Mathlib.Order.CompletePartialOrder
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.BooleanAlgebra
import Mathlib.Algebra.Group.Pointwise.Set.Basic

open scoped Pointwise

attribute [local instance] Classical.propDecidable

noncomputable def Erdos741b.upperDensity :
    Set.{0} Nat → Real
  := by
  sorry

noncomputable def Erdos741b.HasNatDensity :
    Set.{0} Nat → Real → Prop
  := by
  sorry

namespace Erdos741b

structure BiPartition (A : Set ℕ) where
  left : Set ℕ
  right : Set ℕ
  disj : Disjoint left right
  cover : left ∪ right = A

end Erdos741b

theorem Erdos741b.erdos741_upper_density :
    ∀ (A : Set.{0} Nat),
      @GT.gt.{0} Real Real.instLT
          (Erdos741b.upperDensity
            (@HAdd.hAdd.{0, 0, 0} (Set.{0} Nat) (Set.{0} Nat) (Set.{0} Nat)
              (@instHAdd.{0} (Set.{0} Nat) (@Set.add.{0} Nat instAddNat)) A A))
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
        @Exists.{1} (Erdos741b.BiPartition A) fun (P : Erdos741b.BiPartition A) ↦
          And
            (@GT.gt.{0} Real Real.instLT
              (Erdos741b.upperDensity
                (@HAdd.hAdd.{0, 0, 0} (Set.{0} Nat) (Set.{0} Nat) (Set.{0} Nat)
                  (@instHAdd.{0} (Set.{0} Nat) (@Set.add.{0} Nat instAddNat))
                  (@Erdos741b.BiPartition.left A P) (@Erdos741b.BiPartition.left A P)))
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
            (@GT.gt.{0} Real Real.instLT
              (Erdos741b.upperDensity
                (@HAdd.hAdd.{0, 0, 0} (Set.{0} Nat) (Set.{0} Nat) (Set.{0} Nat)
                  (@instHAdd.{0} (Set.{0} Nat) (@Set.add.{0} Nat instAddNat))
                  (@Erdos741b.BiPartition.right A P) (@Erdos741b.BiPartition.right A P)))
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
  := by
  sorry

theorem Erdos741b.erdos741_strict_density_counterexample :
    @Exists.{1} (Set.{0} Nat) fun (A : Set.{0} Nat) ↦
      And
        (Erdos741b.HasNatDensity
          (@HAdd.hAdd.{0, 0, 0} (Set.{0} Nat) (Set.{0} Nat) (Set.{0} Nat)
            (@instHAdd.{0} (Set.{0} Nat) (@Set.add.{0} Nat instAddNat)) A A)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
        (∀ (P : Erdos741b.BiPartition A),
          Not
            (@Exists.{1} Real fun (d₁ : Real) ↦
              And
                (@GT.gt.{0} Real Real.instLT d₁
                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
                (@Exists.{1} Real fun (d₂ : Real) ↦
                  And
                    (@GT.gt.{0} Real Real.instLT d₂
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
                    (And
                      (Erdos741b.HasNatDensity
                        (@HAdd.hAdd.{0, 0, 0} (Set.{0} Nat) (Set.{0} Nat) (Set.{0} Nat)
                          (@instHAdd.{0} (Set.{0} Nat) (@Set.add.{0} Nat instAddNat))
                          (@Erdos741b.BiPartition.left A P) (@Erdos741b.BiPartition.left A P))
                        d₁)
                      (Erdos741b.HasNatDensity
                        (@HAdd.hAdd.{0, 0, 0} (Set.{0} Nat) (Set.{0} Nat) (Set.{0} Nat)
                          (@instHAdd.{0} (Set.{0} Nat) (@Set.add.{0} Nat instAddNat))
                          (@Erdos741b.BiPartition.right A P) (@Erdos741b.BiPartition.right A P))
                        d₂)))))
  := by
  sorry
