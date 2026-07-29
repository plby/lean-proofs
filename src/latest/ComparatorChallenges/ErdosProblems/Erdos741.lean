import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Std.Tactic.BVDecide.LRAT.Internal.Clause

open Filter

namespace Set

@[inline]
noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

noncomputable def upperDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : ℝ :=
  atTop.limsup fun (b : β) ↦ S.partialDensity A b
namespace HasDensity

end HasDensity

end Set

attribute [local instance] Classical.propDecidable

universe u_1

theorem Erdos741.erdos_741.variants.upper :
    Iff True
      (∀ (A : Set.{0} Nat),
        @LT.lt.{0} Real Real.instLT
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (@Set.upperDensity.{0} Nat Nat.instPreorder
              (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder
                Nat.instLocallyFiniteOrder Nat.instOrderBot)
              (@HAdd.hAdd.{0, 0, 0} (Set.{0} Nat) (Set.{0} Nat) (Set.{0} Nat)
                (@instHAdd.{0} (Set.{0} Nat) (@Set.add.{0} Nat instAddNat)) A A)
              (@Set.univ.{0} Nat)) →
          @Exists.{1} (Set.{0} Nat) fun (A₁ : Set.{0} Nat) ↦
            @Exists.{1} (Set.{0} Nat) fun (A₂ : Set.{0} Nat) ↦
              And
                (@Eq.{1} (Set.{0} Nat) A
                  (@Union.union.{0} (Set.{0} Nat) (@Set.instUnion.{0} Nat) A₁ A₂))
                (And
                  (@Disjoint.{0} (Set.{0} Nat)
                    (@CompletePartialOrder.toPartialOrder.{0} (Set.{0} Nat)
                      (@CompleteLattice.toCompletePartialOrder.{0} (Set.{0} Nat)
                        (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} Nat)
                          (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} Nat)
                            (@Set.instCompleteAtomicBooleanAlgebra.{0} Nat)))))
                    (@CompletePartialOrder.toOrderBot.{0} (Set.{0} Nat)
                      (@CompleteLattice.toCompletePartialOrder.{0} (Set.{0} Nat)
                        (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} Nat)
                          (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} Nat)
                            (@Set.instCompleteAtomicBooleanAlgebra.{0} Nat)))))
                    A₁ A₂)
                  (And
                    (@LT.lt.{0} Real Real.instLT
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                      (@Set.upperDensity.{0} Nat Nat.instPreorder
                        (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder
                          Nat.instLocallyFiniteOrder Nat.instOrderBot)
                        (@HAdd.hAdd.{0, 0, 0} (Set.{0} Nat) (Set.{0} Nat) (Set.{0} Nat)
                          (@instHAdd.{0} (Set.{0} Nat) (@Set.add.{0} Nat instAddNat)) A₁ A₁)
                        (@Set.univ.{0} Nat)))
                    (@LT.lt.{0} Real Real.instLT
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                      (@Set.upperDensity.{0} Nat Nat.instPreorder
                        (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder
                          Nat.instLocallyFiniteOrder Nat.instOrderBot)
                        (@HAdd.hAdd.{0, 0, 0} (Set.{0} Nat) (Set.{0} Nat) (Set.{0} Nat)
                          (@instHAdd.{0} (Set.{0} Nat) (@Set.add.{0} Nat instAddNat)) A₂ A₂)
                        (@Set.univ.{0} Nat))))))
  := by
  sorry
