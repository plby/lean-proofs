import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Std.Tactic.BVDecide.LRAT.Internal.Clause

open Finset Nat

namespace Erdos1136

noncomputable def countIn (S : Set ℕ) (n : ℕ) : ℕ :=
  @Finset.card ℕ ((Finset.Icc 1 n).filter (fun x => @decide (x ∈ S) (Classical.dec _)))

def pow2SumFree (S : Set ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ k : ℕ, a + b ≠ 2 ^ k
end Erdos1136

attribute [local instance] Classical.propDecidable

theorem Erdos1136.main_result :
    And
      (@Exists.{1} (Set.{0} Nat) fun (S : Set.{0} Nat) ↦
        And (Erdos1136.pow2SumFree S)
          (@Filter.Tendsto.{0, 0} Nat Real
            (fun (n : Nat) ↦
              @HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@Nat.cast.{0} Real Real.instNatCast (Erdos1136.countIn S n))
                (@Nat.cast.{0} Real Real.instNatCast n))
            (@Filter.atTop.{0} Nat Nat.instPreorder)
            (@nhds.{0} Real
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))))
      (∀ (S : Set.{0} Nat),
        Erdos1136.pow2SumFree S →
          @LE.le.{0} Real Real.instLE
            (@Filter.limsup.{0, 0} Real Nat
              (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} Real
                Real.instConditionallyCompleteLinearOrder)
              (fun (n : Nat) ↦
                @HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@Nat.cast.{0} Real Real.instNatCast (Erdos1136.countIn S n))
                  (@Nat.cast.{0} Real Real.instNatCast n))
              (@Filter.atTop.{0} Nat Nat.instPreorder))
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
  := by
  sorry
theorem Erdos1136.general_upper_bound :
    ∀ (s : Nat → Nat),
      (∀ (k : Nat),
          @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (s k)) →
        @StrictMono.{0, 0} Nat Nat Nat.instPreorder Nat.instPreorder s →
          (∀ (k : Nat),
              @LE.le.{0} Nat instLENat
                (s
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (s k))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
            ∀ (n : Nat),
              @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
                ∀ (A : Finset.{0} Nat),
                  @LE.le.{0} (Finset.{0} Nat)
                      (@Preorder.toLE.{0} (Finset.{0} Nat)
                        (@PartialOrder.toPreorder.{0} (Finset.{0} Nat)
                          (@Finset.instPartialOrder.{0} Nat)))
                      A
                      (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n) →
                    @GT.gt.{0} Nat instLTNat
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                          (@Finset.card.{0} Nat A))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                          (s (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) →
                      @Exists.{1} Nat fun (i : Nat) ↦
                        @Exists.{1} Nat fun (a : Nat) ↦
                          And
                            (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                (@Finset.instSetLike.{0} Nat))
                              A a)
                            (@Exists.{1} Nat fun (b : Nat) ↦
                              And
                                (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                    (@Finset.instSetLike.{0} Nat))
                                  A b)
                                (@Eq.{1} Nat
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a b)
                                  (s i)))
  := by
  sorry
theorem Erdos1136.general_upper_bound_infinite :
    ∀ (s : Nat → Nat),
      (∀ (k : Nat),
          @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (s k)) →
        @StrictMono.{0, 0} Nat Nat Nat.instPreorder Nat.instPreorder s →
          (∀ (k : Nat),
              @LE.le.{0} Nat instLENat
                (s
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (s k))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
            ∀ (A : Set.{0} Nat),
              @LT.lt.{0} Real Real.instLT
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
                  (@Filter.limsup.{0, 0} Real Nat
                    (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} Real
                      Real.instConditionallyCompleteLinearOrder)
                    (fun (n : Nat) ↦
                      @HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@Nat.cast.{0} Real Real.instNatCast (Erdos1136.countIn A n))
                        (@Nat.cast.{0} Real Real.instNatCast n))
                    (@Filter.atTop.{0} Nat Nat.instPreorder)) →
                @Set.Infinite.{0} Nat
                  (@setOf.{0} Nat fun (i : Nat) ↦
                    @Exists.{1} Nat fun (a : Nat) ↦
                      And (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) A a)
                        (@Exists.{1} Nat fun (b : Nat) ↦
                          And
                            (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) A b)
                            (@Eq.{1} Nat
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a b)
                              (s i))))
  := by
  sorry
