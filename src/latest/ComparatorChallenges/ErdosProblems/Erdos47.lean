import Mathlib.Analysis.SpecialFunctions.Log.Basic

attribute [local instance] Classical.propDecidable

noncomputable def UnitFractions.rec_sum :
    Finset.{0} Nat → Rat
  := by
  sorry

theorem Erdos47.erdos47_bloom :
    @Exists.{1} Real fun (C : Real) ↦
      And
        (@LT.lt.{0} Real Real.instLT
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C)
        (@Exists.{1} Nat fun (N₀ : Nat) ↦
          ∀ (N : Nat),
            @GE.ge.{0} Nat instLENat N N₀ →
              ∀ (A : Finset.{0} Nat),
                @LE.le.{0} (Finset.{0} Nat)
                    (@Preorder.toLE.{0} (Finset.{0} Nat)
                      (@PartialOrder.toPreorder.{0} (Finset.{0} Nat)
                        (@Finset.instPartialOrder.{0} Nat)))
                    A
                    (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) N) →
                  @LT.lt.{0} Real Real.instLT
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                            (Real.log (Real.log (Real.log (@Nat.cast.{0} Real Real.instNatCast N))))
                            (Real.log (Real.log (@Nat.cast.{0} Real Real.instNatCast N))))
                          (Real.log (@Nat.cast.{0} Real Real.instNatCast N))))
                      (@Rat.cast.{0} Real Real.instRatCast (UnitFractions.rec_sum A)) →
                    @Exists.{1} (Finset.{0} Nat) fun (S : Finset.{0} Nat) ↦
                      And
                        (@LE.le.{0} (Finset.{0} Nat)
                          (@Preorder.toLE.{0} (Finset.{0} Nat)
                            (@PartialOrder.toPreorder.{0} (Finset.{0} Nat)
                              (@Finset.instPartialOrder.{0} Nat)))
                          S A)
                        (@Eq.{1} Rat (UnitFractions.rec_sum S)
                          (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))))
  := by
  sorry

theorem Erdos47.erdos47 :
    ∀ (δ : Real),
      @GT.gt.{0} Real Real.instLT δ
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
        @Exists.{1} Nat fun (N₀ : Nat) ↦
          ∀ (N : Nat),
            @GE.ge.{0} Nat instLENat N N₀ →
              ∀ (A : Finset.{0} Nat),
                @LE.le.{0} (Finset.{0} Nat)
                    (@Preorder.toLE.{0} (Finset.{0} Nat)
                      (@PartialOrder.toPreorder.{0} (Finset.{0} Nat)
                        (@Finset.instPartialOrder.{0} Nat)))
                    A
                    (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) N) →
                  @LT.lt.{0} Real Real.instLT
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) δ
                        (Real.log (@Nat.cast.{0} Real Real.instNatCast N)))
                      (@Rat.cast.{0} Real Real.instRatCast (UnitFractions.rec_sum A)) →
                    @Exists.{1} (Finset.{0} Nat) fun (S : Finset.{0} Nat) ↦
                      And
                        (@LE.le.{0} (Finset.{0} Nat)
                          (@Preorder.toLE.{0} (Finset.{0} Nat)
                            (@PartialOrder.toPreorder.{0} (Finset.{0} Nat)
                              (@Finset.instPartialOrder.{0} Nat)))
                          S A)
                        (@Eq.{1} Rat (UnitFractions.rec_sum S)
                          (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
  := by
  sorry
