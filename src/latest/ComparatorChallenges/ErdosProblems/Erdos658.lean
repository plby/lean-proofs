import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic

attribute [local instance] Classical.propDecidable

noncomputable def Erdos658.grid2 :
    Nat → Finset.{0} (Prod.{0, 0} Int Int)
  := by
  sorry

noncomputable def Erdos658.grid3 :
    Nat → Finset.{0} (Prod.{0, 0} Int (Prod.{0, 0} Int Int))
  := by
  sorry

noncomputable def Erdos658.ContainsSquare :
    Finset.{0} (Prod.{0, 0} Int Int) → Prop
  := by
  sorry

noncomputable def Erdos658.ContainsQuadruple :
    Finset.{0} (Prod.{0, 0} Int (Prod.{0, 0} Int Int)) → Prop
  := by
  sorry

noncomputable def Theorem_2_2 :
    Prop
  := by
  sorry

axiom frankl_roedl_theorem :
    Theorem_2_2

theorem Erdos658.Theorem_1_2 :
    Theorem_2_2 →
      ∀ (δ : Real),
        @GT.gt.{0} Real Real.instLT δ
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
          @Exists.{1} Nat fun (N₀ : Nat) ↦
            ∀ (N : Nat),
              @LT.lt.{0} Nat instLTNat N₀ N →
                ∀ (S : Finset.{0} (Prod.{0, 0} Int (Prod.{0, 0} Int Int))),
                  @LE.le.{0} (Finset.{0} (Prod.{0, 0} Int (Prod.{0, 0} Int Int)))
                      (@Preorder.toLE.{0} (Finset.{0} (Prod.{0, 0} Int (Prod.{0, 0} Int Int)))
                        (@PartialOrder.toPreorder.{0}
                          (Finset.{0} (Prod.{0, 0} Int (Prod.{0, 0} Int Int)))
                          (@Finset.instPartialOrder.{0} (Prod.{0, 0} Int (Prod.{0, 0} Int Int)))))
                      S (Erdos658.grid3 N) →
                    @LE.le.{0} Real Real.instLE
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) δ
                          (@HPow.hPow.{0, 0, 0} Real Nat Real
                            (@instHPow.{0, 0} Real Nat
                              (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                            (@Nat.cast.{0} Real Real.instNatCast N)
                            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                        (@Nat.cast.{0} Real Real.instNatCast
                          (@Finset.card.{0} (Prod.{0, 0} Int (Prod.{0, 0} Int Int)) S)) →
                      Erdos658.ContainsQuadruple S
  := by
  sorry

theorem Erdos658.Theorem_1_1 :
    Theorem_2_2 →
      ∀ (δ : Real),
        @GT.gt.{0} Real Real.instLT δ
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
          @Exists.{1} Nat fun (N₀ : Nat) ↦
            ∀ (N : Nat),
              @LT.lt.{0} Nat instLTNat N₀ N →
                ∀ (S : Finset.{0} (Prod.{0, 0} Int Int)),
                  @LE.le.{0} (Finset.{0} (Prod.{0, 0} Int Int))
                      (@Preorder.toLE.{0} (Finset.{0} (Prod.{0, 0} Int Int))
                        (@PartialOrder.toPreorder.{0} (Finset.{0} (Prod.{0, 0} Int Int))
                          (@Finset.instPartialOrder.{0} (Prod.{0, 0} Int Int))))
                      S (Erdos658.grid2 N) →
                    @LE.le.{0} Real Real.instLE
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) δ
                          (@HPow.hPow.{0, 0, 0} Real Nat Real
                            (@instHPow.{0, 0} Real Nat
                              (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                            (@Nat.cast.{0} Real Real.instNatCast N)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@Nat.cast.{0} Real Real.instNatCast
                          (@Finset.card.{0} (Prod.{0, 0} Int Int) S)) →
                      Erdos658.ContainsSquare S
  := by
  sorry

theorem Erdos658.erdos658 :
    ∀ (δ : Real),
      @GT.gt.{0} Real Real.instLT δ
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
        @Exists.{1} Nat fun (N₀ : Nat) ↦
          ∀ (N : Nat),
            @LT.lt.{0} Nat instLTNat N₀ N →
              ∀ (S : Finset.{0} (Prod.{0, 0} Int Int)),
                @LE.le.{0} (Finset.{0} (Prod.{0, 0} Int Int))
                    (@Preorder.toLE.{0} (Finset.{0} (Prod.{0, 0} Int Int))
                      (@PartialOrder.toPreorder.{0} (Finset.{0} (Prod.{0, 0} Int Int))
                        (@Finset.instPartialOrder.{0} (Prod.{0, 0} Int Int))))
                    S (Erdos658.grid2 N) →
                  @LE.le.{0} Real Real.instLE
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) δ
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat
                            (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                          (@Nat.cast.{0} Real Real.instNatCast N)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{0} (Prod.{0, 0} Int Int) S)) →
                    Erdos658.ContainsSquare S
  := by
  sorry
