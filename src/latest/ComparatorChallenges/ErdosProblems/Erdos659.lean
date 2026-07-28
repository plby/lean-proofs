import Mathlib.Analysis.InnerProductSpace.PiL2

attribute [local instance] Classical.propDecidable

structure BinQuadForm where
  a : ℤ
  b : ℤ
  c : ℤ

noncomputable def BinQuadForm.discr :
    BinQuadForm → Int
  := by
  sorry

noncomputable def BinQuadForm.Primitive :
    BinQuadForm → Prop
  := by
  sorry

noncomputable def BinQuadForm.PosDef :
    BinQuadForm → Prop
  := by
  sorry

noncomputable def BinQuadForm.B :
    BinQuadForm → Real → Nat
  := by
  sorry

axiom bernays :
    ∀ (Δ : Int),
      Not
          (@Exists.{1} Int fun (z : Int) ↦
            @Eq.{1} Int (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) z z) Δ) →
        @Exists.{1} Real fun (CΔ : Real) ↦
          And
            (@LT.lt.{0} Real Real.instLT
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) CΔ)
            (∀ (f : BinQuadForm),
              f.Primitive →
                f.PosDef →
                  @Eq.{1} Int f.discr Δ →
                    @Asymptotics.IsEquivalent.{0, 0} Real Real
                      (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                        (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                          (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                            (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
                      (@Filter.atTop.{0} Real Real.instPreorder)
                      (fun (x : Real) ↦ @Nat.cast.{0} Real Real.instNatCast (f.B x)) fun (x : Real) ↦
                      @HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) CΔ x)
                        (Real.log x).sqrt)

noncomputable def Erdos659.distinctDistances :
    Finset.{0}
        (EuclideanSpace.{0, 0} Real
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
      Nat
  := by
  sorry

theorem Erdos659.erdos_659 :
    @Exists.{1}
      (Nat →
        Finset.{0}
          (EuclideanSpace.{0, 0} Real
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      fun
        (A :
          Nat →
            Finset.{0}
              (EuclideanSpace.{0, 0} Real
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))) ↦
      And
        (∀ (n : Nat),
          And
            (@Eq.{1} Nat
              (@Finset.card.{0}
                (EuclideanSpace.{0, 0} Real
                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (A n))
              n)
            (∀
              (S :
                Finset.{0}
                  (EuclideanSpace.{0, 0} Real
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))),
              @LE.le.{0}
                  (Finset.{0}
                    (EuclideanSpace.{0, 0} Real
                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                  (@Preorder.toLE.{0}
                    (Finset.{0}
                      (EuclideanSpace.{0, 0} Real
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                    (@PartialOrder.toPreorder.{0}
                      (Finset.{0}
                        (EuclideanSpace.{0, 0} Real
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                      (@Finset.instPartialOrder.{0}
                        (EuclideanSpace.{0, 0} Real
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                  S (A n) →
                @Eq.{1} Nat
                    (@Finset.card.{0}
                      (EuclideanSpace.{0, 0} Real
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      S)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                    (Erdos659.distinctDistances S)))
        (@Asymptotics.IsBigO.{0, 0, 0} Nat Real Real Real.norm Real.norm
          (@Filter.atTop.{0} Nat Nat.instPreorder)
          (fun (n : Nat) ↦ @Nat.cast.{0} Real Real.instNatCast (Erdos659.distinctDistances (A n)))
          fun (n : Nat) ↦
          @HDiv.hDiv.{0, 0, 0} Real Real Real
            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@Nat.cast.{0} Real Real.instNatCast n)
            (Real.log (@Nat.cast.{0} Real Real.instNatCast n)).sqrt)
  := by
  sorry
