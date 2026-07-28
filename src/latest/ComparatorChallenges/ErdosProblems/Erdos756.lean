import Mathlib.Analysis.CStarAlgebra.Classes

attribute [local instance] Classical.propDecidable

universe u_1

noncomputable abbrev Erdos756.distance_count.match_1 :
    (motive : Prod.{0, 0} Complex Complex → Sort u_1) →
      (x : Prod.{0, 0} Complex Complex) →
        ((x y : Complex) → motive (@Prod.mk.{0, 0} Complex Complex x y)) → motive x
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry

noncomputable def Erdos756.distance_count :
    Finset.{0} Complex → Real → Nat
  := by
  sorry

theorem Erdos756.erdos756 :
    ∀ (n : Nat),
      @Exists.{1} (Finset.{0} Complex) fun (P : Finset.{0} Complex) ↦
        And (@Eq.{1} Nat (@Finset.card.{0} Complex P) n)
          (@Exists.{1} (Finset.{0} Real) fun (S : Finset.{0} Real) ↦
            And
              (@LE.le.{0} (Finset.{0} Real)
                (@Preorder.toLE.{0} (Finset.{0} Real)
                  (@PartialOrder.toPreorder.{0} (Finset.{0} Real) (@Finset.instPartialOrder.{0} Real)))
                S
                (@Finset.image.{0, 0} (Prod.{0, 0} Complex Complex) Real Real.decidableEq
                  (fun (x : Prod.{0, 0} Complex Complex) ↦
                    Erdos756.distance_count.match_1.{1} (fun (x : Prod.{0, 0} Complex Complex) ↦ Real) x
                      fun (x y : Complex) ↦
                      @Dist.dist.{0} Complex
                        (@PseudoMetricSpace.toDist.{0} Complex
                          (@SeminormedRing.toPseudoMetricSpace.{0} Complex
                            (@SeminormedCommRing.toSeminormedRing.{0} Complex
                              (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                  instCommCStarAlgebraComplex)))))
                        x y)
                  (@Finset.offDiag.{0} Complex P)))
              (And
                (@Eq.{1} Nat (@Finset.card.{0} Real S)
                  (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                (∀ (d : Real),
                  @Membership.mem.{0, 0} Real (Finset.{0} Real)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Real) Real
                        (@Finset.instSetLike.{0} Real))
                      S d →
                    @GE.ge.{0} Nat instLENat (Erdos756.distance_count P d)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
  := by
  sorry
