import Mathlib.Analysis.CStarAlgebra.Classes

attribute [local instance] Classical.propDecidable

theorem Erdos498.littlewood_offord_complex_bound :
    ∀ (n : Nat) (z : Fin n → Complex),
      (∀ (i : Fin n),
          @LT.lt.{0} Real Real.instLT
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@Norm.norm.{0} Complex Complex.instNorm (z i))) →
        ∀ (c : Complex),
          have signs :=
            @Insert.insert.{0, 0} Int (Finset.{0} Int) (@Finset.instInsert.{0} Int Int.instDecidableEq)
              (@Neg.neg.{0} Int Int.instNegInt
                (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
              (@Singleton.singleton.{0, 0} Int (Finset.{0} Int) (@Finset.instSingleton.{0} Int)
                (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))));
          have all_coeffs :=
            @Set.ofPred.{0} (Fin n → Int) fun (ε : Fin n → Int) ↦
              ∀ (i : Fin n),
                @Membership.mem.{0, 0} Int (Finset.{0} Int)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Int) Int (@Finset.instSetLike.{0} Int))
                  signs (ε i);
          have valid_sums :=
            @Set.ofPred.{0} (Fin n → Int) fun (ε : Fin n → Int) ↦
              And
                (@Membership.mem.{0, 0} (Fin n → Int) (Set.{0} (Fin n → Int))
                  (@Set.instMembership.{0} (Fin n → Int)) all_coeffs ε)
                (@Membership.mem.{0, 0} Complex (Set.{0} Complex) (@Set.instMembership.{0} Complex)
                  (@Metric.closedBall.{0} Complex
                    (@SeminormedRing.toPseudoMetricSpace.{0} Complex
                      (@SeminormedCommRing.toSeminormedRing.{0} Complex
                        (@NormedCommRing.toSeminormedCommRing.{0} Complex
                          (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                            instCommCStarAlgebraComplex))))
                    c (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                  (@Finset.sum.{0, 0} (Fin n) Complex Complex.instAddCommMonoid
                    (@Finset.univ.{0} (Fin n) (Fin.fintype n)) fun (i : Fin n) ↦
                    @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
                      (@Int.cast.{0} Complex Complex.instIntCast (ε i)) (z i)));
          @LE.le.{0} Nat instLENat (@Set.ncard.{0} (Fin n → Int) valid_sums)
            (n.choose
              (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  := by
  sorry
