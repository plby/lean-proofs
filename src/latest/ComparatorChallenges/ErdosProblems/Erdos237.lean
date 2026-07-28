import Mathlib.Analysis.SpecialFunctions.Log.Basic

attribute [local instance] Classical.propDecidable

noncomputable def Admissible :
    Finset.{0} Int → Prop
  := by
  sorry

axiom maynard_tao :
    ∀ (m : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m →
        ∀ (B : Finset.{0} Int),
          Admissible B →
            @LT.lt.{0} Real Real.instLT
                (Real.exp
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@OfNat.ofNat.{0} Real (nat_lit 8)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat
                            (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                            (@Nat.instNeZeroSucc
                              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))
                      (@Nat.cast.{0} Real Real.instNatCast m))
                    (@OfNat.ofNat.{0} Real (nat_lit 4)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          (@Nat.instNeZeroSucc
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{0} Int B))
                  (Real.log (@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{0} Int B)))) →
              ∀ (N : Nat),
                @Exists.{1} Int fun (n : Int) ↦
                  And (@LT.lt.{0} Int Int.instLTInt (@Nat.cast.{0} Int instNatCastInt N) n)
                    (@LE.le.{0} Nat instLENat m
                      (@Finset.card.{0} Int
                        (@Finset.filter.{0} Int
                          (fun (b : Int) ↦
                            Nat.Prime
                              (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) n
                                  b).natAbs)
                          (fun (a : Int) ↦
                            (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) n
                                  a).natAbs.decidablePrime)
                          B)))

noncomputable def Erdos237.repCount :
    Set.{0} Nat → Nat → Nat
  := by
  sorry

theorem Erdos237.erdos_237 :
    ∀ (A : Set.{0} Nat),
      @Set.Infinite.{0} Nat A →
        ∀ (C : Nat), @Exists.{1} Nat fun (n : Nat) ↦ @LT.lt.{0} Nat instLTNat C (Erdos237.repCount A n)
  := by
  sorry
