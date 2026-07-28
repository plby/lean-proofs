import Mathlib.Analysis.SpecialFunctions.Log.Basic

attribute [local instance] Classical.propDecidable

universe u_1

noncomputable abbrev Erdos457.erdos_457.match_1 :
    (motive : Nat → Sort u_1) → (x : Nat) → ((n : Nat) → motive n) → motive x
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry

noncomputable def Erdos457.F :
    Nat → Nat
  := by
  sorry

theorem Erdos457.thm_main :
    @Set.Infinite.{0} Nat
      (@setOf.{0} Nat fun (n : Nat) ↦
        ∀ (p : Nat),
          Nat.Prime p →
            @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast p)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfScientific.ofScientific.{0} Real
                    (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) (nat_lit 21) Bool.true
                    (nat_lit 1))
                  (Real.log (@Nat.cast.{0} Real Real.instNatCast n))) →
              @Dvd.dvd.{0} Nat Nat.instDvd p (Erdos457.F n))
  := by
  sorry

theorem Erdos457.erdos_457 :
    @Exists.{1} Real fun (ε : Real) ↦
      And
        (@GT.gt.{0} Real Real.instLT ε
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
        (@Set.Infinite.{0} Nat
          (@setOf.{0} Nat fun (x : Nat) ↦
            Erdos457.erdos_457.match_1.{1} (fun (x : Nat) ↦ Prop) x fun (n : Nat) ↦
              ∀ (p : Nat),
                @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast p)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@OfNat.ofNat.{0} Real (nat_lit 2)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                              (@Nat.instNeZeroSucc
                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                        ε)
                      (Real.log (@Nat.cast.{0} Real Real.instNatCast n))) →
                  Nat.Prime p →
                    @Dvd.dvd.{0} Nat Nat.instDvd p
                      (@Finset.prod.{0, 0} Nat Nat Nat.instCommMonoid
                        (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.floor.{0} Real Real.semiring Real.partialOrder
                            (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder
                              Real.instFloorRing)
                            (Real.log (@Nat.cast.{0} Real Real.instNatCast n))))
                        fun (i : Nat) ↦
                        @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n i)))
  := by
  sorry
