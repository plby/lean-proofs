import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

attribute [local instance] Classical.propDecidable

universe u_1

noncomputable def Erdos753.listChromaticNumber :
    {V : Type u_1} → SimpleGraph.{u_1} V → Nat
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry

theorem Erdos753.erdos_753_negation :
    Not
      (@Exists.{1} Real fun (c : Real) ↦
        And
          (@GT.gt.{0} Real Real.instLT c
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
          (@Exists.{1} Nat fun (N : Nat) ↦
            ∀ (n : Nat),
              @LE.le.{0} Nat instLENat N n →
                ∀ (G : SimpleGraph.{0} (Fin n)),
                  @LT.lt.{0} Real Real.instLT
                    (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                      (@Nat.cast.{0} Real Real.instNatCast n)
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@OfNat.ofNat.{0} Real (nat_lit 2)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                (@Nat.instNeZeroSucc
                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
                        c))
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@Nat.cast.{0} Real Real.instNatCast
                        (@Erdos753.listChromaticNumber.{0} (Fin n) G))
                      (@Nat.cast.{0} Real Real.instNatCast
                        (@Erdos753.listChromaticNumber.{0} (Fin n)
                          (@Compl.compl.{0} (SimpleGraph.{0} (Fin n))
                            (@SimpleGraph.instCompl.{0} (Fin n)) G))))))
  := by
  sorry
