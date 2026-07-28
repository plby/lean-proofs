import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base

attribute [local instance] Classical.propDecidable

universe u_1

noncomputable def Erdos1036.hom_num :
    {V : Type u_1} → SimpleGraph.{u_1} V → Nat
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry

noncomputable def Erdos1036.I_num :
    {V : Type u_1} → [Fintype.{u_1} V] → [DecidableEq.{u_1 + 1} V] → SimpleGraph.{u_1} V → Nat
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry

theorem Erdos1036.erdos_1036 :
    ∀ (c : Real),
      @GT.gt.{0} Real Real.instLT c
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
        @Exists.{1} Real fun (ε : Real) ↦
          And
            (@GT.gt.{0} Real Real.instLT ε
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
            (@Exists.{1} Nat fun (n₀ : Nat) ↦
              ∀ (n : Nat),
                @GE.ge.{0} Nat instLENat n n₀ →
                  ∀ {V : Type u_1} [inst : Fintype.{u_1} V] [inst_1 : DecidableEq.{u_1 + 1} V]
                    (G : SimpleGraph.{u_1} V)
                    [@DecidableRel.{u_1 + 1, u_1 + 1} V V (@SimpleGraph.Adj.{u_1} V G)],
                    @Eq.{1} Nat (@Fintype.card.{u_1} V inst) n →
                      @LE.le.{0} Real Real.instLE
                          (@Nat.cast.{0} Real Real.instNatCast (@Erdos1036.hom_num.{u_1} V G))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c
                            (Real.logb
                              (@OfNat.ofNat.{0} Real (nat_lit 2)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                              (@Nat.cast.{0} Real Real.instNatCast n))) →
                        @GE.ge.{0} Real Real.instLE
                          (@Nat.cast.{0} Real Real.instNatCast (@Erdos1036.I_num.{u_1} V inst inst_1 G))
                          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                            (@OfNat.ofNat.{0} Real (nat_lit 2)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) ε
                              (@Nat.cast.{0} Real Real.instNatCast n))))
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry
