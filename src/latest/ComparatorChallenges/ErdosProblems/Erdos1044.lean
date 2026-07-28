import Mathlib.Data.ENNReal.Basic

attribute [local instance] Classical.propDecidable

noncomputable def Erdos1044.lambdaInf :
    ENNReal
  := by
  sorry

theorem Erdos1044.erdos_problem_1044 :
    @Eq.{1} ENNReal Erdos1044.lambdaInf
      (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
          (@AddMonoidWithOne.toNatCast.{0} ENNReal
            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
  := by
  sorry
