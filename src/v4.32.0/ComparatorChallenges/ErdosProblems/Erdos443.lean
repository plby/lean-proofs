import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos443

set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.whitespace false
set_option linter.flexible false
set_option linter.unusedVariables false

open scoped Classical

open scoped Pointwise

set_option maxHeartbeats 0
set_option linter.style.cases false
set_option linter.style.longLine false
set_option linter.style.multiGoal false
set_option linter.style.refine false

def A (k : ℕ) : Finset ℕ :=
  (Finset.Ioo 0 k).image (fun r => r * (k - r))
end Erdos443

attribute [local instance] Classical.propDecidable

theorem Erdos443.erdos_443_part_one :
    ∀ (s : Nat),
      @Exists.{1} Nat fun (m : Nat) ↦
        @Exists.{1} Nat fun (n : Nat) ↦
          And (@LT.lt.{0} Nat instLTNat n m)
            (@LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast s)
              (@Nat.cast.{0} Real Real.instNatCast
                (@Finset.card.{0} Nat
                  (@Inter.inter.{0} (Finset.{0} Nat) (@Finset.instInter.{0} Nat instDecidableEqNat)
                    (Erdos443.A n) (Erdos443.A m)))))
  := by
  sorry
theorem Erdos443.erdos_443_part_two :
    ∀ (ε : Real),
      @LT.lt.{0} Real Real.instLT
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
        @Exists.{1} Nat fun (n₀ : Nat) ↦
          ∀ (m n : Nat),
            @LT.lt.{0} Nat instLTNat n₀ n →
              @LT.lt.{0} Nat instLTNat n m →
                @LT.lt.{0} Real Real.instLT
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@Finset.card.{0} Nat
                      (@Inter.inter.{0} (Finset.{0} Nat) (@Finset.instInter.{0} Nat instDecidableEqNat)
                        (Erdos443.A n) (Erdos443.A m))))
                  (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@Nat.cast.{0} Real Real.instNatCast m) (@Nat.cast.{0} Real Real.instNatCast n))
                    ε)
  := by
  sorry
