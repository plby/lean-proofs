import Mathlib.Analysis.Complex.Norm
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos519

open Finset Complex

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.longLine false
set_option maxHeartbeats 10000000

noncomputable def powerSum {n : ℕ} (z : Fin n → ℂ) (k : ℕ) : ℂ :=
  ∑ m : Fin n, z m ^ k
end Erdos519

attribute [local instance] Classical.propDecidable

theorem Erdos519.erdos519 :
    ∀ {n : Nat}
      (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)
      (z : Fin n → Complex),
      @Eq.{1} Complex (z (@Fin.mk n (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hn))
          (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)) →
        @Exists.{1} (Fin n) fun (k : Fin n) ↦
          @LT.lt.{0} Real Real.instLT
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@OfNat.ofNat.{0} Real (nat_lit 6)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat
                    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                    (@Nat.instNeZeroSucc
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))))
            (@Norm.norm.{0} Complex Complex.instNorm
              (@Erdos519.powerSum n z
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val n k)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  := by
  sorry
