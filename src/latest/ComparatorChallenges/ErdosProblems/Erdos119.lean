import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Std.Tactic.BVDecide.LRAT.Internal.Clause

open Filter Finset Set
open Metric

namespace Erdos119

noncomputable def p (z : ℕ → ℂ) (n : ℕ) : ℂ → ℂ :=
  fun w => ∏ i ∈ range n, (w - z i)

noncomputable def M (z : ℕ → ℂ) (n : ℕ) : ℝ :=
  sSup {‖p z n w‖ | (w : ℂ) (_ : ‖w‖ = 1)}
end Erdos119

attribute [local instance] Classical.propDecidable

theorem Erdos119.erdos_119.parts.iii_quantitative :
    ∀ (z : Nat → Complex),
      (∀ (i : Nat),
          @Eq.{1} Real (@Norm.norm.{0} Complex Complex.instNorm (z i))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
        @Exists.{1} Real fun (C : Real) ↦
          And
            (@GT.gt.{0} Real Real.instLT C
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
            (@Filter.Eventually.{0} Nat
              (fun (n : Nat) ↦
                @LT.lt.{0} Real Real.instLT
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                        (@Nat.cast.{0} Real Real.instNatCast n)
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@OfNat.ofNat.{0} Real (nat_lit 5)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                (@Nat.instNeZeroSucc
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                          (@OfNat.ofNat.{0} Real (nat_lit 4)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                (@Nat.instNeZeroSucc
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                      (Real.log (@Nat.cast.{0} Real Real.instNatCast n)).sqrt))
                  (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (Finset.range n) fun (k : Nat) ↦
                    Erdos119.M z k))
              (@Filter.atTop.{0} Nat Nat.instPreorder))
  := by
  sorry
