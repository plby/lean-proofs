import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos866b

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.whitespace false

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

open Finset
open scoped Pointwise

attribute [local instance] Classical.propDecidable

def HasPairwiseSums (A : Finset ℤ) (k : ℕ) : Prop :=
  ∃ b : Fin k → ℤ, Function.Injective b ∧ ∀ i j : Fin k, i < j → b i + b j ∈ A

def HasPosPairwiseSums (A : Finset ℤ) (k : ℕ) : Prop :=
  ∃ b : Fin k → ℤ, Function.Injective b ∧ (∀ i : Fin k, 0 < b i) ∧
    ∀ i j : Fin k, i < j → b i + b j ∈ A

noncomputable def gFun (k n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ (A : Finset ℤ), A ⊆ Icc (1 : ℤ) (2 * ↑n) →
    n + m ≤ A.card → HasPairwiseSums A k}

noncomputable def hFun (k n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ (A : Finset ℤ), A ⊆ Icc (1 : ℤ) (2 * ↑n) →
    n + m ≤ A.card → HasPosPairwiseSums A k}
section SidonBound

open Real

end SidonBound

end Erdos866b

attribute [local instance] Classical.propDecidable

theorem Erdos866b.g3 :
    ∀ (n : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) n →
        @Eq.{1} Nat (Erdos866b.gFun (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) n)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
  := by
  sorry
theorem Erdos866b.h3 :
    ∀ (n : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) n →
        @Eq.{1} Nat (Erdos866b.hFun (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) n)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
  := by
  sorry
theorem Erdos866b.g4 :
    ∀ (n : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n →
        @Eq.{1} Nat (Erdos866b.gFun (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) n)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
  := by
  sorry
theorem Erdos866b.h4upper :
    ∀ (n : Nat),
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
        @LE.le.{0} Nat instLENat
          (Erdos866b.hFun (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) n)
          (@OfNat.ofNat.{0} Nat (nat_lit 2270) (instOfNatNat (nat_lit 2270)))
  := by
  sorry
theorem Erdos866b.g5upper :
    ∀ (n : Nat),
      @LT.lt.{0} Nat instLTNat
        (Erdos866b.gFun (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) n)
        (@OfNat.ofNat.{0} Nat (nat_lit 120000000) (instOfNatNat (nat_lit 120000000)))
  := by
  sorry
theorem Erdos866b.generalupper :
    ∀ (k : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) k →
        @Exists.{1} Nat fun (N : Nat) ↦
          ∀ (n : Nat),
            @LE.le.{0} Nat instLENat N n →
              And (@LE.le.{0} Nat instLENat (Erdos866b.gFun k n) (Erdos866b.hFun k n))
                (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (Erdos866b.hFun k n))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 4)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          (@Nat.instNeZeroSucc
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                    (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                      (@Nat.cast.{0} Real Real.instNatCast n)
                      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                            (@OfNat.ofNat.{0} Real (nat_lit 2)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                              (@Nat.cast.{0} Real Real.instNatCast k)
                              (@OfNat.ofNat.{0} Real (nat_lit 2)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                        (instOfNatNat (nat_lit 0))))))))))))))
  := by
  sorry
