import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos728

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false
set_option linter.unusedSimpArgs false

namespace Erdos728b

open Real

open scoped Nat Topology

attribute [local instance] Classical.propDecidable

def good_triples (C ε : ℝ) : Set (ℕ × ℕ × ℕ) :=
  { t | let (a, b, n) := t; ε * n ≤ a ∧ a ≤ (1 - ε) * n ∧ ε * n ≤ b ∧ b ≤ (1 - ε) * n ∧
        Nat.factorial a * Nat.factorial b ∣ Nat.factorial n * Nat.factorial (a + b - n) ∧
        (a + b : ℝ) > n + C * Real.log n }
end Erdos728b

end Erdos728

attribute [local instance] Classical.propDecidable

theorem Erdos728.Erdos728b.erdos_728 :
    ∀ (C ε : Real),
      @LT.lt.{0} Real Real.instLT
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
        @LT.lt.{0} Real Real.instLT
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
          @LT.lt.{0} Real Real.instLT ε
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))) →
            @Set.Infinite.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat))
              (Erdos728.Erdos728b.good_triples C ε)
  := by
  sorry
theorem Erdos728.Erdos728b.erdos_728_fc :
    @Filter.Eventually.{0} Real
      (fun (ε : Real) ↦
        ∀ (C : Real),
          @GT.gt.{0} Real Real.instLT C
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
            ∀ (C' : Real),
              @GT.gt.{0} Real Real.instLT C' C →
                @Exists.{1} Nat fun (a : Nat) ↦
                  @Exists.{1} Nat fun (b : Nat) ↦
                    @Exists.{1} Nat fun (n : Nat) ↦
                      And
                        (@LT.lt.{0} Nat instLTNat
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)
                        (And
                          (@LT.lt.{0} Real Real.instLT
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) ε
                              (@Nat.cast.{0} Real Real.instNatCast n))
                            (@Nat.cast.{0} Real Real.instNatCast a))
                          (And
                            (@LT.lt.{0} Real Real.instLT
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) ε
                                (@Nat.cast.{0} Real Real.instNatCast n))
                              (@Nat.cast.{0} Real Real.instNatCast b))
                            (And
                              (@Dvd.dvd.{0} Nat Nat.instDvd
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  a.factorial b.factorial)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  n.factorial
                                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a
                                        b)
                                      n).factorial))
                              (And
                                (@GT.gt.{0} Real Real.instLT
                                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                    (@Nat.cast.{0} Real Real.instNatCast a)
                                    (@Nat.cast.{0} Real Real.instNatCast b))
                                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                    (@Nat.cast.{0} Real Real.instNatCast n)
                                    (@HMul.hMul.{0, 0, 0} Real Real Real
                                      (@instHMul.{0} Real Real.instMul) C
                                      (Real.log (@Nat.cast.{0} Real Real.instNatCast n)))))
                                (@LT.lt.{0} Real Real.instLT
                                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                    (@Nat.cast.{0} Real Real.instNatCast a)
                                    (@Nat.cast.{0} Real Real.instNatCast b))
                                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                    (@Nat.cast.{0} Real Real.instNatCast n)
                                    (@HMul.hMul.{0, 0, 0} Real Real Real
                                      (@instHMul.{0} Real Real.instMul) C'
                                      (Real.log (@Nat.cast.{0} Real Real.instNatCast n))))))))))
      (@nhdsWithin.{0} Real
        (@UniformSpace.toTopologicalSpace.{0} Real
          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@Set.Ioi.{0} Real Real.instPreorder
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
  := by
  sorry
