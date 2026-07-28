import Mathlib.NumberTheory.Real.Irrational

attribute [local instance] Classical.propDecidable

axiom tao_teravainen :
    @Exists.{1} Real fun (C : Real) ↦
      And
        (@LT.lt.{0} Real Real.instLT
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C)
        (@Filter.Frequently.{0} Nat
          (fun (N : Nat) ↦
            ∀ (k : Nat),
              @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k →
                And
                  (@LE.le.{0} Nat instLENat
                    (@Finset.card.{0} Nat
                      (@Finsupp.support.{0, 0} Nat Nat
                        (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
                            k).factorization))
                    (@Finsupp.sum.{0, 0, 0} Nat Nat Nat
                      (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) Nat.instAddCommMonoid
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
                          k).factorization
                      fun (x k : Nat) ↦ k))
                  (@LE.le.{0} Real Real.instLE
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@Finsupp.sum.{0, 0, 0} Nat Nat Nat
                        (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) Nat.instAddCommMonoid
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
                            k).factorization
                        fun (x k : Nat) ↦ k))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                      (@Nat.cast.{0} Real Real.instNatCast k))))
          (@Filter.atTop.{0} Nat Nat.instPreorder))

noncomputable def Erdos258.erdosSeries :
    (Nat → Nat) → Real
  := by
  sorry

theorem Erdos258.erdos_258 :
    ∀ (a : Nat → Nat),
      (∀ (n : Nat),
          @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (a
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
        @Filter.Tendsto.{0, 0} Nat Nat a (@Filter.atTop.{0} Nat Nat.instPreorder)
            (@Filter.atTop.{0} Nat Nat.instPreorder) →
          Irrational (Erdos258.erdosSeries a)
  := by
  sorry
