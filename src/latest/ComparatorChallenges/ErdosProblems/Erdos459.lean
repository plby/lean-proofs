import Mathlib

namespace Erdos459

def f (u : ℕ) : ℕ :=
  if h : u < 2 then 0
  else Nat.find (show ∃ v, u < v ∧ v.primeFactors ⊆ u.primeFactors by

    obtain ⟨p, hp⟩ : ∃ p, Nat.Prime p ∧ p ∣ u := by
      exact Nat.exists_prime_and_dvd ( by linarith )

    use u * p
    exact ⟨
      lt_mul_of_one_lt_right ( by linarith ) hp.1.one_lt,
      fun x hx => by
        rw [ Nat.primeFactors_mul ] at * <;> aesop⟩)
attribute [local instance] Classical.propDecidable

end Erdos459

attribute [local instance] Classical.propDecidable

theorem Erdos459.main_theorem :
    ∀ (ε δ : Real),
      @LT.lt.{0} Real Real.instLT
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
        @LT.lt.{0} Real Real.instLT
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) δ →
          @Exists.{1} Real fun (x₀ : Real) ↦
            ∀ (x : Real),
              @GE.ge.{0} Real Real.instLE x x₀ →
                @GE.ge.{0} Real Real.instLE
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@Finset.card.{0} Nat
                      (@Finset.filter.{0} Nat
                        (fun (n : Nat) ↦
                          @LT.lt.{0} Real Real.instLT
                            (@Nat.cast.{0} Real Real.instNatCast (Erdos459.f n))
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                (@OfNat.ofNat.{0} Real (nat_lit 1)
                                  (@One.toOfNat1.{0} Real Real.instOne))
                                ε)
                              (@Nat.cast.{0} Real Real.instNatCast n)))
                        (fun (a : Nat) ↦
                          (@Nat.cast.{0} Real Real.instNatCast (Erdos459.f a)).decidableLT
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                (@OfNat.ofNat.{0} Real (nat_lit 1)
                                  (@One.toOfNat1.{0} Real Real.instOne))
                                ε)
                              (@Nat.cast.{0} Real Real.instNatCast a)))
                        (Finset.range
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@Nat.floor.{0} Real Real.semiring Real.partialOrder
                              (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder
                                Real.instFloorRing)
                              x)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) δ)
                    x)
  := by
  sorry
