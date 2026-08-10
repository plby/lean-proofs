import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace Erdos314

open Finset Real MeasureTheory intervalIntegral

noncomputable section

set_option linter.style.setOption false
set_option linter.flexible false

def harmonicPartialSum (n m : ℕ) : ℝ :=
  ∑ ℓ ∈ Finset.Icc n m, (↑ℓ : ℝ)⁻¹
end
end Erdos314

attribute [local instance] Classical.propDecidable

theorem Erdos314.main_theorem :
    ∀ (c : Real),
      @GT.gt.{0} Real Real.instLT c
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
        ∀ (N : Nat),
          @Exists.{1} Nat fun (m : Nat) ↦
            @Exists.{1} Nat fun (n : Nat) ↦
              And (@LE.le.{0} Nat instLENat N n)
                (And
                  (@LE.le.{0} Real Real.instLE
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (Erdos314.harmonicPartialSum n m))
                  (@LE.le.{0} Real Real.instLE (Erdos314.harmonicPartialSum n m)
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) c
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat
                            (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                          (@Nat.cast.{0} Real Real.instNatCast n)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
  := by
  sorry
