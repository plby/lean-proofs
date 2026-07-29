import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Erdos484

open Finset

open Finset

noncomputable def monochromaticSumSet (N : ℕ) (k : ℕ) (f : ℕ → Fin k) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter (fun n =>
    ∃ a ∈ Finset.Icc 1 N, ∃ b ∈ Finset.Icc 1 N, a ≠ b ∧ f a = f b ∧ a + b = n)
end Erdos484

attribute [local instance] Classical.propDecidable

theorem Erdos484.monochromatic_sums_linear :
    @Exists.{1} Real fun (c : Real) ↦
      And
        (@GT.gt.{0} Real Real.instLT c
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
        (∀ (k : Nat),
          @GE.ge.{0} Nat instLENat k (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
            @Exists.{1} Nat fun (N₀ : Nat) ↦
              ∀ (N : Nat),
                @GE.ge.{0} Nat instLENat N N₀ →
                  ∀ (f : Nat → Fin k),
                    @GE.ge.{0} Nat instLENat (@Finset.card.{0} Nat (Erdos484.monochromaticSumSet N k f))
                      (@Nat.floor.{0} Real Real.semiring Real.partialOrder
                        (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder
                          Real.instFloorRing)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c
                          (@Nat.cast.{0} Real Real.instNatCast N))))
  := by
  sorry
