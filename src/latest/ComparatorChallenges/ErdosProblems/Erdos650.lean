import Mathlib.Analysis.Real.Sqrt
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos650

set_option linter.style.setOption false
set_option linter.flexible false

open Finset Real Nat

def HasDivMatching (A : Finset ℕ) (B : Finset ℤ) (r : ℕ) : Prop :=
  ∃ (c : Fin r → ℕ) (b : Fin r → ℤ),
    Function.Injective c ∧ Function.Injective b ∧
    (∀ i, c i ∈ A) ∧ (∀ i, b i ∈ B) ∧
    (∀ i, (c i : ℤ) ∣ b i)

noncomputable def erdos_f (m : ℕ) : ℕ :=
  sSup { r : ℕ | ∀ (A : Finset ℕ), (∀ a ∈ A, 0 < a) → A.card = m →
    ∀ (x : ℝ), HasDivMatching A (Finset.Ioo ⌊x⌋ ⌈x + 2 * ↑(A.sup id)⌉) r }
end Erdos650

attribute [local instance] Classical.propDecidable

theorem Erdos650.erdos_f_eq :
    ∀ (m : Nat),
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m →
        @Eq.{1} Nat (Erdos650.erdos_f m)
          (@Min.min.{0} Nat instMinNat m
            (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
              (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                (@Nat.cast.{0} Real Real.instNatCast m).sqrt)))
  := by
  sorry
