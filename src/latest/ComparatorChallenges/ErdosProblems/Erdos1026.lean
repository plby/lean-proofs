import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Erdos1026

set_option linter.style.setOption false
set_option linter.style.maxHeartbeats false
set_option linter.style.whitespace false
set_option linter.style.cdot false
set_option linter.style.longLine false
set_option linter.style.emptyLine false
set_option linter.deprecated false
set_option linter.flexible false
set_option linter.unusedVariables false

set_option aesop.warn.nonterminal false
set_option maxHeartbeats 50000000
noncomputable section AristotleLemmas

end AristotleLemmas

noncomputable section AristotleLemmas

end AristotleLemmas

noncomputable section AristotleLemmas

end AristotleLemmas

noncomputable def IsMonotoneSubseq {n : ℕ} (x : Fin n → ℝ) (m : ℕ) (s : Fin (m + 1) → Fin n) : Prop :=
  StrictMono s ∧
    (Monotone (fun i => x (s i)) ∨ Antitone (fun i => x (s i)))

noncomputable def monoSubseqSumSet {n : ℕ} (x : Fin n → ℝ) : Set ℝ :=
  { r | ∃ (m : ℕ) (s : Fin (m + 1) → Fin n),
      IsMonotoneSubseq x m s ∧ r = ∑ i, x (s i) }

noncomputable def maxMonoSubseqSum {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  sSup (monoSubseqSumSet x)

noncomputable def score {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  maxMonoSubseqSum x / (∑ i, x i)

noncomputable def c_opt (n : ℕ) : ℝ :=
  sInf { r : ℝ |
    ∃ (x : Fin n → ℝ),
      (∀ i, 0 < x i) ∧
      Function.Injective x ∧
      r = score x }
end Erdos1026

attribute [local instance] Classical.propDecidable

theorem Erdos1026.c_opt_eq_k_div_sq_add_a :
    ∀ (k n : Nat) (a : Int),
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k →
        @LT.lt.{0} Int Int.instLTInt
            (@Neg.neg.{0} Int Int.instNegInt (@Nat.cast.{0} Int instNatCastInt k)) a →
          @LE.le.{0} Int Int.instLEInt a (@Nat.cast.{0} Int instNatCastInt k) →
            @Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt n)
                (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                  (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                    (@HPow.hPow.{0, 0, 0} Int Nat Int
                      (@instHPow.{0, 0} Int Nat
                        (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                      (@Nat.cast.{0} Int instNatCastInt k)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                  (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                    (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))) a)) →
              @Eq.{1} Real (Erdos1026.c_opt n)
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@Nat.cast.{0} Real Real.instNatCast k)
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@HPow.hPow.{0, 0, 0} Real Nat Real
                      (@instHPow.{0, 0} Real Nat
                        (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                      (@Nat.cast.{0} Real Real.instNatCast k)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@Int.cast.{0} Real Real.instIntCast a)))
  := by
  sorry
