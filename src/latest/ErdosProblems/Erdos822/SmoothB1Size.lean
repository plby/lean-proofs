/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.SmoothB1Cofactors
import ErdosProblems.Erdos822.SmoothPart

/-! # Smooth-part size follows directly from bounded prime powers -/

namespace Erdos822

open scoped BigOperators Classical
open Filter

theorem smoothPart_le_cutoff_pow_cutoff {m y : ℕ} (hy : 1 ≤ y)
    (hbounded : SmallPrimePowersBounded m y) : smoothPart m y ≤ y ^ y := by
  have hsupport : (smoothFactorization m y).support ⊆ Finset.Icc 1 y := by
    intro p hp
    have hp' : p ∈ m.primeFactors ∧ p ≤ y := by
      simpa [smoothFactorization, Finsupp.support_filter] using hp
    exact Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hp'.1).one_le, hp'.2⟩
  have hcard : (smoothFactorization m y).support.card ≤ y := by
    have h := Finset.card_le_card hsupport
    simpa using h
  calc
    smoothPart m y = ∏ p ∈ (smoothFactorization m y).support, p ^ m.factorization p := by
      exact Finsupp.prod_filter_index _ _ _
    _ ≤ ∏ _p ∈ (smoothFactorization m y).support, y := by
      apply Finset.prod_le_prod'
      intro p hp
      have hp' : p ∈ m.primeFactors ∧ p ≤ y := by
        simpa [smoothFactorization, Finsupp.support_filter] using hp
      exact hbounded p (Nat.prime_of_mem_primeFactors hp'.1) hp'.2
    _ = y ^ (smoothFactorization m y).support.card := by simp
    _ ≤ y ^ y := Nat.pow_le_pow_right hy hcard

theorem b1Cutoff_pow_self_le_natLog {N : ℕ} (hN : 2 ≤ N) (hy : 1 ≤ b1Cutoff N) :
    b1Cutoff N ^ b1Cutoff N ≤ Nat.log 2 N := by
  have hK : Nat.log 2 N ≠ 0 := by
    have h := Nat.le_log_of_pow_le (by norm_num : 1 < 2) (show 2 ^ 1 ≤ N by simpa using hN)
    omega
  calc
    b1Cutoff N ^ b1Cutoff N ≤ (2 ^ b1Cutoff N) ^ b1Cutoff N :=
      Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
    _ = 2 ^ (b1Cutoff N ^ 2) := by rw [← pow_mul, pow_two]
    _ ≤ 2 ^ (b1Cutoff N ^ 4) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right hy (by norm_num))
    _ ≤ 2 ^ b1DoubleLog N := Nat.pow_le_pow_right (by norm_num) (nthRoot_pow_le (by norm_num))
    _ ≤ Nat.log 2 N := Nat.pow_log_le_self 2 hK

theorem smoothB1Cofactors_smoothPart_le_natLog {N m : ℕ}
    (hN : 2 ≤ N) (hy : 1 ≤ b1Cutoff N) (hm : m ∈ smoothB1Cofactors N) :
    smoothPart m (b1Cutoff N) ≤ Nat.log 2 N :=
  (smoothPart_le_cutoff_pow_cutoff hy (smoothB1Cofactors_smallPrimePowersBounded hN hm)).trans
    (b1Cutoff_pow_self_le_natLog hN hy)

theorem eventually_smoothB1Cofactors_smoothPart_le_natLog :
    ∀ᶠ N : ℕ in atTop, ∀ m ∈ smoothB1Cofactors N,
      smoothPart m (b1Cutoff N) ≤ Nat.log 2 N := by
  filter_upwards [eventually_ge_atTop 2, tendsto_b1Cutoff_atTop.eventually_ge_atTop 1]
    with N hN hy
  exact fun m hm ↦ smoothB1Cofactors_smoothPart_le_natLog hN hy hm

#print axioms eventually_smoothB1Cofactors_smoothPart_le_natLog

end Erdos822
