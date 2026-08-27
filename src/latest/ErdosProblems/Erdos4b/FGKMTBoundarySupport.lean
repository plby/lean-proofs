/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTBoundaryFactor
import ErdosProblems.Erdos4b.FGKMTConvolutionMoments
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Exact support of the pre-sieve boundary factor

Its absolute value is `1 / n` on the squarefree divisors of the nonzero
modulus, and zero elsewhere. Both moments are therefore finite sums;
their quantitative bounds are handled separately.
-/

namespace Erdos4b.FGKMT

noncomputable section

open ArithmeticFunction
open scoped BigOperators

theorem preSieveBoundary_abs_of_squarefree_dvd {M n : ℕ}
    (hn : Squarefree n) (hnM : n ∣ M) : |preSieveBoundary M n| = 1 / (n : ℝ) := by
  rw [preSieveBoundary, squarefreePrimeWeight_apply_of_squarefree _ hn, Finset.abs_prod]
  calc
    _ = ∏ p ∈ n.primeFactors, 1 / (p : ℝ) := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [if_pos ((Nat.dvd_of_mem_primeFactors hp).trans hnM), abs_neg,
        abs_of_nonneg (by positivity : 0 ≤ 1 / (p : ℝ))]
    _ = 1 / (n : ℝ) := by
      simp only [one_div, Finset.prod_inv_distrib]
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hn]

theorem preSieveBoundary_eq_zero_of_not_dvd {M n : ℕ}
    (hM : M ≠ 0) (hnM : ¬n ∣ M) : preSieveBoundary M n = 0 := by
  by_cases hn : Squarefree n
  · have hnot : ¬n.primeFactors ⊆ M.primeFactors := by
      intro hsub
      apply hnM
      have hd := (Nat.prod_primeFactors_dvd_iff hM).mpr hsub
      rwa [Nat.prod_primeFactors_of_squarefree hn] at hd
    obtain ⟨p, hpn, hpM⟩ := Finset.not_subset.mp hnot
    have hpd : ¬p ∣ M := by
      intro hd
      exact hpM (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hpn, hd, hM⟩)
    rw [preSieveBoundary, squarefreePrimeWeight_apply_of_squarefree _ hn]
    exact Finset.prod_eq_zero hpn (if_neg hpd)
  · exact squarefreePrimeWeight_apply_of_not_squarefree _ hn

theorem preSieveBoundary_abs_apply {M : ℕ} (hM : M ≠ 0) (n : ℕ) :
    |preSieveBoundary M n| = if Squarefree n ∧ n ∣ M then 1 / (n : ℝ) else 0 := by
  by_cases hn : Squarefree n
  · by_cases hnM : n ∣ M
    · rw [if_pos ⟨hn, hnM⟩, preSieveBoundary_abs_of_squarefree_dvd hn hnM]
    · rw [if_neg (fun h => hnM h.2), preSieveBoundary_eq_zero_of_not_dvd hM hnM, abs_zero]
  · rw [if_neg (fun h => hn h.1)]
    change |squarefreePrimeWeight _ n| = 0
    rw [squarefreePrimeWeight_apply_of_not_squarefree _ hn, abs_zero]

def boundarySupport (M : ℕ) : Finset ℕ := M.divisors.filter Squarefree

theorem mem_boundarySupport {M n : ℕ} (hM : M ≠ 0) :
    n ∈ boundarySupport M ↔ Squarefree n ∧ n ∣ M := by
  rw [boundarySupport, Finset.mem_filter, Nat.mem_divisors]
  exact ⟨fun h => ⟨h.2, h.1.1⟩, fun h => ⟨⟨h.2, hM⟩, h.1⟩⟩

theorem preSieveBoundary_abs_tsum_eq {M : ℕ} (hM : M ≠ 0) :
    (∑' n, |preSieveBoundary M n|) = ∑ n ∈ boundarySupport M, 1 / (n : ℝ) := by
  rw [tsum_eq_sum (s := boundarySupport M) (fun n hn => by
    rw [preSieveBoundary_abs_apply hM, if_neg (fun h => hn ((mem_boundarySupport hM).mpr h))])]
  apply Finset.sum_congr rfl
  intro n hn
  exact preSieveBoundary_abs_of_squarefree_dvd ((mem_boundarySupport hM).mp hn).1
    ((mem_boundarySupport hM).mp hn).2

theorem preSieveBoundary_log_summable {M : ℕ} (hM : M ≠ 0) :
    Summable (fun n => |preSieveBoundary M n| * Real.log n) := by
  apply summable_of_ne_finset_zero (s := boundarySupport M)
  intro n hn
  rw [preSieveBoundary_abs_apply hM, if_neg (fun h => hn ((mem_boundarySupport hM).mpr h)),
    zero_mul]

theorem preSieveBoundary_log_tsum_eq {M : ℕ} (hM : M ≠ 0) :
    (∑' n, |preSieveBoundary M n| * Real.log n) =
      ∑ n ∈ boundarySupport M, Real.log n / (n : ℝ) := by
  rw [tsum_eq_sum (s := boundarySupport M) (fun n hn => by
    rw [preSieveBoundary_abs_apply hM, if_neg (fun h => hn ((mem_boundarySupport hM).mpr h)),
      zero_mul])]
  apply Finset.sum_congr rfl
  intro n hn
  rw [preSieveBoundary_abs_of_squarefree_dvd ((mem_boundarySupport hM).mp hn).1
    ((mem_boundarySupport hM).mp hn).2]
  ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.preSieveBoundary_log_tsum_eq
