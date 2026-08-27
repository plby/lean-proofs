/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTBoundaryFactor
import ErdosProblems.Erdos4b.FGKMTEulerMajorant
import Mathlib.Data.Nat.Totient

/-!
# Absolute mass of the finite pre-sieve factor

The boundary factor contributes at most `M / φ M`. This estimate keeps
the actual modulus dependence explicit; it is not absorbed into a
constant depending on the growing sieve dimension.
-/

namespace Erdos4b.FGKMT

noncomputable section

open ArithmeticFunction
open scoped BigOperators

def boundaryAbsoluteMass (M : ℕ) : ℝ :=
  ∏ p ∈ M.primeFactors, (1 + 1 / (p : ℝ))

theorem preSieveBoundary_isMultiplicative (M : ℕ) :
    (preSieveBoundary M).IsMultiplicative := squarefreePrimeWeight_isMultiplicative _

theorem preSieveBoundary_prime (M : ℕ) {p : ℕ} (hp : p.Prime) :
    preSieveBoundary M p = if p ∣ M then -(1 / (p : ℝ)) else 0 :=
  squarefreePrimeWeight_prime _ hp

theorem preSieveBoundary_prime_pow_ge_two (M : ℕ) {p j : ℕ}
    (hp : p.Prime) (hj : 2 ≤ j) : preSieveBoundary M (p ^ j) = 0 :=
  squarefreePrimeWeight_prime_pow_ge_two _ hp hj

theorem preSieveBoundary_abs_local_tsum (M : ℕ) {p : ℕ} (hp : p.Prime) :
    (∑' j, |preSieveBoundary M (p ^ j)|) =
      if p ∣ M then 1 + 1 / (p : ℝ) else 1 := by
  rw [tsum_eq_sum (s := Finset.range 2) (fun j hj => by
    have hj2 : 2 ≤ j := by simpa only [Finset.mem_range, not_lt] using hj
    rw [preSieveBoundary_prime_pow_ge_two M hp hj2, abs_zero])]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add]
  rw [(preSieveBoundary_isMultiplicative M).map_one, abs_one, preSieveBoundary_prime M hp]
  by_cases hpM : p ∣ M
  · rw [if_pos hpM, if_pos hpM, abs_neg, abs_of_nonneg (by positivity : 0 ≤ 1 / (p : ℝ))]
  · simp only [if_neg hpM, abs_zero, add_zero]

theorem preSieveBoundary_absolute_sum_bound {M : ℕ} (hM : M ≠ 0) :
    Summable (fun n => |preSieveBoundary M n|) ∧
      (∑' n, |preSieveBoundary M n|) ≤ boundaryAbsoluteMass M := by
  have hf := preSieveBoundary_isMultiplicative M
  apply summable_and_tsum_le_of_local_products (fun n => |preSieveBoundary M n|)
    (by simp) (by rw [hf.map_one, abs_one]) (fun n => abs_nonneg _)
  · intro m n hmn
    rw [hf.map_mul_of_coprime hmn, abs_mul]
  · intro p hp
    apply summable_of_ne_finset_zero (s := Finset.range 2)
    intro j hj
    have hj2 : 2 ≤ j := by simpa only [Finset.mem_range, not_lt] using hj
    rw [preSieveBoundary_prime_pow_ge_two M hp hj2, abs_zero, norm_zero]
  · intro N
    calc
      (∏ p ∈ N.primesBelow, ∑' j, |preSieveBoundary M (p ^ j)|) =
          ∏ p ∈ N.primesBelow, (if p ∣ M then 1 + 1 / (p : ℝ) else 1) := by
        apply Finset.prod_congr rfl
        intro p hp
        exact preSieveBoundary_abs_local_tsum M (Nat.prime_of_mem_primesBelow hp)
      _ = ∏ p ∈ N.primesBelow.filter (fun p => p ∣ M), (1 + 1 / (p : ℝ)) := by
        rw [Finset.prod_filter]
      _ ≤ boundaryAbsoluteMass M := by
        apply Finset.prod_le_prod_of_subset_of_one_le
        · intro p hp
          obtain ⟨hpN, hpM⟩ := Finset.mem_filter.mp hp
          exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primesBelow hpN, hpM, hM⟩
        · intro p _
          positivity
        · intro p _ _
          have hp0 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
          linarith

theorem boundaryAbsoluteMass_le_totientRatio {M : ℕ} (hM : 0 < M) :
    boundaryAbsoluteMass M ≤ (M : ℝ) / M.totient := by
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hphi : (M.totient : ℝ) =
      (M : ℝ) * ∏ p ∈ M.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) (Nat.totient_eq_mul_prod_factors M)
    push_cast at h
    exact h
  have hpos : ∀ p ∈ M.primeFactors, (0 : ℝ) < 1 - (p : ℝ)⁻¹ := by
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    rw [sub_pos, inv_lt_one₀ (by linarith : (0 : ℝ) < p)]
    exact hp1
  have hprodpos : (0 : ℝ) < ∏ p ∈ M.primeFactors, (1 - (p : ℝ)⁻¹) :=
    Finset.prod_pos hpos
  calc
    boundaryAbsoluteMass M ≤ ∏ p ∈ M.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹ := by
      apply Finset.prod_le_prod
      · intro p _
        positivity
      · intro p hp
        rw [← one_div (1 - (p : ℝ)⁻¹), le_div_iff₀ (hpos p hp)]
        simp only [one_div]
        nlinarith [sq_nonneg ((p : ℝ)⁻¹)]
    _ = (∏ p ∈ M.primeFactors, (1 - (p : ℝ)⁻¹))⁻¹ :=
      Finset.prod_inv_distrib _
    _ = (M : ℝ) / M.totient := by
      rw [hphi]
      field_simp [hM0, hprodpos.ne']

theorem preSieveBoundary_abs_tsum_le_totientRatio {M : ℕ} (hM : 0 < M) :
    (∑' n, |preSieveBoundary M n|) ≤ (M : ℝ) / M.totient :=
  (preSieveBoundary_absolute_sum_bound hM.ne').2.trans (boundaryAbsoluteMass_le_totientRatio hM)

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.preSieveBoundary_abs_tsum_le_totientRatio
