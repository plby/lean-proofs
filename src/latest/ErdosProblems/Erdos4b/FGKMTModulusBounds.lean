/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTBoundarySigned
import ErdosProblems.Erdos4b.GeneralFourierPrimeMass
import ErdosProblems.Erdos220.Mertens

/-!
# Logarithmic bounds for the pre-sieve modulus

These estimates reuse the proved prime-log Mertens bound from the
earlier Erdős 4 development and the finite Euler-product bounds from
Erdős 220. A split at the ceiling of `1 + log M` bounds both modulus
losses by a common positive logarithm-of-logarithm scale.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

def modulusPrimeLogMass (M : ℕ) : ℝ :=
  ∑ p ∈ M.primeFactors, Real.log p / (p : ℝ)

def modulusLogScale (M : ℕ) : ℝ := 1 + Real.log (4 + Real.log M)

theorem modulusPrimeLogMass_nonneg (M : ℕ) : 0 ≤ modulusPrimeLogMass M := by
  unfold modulusPrimeLogMass
  positivity

theorem one_le_modulusLogScale (M : ℕ) : 1 ≤ modulusLogScale M := by
  have hlog := Real.log_natCast_nonneg M
  have h := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 4 + Real.log M)
  unfold modulusLogScale
  linarith

theorem roughPrimeLogDivisorMass_zero_eq (M : ℕ) :
    roughPrimeLogDivisorMass M 0 = modulusPrimeLogMass M := by
  unfold roughPrimeLogDivisorMass modulusPrimeLogMass
  rw [Finset.filter_eq_self.mpr (fun p hp => Nat.pos_of_mem_primeFactors hp)]

theorem exists_modulusPrimeLogMass_le_logScale :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 0 < M →
      modulusPrimeLogMass M ≤ C * modulusLogScale M := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_roughPrimeLogDivisorMass_log_bound
  refine ⟨C + 2, by linarith, ?_⟩
  intro M hM
  have hlog := Real.log_natCast_nonneg M
  have h := hbound (P := M) (B := 1) (L := 1 + Real.log M) hM
    (by norm_num) (by linarith) (by linarith) 0
  rw [roughPrimeLogDivisorMass_zero_eq] at h
  have hmono : Real.log (1 + Real.log M + 1) ≤ Real.log (4 + Real.log M) :=
    Real.log_le_log (by linarith) (by linarith)
  have hscale := one_le_modulusLogScale M
  unfold modulusLogScale at hscale ⊢
  nlinarith [mul_nonneg hC (sub_nonneg.mpr hscale)]

theorem totientRatio_eq_inverse_primeFactors_product {M : ℕ} (hM : 0 < M) :
    (M : ℝ) / M.totient = ∏ p ∈ M.primeFactors, (1 - 1 / (p : ℝ))⁻¹ := by
  rw [Finset.prod_inv_distrib, primeFactors_totientProduct hM, inv_div]

theorem inverse_prime_factor_le_one_add_log {p : ℕ} (hp : p.Prime) :
    (1 - 1 / (p : ℝ))⁻¹ ≤ 1 + 4 * (Real.log p / (p : ℝ)) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hlogp : (1 : ℝ) / 2 ≤ Real.log p :=
    hlog2.trans (Real.log_le_log (by norm_num) hp2)
  have hrecip : 1 / ((p : ℝ) - 1) ≤ 2 / (p : ℝ) := by
    apply (div_le_div_iff₀ hp1 hp0).2
    nlinarith
  have hlogrecip : 2 / (p : ℝ) ≤ 4 * (Real.log p / (p : ℝ)) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith) hp0.le
  have hid : (1 - 1 / (p : ℝ))⁻¹ = 1 + 1 / ((p : ℝ) - 1) := by
    field_simp [hp0.ne', hp1.ne']
    ring
  rw [hid]
  linarith

theorem rough_inverse_primeFactors_product_le {M T : ℕ} (hM : 0 < M) (hT : 0 < T) :
    (∏ p ∈ M.primeFactors.filter (fun p => T < p), (1 - 1 / (p : ℝ))⁻¹) ≤
      Real.exp (4 * (Real.log M / T)) := by
  let S := M.primeFactors.filter (fun p => T < p)
  calc
    _ ≤ ∏ p ∈ S, (1 + 4 * (Real.log p / (p : ℝ))) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hpPrime := Nat.prime_of_mem_primeFactors (Finset.filter_subset _ _ hp)
        simpa only [one_div] using
          (show (0 : ℝ) ≤ (1 - (p : ℝ)⁻¹)⁻¹ from
            zero_le_one.trans (Erdos220.one_le_inverse_prime_factor hpPrime))
      · intro p hp
        exact inverse_prime_factor_le_one_add_log
          (Nat.prime_of_mem_primeFactors (Finset.filter_subset _ _ hp))
    _ ≤ Real.exp (∑ p ∈ S, 4 * (Real.log p / (p : ℝ))) :=
      Real.prod_one_add_le_exp_sum S (fun p => by positivity)
    _ ≤ Real.exp (4 * (Real.log M / T)) := by
      apply Real.exp_le_exp.mpr
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (roughPrimeLogDivisorMass_le_log_div hM hT)
        (by norm_num)

theorem small_inverse_primeFactors_product_le (M T : ℕ) :
    (∏ p ∈ M.primeFactors.filter (fun p => p ≤ T), (1 - 1 / (p : ℝ))⁻¹) ≤
      partial_euler_product T := by
  rw [partial_euler_product]
  simp only [one_div]
  apply Finset.prod_le_prod_of_subset_of_one_le
  · intro p hp
    obtain ⟨hpM, hpT⟩ := Finset.mem_filter.mp hp
    have hpPrime := Nat.prime_of_mem_primeFactors hpM
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpPrime.one_le, hpT⟩, hpPrime⟩
  · intro p hp
    exact zero_le_one.trans (Erdos220.one_le_inverse_prime_factor
      (Nat.prime_of_mem_primeFactors (Finset.filter_subset _ _ hp)))
  · intro p hp _
    exact Erdos220.one_le_inverse_prime_factor (Finset.mem_filter.mp hp).2

theorem totientRatio_le_partialEuler_mul_exp {M T : ℕ} (hM : 0 < M) (hT : 0 < T) :
    (M : ℝ) / M.totient ≤ partial_euler_product T *
      Real.exp (4 * (Real.log M / T)) := by
  rw [totientRatio_eq_inverse_primeFactors_product hM,
    ← Finset.prod_filter_mul_prod_filter_not M.primeFactors (fun p => p ≤ T)
      (fun p => (1 - 1 / (p : ℝ))⁻¹)]
  simp only [not_le]
  apply mul_le_mul (small_inverse_primeFactors_product_le M T)
    (rough_inverse_primeFactors_product_le hM hT)
  · apply Finset.prod_nonneg
    intro p hp
    simpa only [one_div] using
      zero_le_one.trans (Erdos220.one_le_inverse_prime_factor
        (Nat.prime_of_mem_primeFactors (Finset.filter_subset _ _ hp)))
  · exact zero_le_one.trans partial_euler_trivial_lower_bound

theorem exists_totientRatio_le_logScale :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 0 < M →
      (M : ℝ) / M.totient ≤ C * modulusLogScale M := by
  obtain ⟨C, hC, hpartial⟩ := Erdos220.partial_euler_product_le_log
  refine ⟨C * Real.exp 4, mul_pos hC (Real.exp_pos 4), ?_⟩
  intro M hM
  let T := Nat.ceil (1 + Real.log M)
  have hlog := Real.log_natCast_nonneg M
  have hLT : 1 + Real.log M ≤ (T : ℝ) := Nat.le_ceil _
  have hT1 : 1 ≤ T := by exact_mod_cast (show (1 : ℝ) ≤ T by linarith)
  have hTR : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hTupper : (T : ℝ) ≤ 1 + Real.log M + 1 :=
    (Nat.ceil_lt_add_one (by linarith : 0 ≤ 1 + Real.log M)).le
  have hlogT : Real.log ((T : ℝ) + 2) ≤ modulusLogScale M := by
    have hmono : Real.log ((T : ℝ) + 2) ≤ Real.log (4 + Real.log M) :=
      Real.log_le_log (by positivity) (by linarith)
    unfold modulusLogScale
    linarith
  have hquot : Real.log M / T ≤ 1 := (div_le_one hTR).2 (by linarith)
  calc
    _ ≤ partial_euler_product T * Real.exp (4 * (Real.log M / T)) :=
      totientRatio_le_partialEuler_mul_exp hM (by omega)
    _ ≤ (C * Real.log ((T : ℝ) + 2)) * Real.exp 4 := by
      apply mul_le_mul (hpartial T hT1) (Real.exp_le_exp.mpr (by linarith))
      · exact (Real.exp_pos _).le
      · exact mul_nonneg hC.le (Real.log_nonneg (by linarith))
    _ ≤ (C * modulusLogScale M) * Real.exp 4 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogT hC.le) (Real.exp_pos 4).le
    _ = _ := by ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_modulusPrimeLogMass_le_logScale
#print axioms Erdos4b.FGKMT.exists_totientRatio_le_logScale
