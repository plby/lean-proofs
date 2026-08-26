import ErdosProblems.Erdos421.UpperSieveCoefficientGrowth
import ErdosProblems.Erdos421.RoughEulerProduct

/-! # Canonical upper-sieve coefficients at a prime cutoff -/

namespace Erdos421

noncomputable def canonicalUpperSieve (D z : ℕ) : ℕ → ℝ :=
  BoundingSieve.lambdaSquared (selbergOptimizedWeight
    (uniformResidueSieve (primeProductBelow z) (primeProductBelow_squarefree z)) D)

noncomputable def canonicalUpperMain (D z : ℕ) : ℝ :=
  ∑ d ∈ (primeProductBelow z).divisors, canonicalUpperSieve D z d / (d : ℝ)

theorem canonicalUpperSieve_isUpper {D : ℕ} (hD : 1 ≤ D) (z : ℕ) :
    BoundingSieve.IsUpperMoebius (canonicalUpperSieve D z) :=
  selbergOptimized_upperMoebius _ hD

theorem canonicalUpperSieve_support {D z k : ℕ} (hk : D ^ 2 < k) :
    canonicalUpperSieve D z k = 0 := selbergLambdaSquared_eq_zero_of_gt _ hk

theorem canonicalUpperSieve_divisor_support (D z k : ℕ) (hk : ¬k ∣ primeProductBelow z) :
    canonicalUpperSieve D z k = 0 := selbergLambdaSquared_eq_zero_of_not_dvd _ D hk

theorem canonicalUpperMain_le_exp_error {D z : ℕ} (hD : 0 < D) (hz : 2 ≤ z)
    (herr : Real.exp (16 * Real.exp 1 - Real.log D / Real.log z) ≤ 1 / 2) :
    canonicalUpperMain D z ≤
      (1 + 2 * Real.exp (16 * Real.exp 1 - Real.log D / Real.log z)) * roughEulerProduct z := by
  let s := uniformResidueSieve (primeProductBelow z) (primeProductBelow_squarefree z)
  have hprimes : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) ≤ z := by
    intro p hp
    change p ∈ (primeProductBelow z).primeFactors at hp
    rw [primeFactors_primeProductBelow] at hp
    exact_mod_cast (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).2.le
  have hV : sieveEulerProduct s = roughEulerProduct z := by
    rw [uniformResidueSieve_euler, primeFactors_primeProductBelow]
    rfl
  have hmain : s.mainSum (BoundingSieve.lambdaSquared (selbergOptimizedWeight s D)) =
      canonicalUpperMain D z := by
    unfold canonicalUpperMain canonicalUpperSieve
    rfl
  have hepos := Real.exp_pos (16 * Real.exp 1 - Real.log D / Real.log z)
  have he1 : Real.exp (16 * Real.exp 1 - Real.log D / Real.log z) < 1 := by linarith
  have hb := selbergOptimized_mainTerm_le s (by exact_mod_cast hz) hprimes
    (fun p _ ↦ uniformResidueSieve_nu _ _ p) hD he1
  rw [hmain, hV] at hb
  apply hb.trans
  apply (div_le_iff₀ (sub_pos.mpr he1)).mpr
  have hvpos := roughEulerProduct_pos z
  have heq : 1 ≤ (1 + 2 * Real.exp (16 * Real.exp 1 - Real.log D / Real.log z)) *
      (1 - Real.exp (16 * Real.exp 1 - Real.log D / Real.log z)) := by nlinarith
  have hm := mul_le_mul_of_nonneg_left heq hvpos.le
  nlinarith

theorem canonicalUpperMain_le_level_error {D z : ℕ} (hD : 0 < D) (hz : 2 ≤ z)
    (hlevel : 16 * Real.exp 1 + 1 ≤ Real.log D / Real.log z) :
    canonicalUpperMain D z ≤
      (1 + 2 * Real.exp (16 * Real.exp 1 - Real.log D / Real.log z)) * roughEulerProduct z := by
  apply canonicalUpperMain_le_exp_error hD hz
  calc
    _ ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ 1 / 2 := by
      rw [Real.exp_neg, inv_eq_one_div]
      apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
      have h := Real.add_one_le_exp 1
      norm_num at h
      exact h

end Erdos421
