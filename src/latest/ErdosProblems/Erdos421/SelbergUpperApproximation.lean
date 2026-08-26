import ErdosProblems.Erdos421.SelbergRankinExponent
import ErdosProblems.Erdos421.SelbergMainTerm

/-! # A quantitative upper-sieve main-term approximation -/

namespace Erdos421

theorem selbergOptimized_mainTerm_le (s : BoundingSieve) {z : ℝ} (hz : 2 ≤ z)
    (hprimes : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) ≤ z)
    (hν : ∀ p ∈ s.prodPrimes.primeFactors, s.nu p = (p : ℝ)⁻¹)
    {D : ℕ} (hD : 0 < D)
    (herr : Real.exp (16 * Real.exp 1 - Real.log D / Real.log z) < 1) :
    s.mainSum (BoundingSieve.lambdaSquared (selbergOptimizedWeight s D)) ≤
      sieveEulerProduct s / (1 - Real.exp (16 * Real.exp 1 - Real.log D / Real.log z)) := by
  have hV := sieveEulerProduct_pos s
  have hE := sub_pos.mpr herr
  have hG := selbergNormalizer_reciprocal_lower s hz hprimes hν hD
  rw [selbergOptimized_mainTerm s hD]
  calc
    _ ≤ 1 / ((sieveEulerProduct s)⁻¹ *
        (1 - Real.exp (16 * Real.exp 1 - Real.log D / Real.log z))) :=
      one_div_le_one_div_of_le (by positivity) hG
    _ = _ := by field_simp

theorem exp_rankin_error_le {z : ℝ} {D : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hlevel : 16 * Real.exp 1 + Real.log (2 / ε) ≤ Real.log D / Real.log z) :
    Real.exp (16 * Real.exp 1 - Real.log D / Real.log z) ≤ ε / 2 := by
  have hp : 0 < ε / 2 := by positivity
  have hlog : -Real.log (2 / ε) = Real.log (ε / 2) := by
    rw [Real.log_div (by norm_num) hε.ne', Real.log_div hε.ne' (by norm_num)]
    ring
  calc
    _ ≤ Real.exp (-Real.log (2 / ε)) := Real.exp_le_exp.mpr (by linarith)
    _ = ε / 2 := by rw [hlog, Real.exp_log hp]

theorem selbergOptimized_mainTerm_le_one_add (s : BoundingSieve) {z : ℝ} (hz : 2 ≤ z)
    (hprimes : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) ≤ z)
    (hν : ∀ p ∈ s.prodPrimes.primeFactors, s.nu p = (p : ℝ)⁻¹)
    {D : ℕ} (hD : 0 < D) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlevel : 16 * Real.exp 1 + Real.log (2 / ε) ≤ Real.log D / Real.log z) :
    s.mainSum (BoundingSieve.lambdaSquared (selbergOptimizedWeight s D)) ≤
      (1 + ε) * sieveEulerProduct s := by
  have hb := exp_rankin_error_le hε hlevel
  have herr : Real.exp (16 * Real.exp 1 - Real.log D / Real.log z) < 1 := by linarith
  have hV := (sieveEulerProduct_pos s).le
  apply (selbergOptimized_mainTerm_le s hz hprimes hν hD herr).trans
  apply (div_le_iff₀ (sub_pos.mpr herr)).mpr
  have hfactor : 1 ≤ (1 + ε) * (1 - Real.exp (16 * Real.exp 1 - Real.log D / Real.log z)) := by
    have he0 := (Real.exp_pos (16 * Real.exp 1 - Real.log D / Real.log z)).le
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hfactor hV
  nlinarith

end Erdos421
