import ErdosProblems.Erdos421.PrimeConvolutionSieve
import ErdosProblems.Erdos421.SieveWindowErrors

/-! # Actual upper and lower divisor sieves for the merged prime-cofactor weight -/

namespace Erdos421

theorem canonicalPrimeUpper_pointwise (P : Finset ℕ) {Q D : ℕ}
    (hP : ∀ p ∈ P, 0 < p ∧ p ≤ Q) (hD : 1 ≤ D) (z n : ℕ) :
    primeCofactorWeight P z n ≤ ∑ m ∈ Finset.Icc 1 (Q * D ^ 2),
      if m ∣ n then primeDivisorConvolution P (canonicalUpperSieve D z) m else 0 :=
  primeDivisorConvolution_upper P _ hP
    (fun _ hd ↦ canonicalUpperSieve_support hd) (canonicalUpperSieve_pointwise hD z) n

theorem canonicalPrimeLower_pointwise (P : Finset ℕ) {Q D z : ℕ}
    (hP : ∀ p ∈ P, 0 < p ∧ p ≤ Q) (hD : 1 ≤ D) (hz : 1 ≤ z) (n : ℕ) :
    (∑ m ∈ Finset.Icc 1 (Q * (z * D ^ 2)),
      if m ∣ n then primeDivisorConvolution P (lowerSieveCoefficient D z) m else 0) ≤
        primeCofactorWeight P z n :=
  primeDivisorConvolution_lower P _ hP
    (fun _ hd ↦ lowerSieveCoefficient_support hD hz hd)
    (lowerSieveCoefficient_pointwise hD hz) n

theorem canonicalPrimeUpper_main (P : Finset ℕ) {Q : ℕ}
    (hP : ∀ p ∈ P, 0 < p ∧ p ≤ Q) (D z : ℕ) :
    (∑ m ∈ Finset.Icc 1 (Q * D ^ 2),
      primeDivisorConvolution P (canonicalUpperSieve D z) m / (m : ℝ)) =
        (∑ p ∈ P, (p : ℝ)⁻¹) * canonicalUpperMain D z := by
  rw [primeDivisorConvolution_main P _ hP (fun _ hd ↦ canonicalUpperSieve_support hd),
    ← canonicalUpperMain_truncated]

theorem canonicalPrimeLower_main (P : Finset ℕ) {Q D z : ℕ}
    (hP : ∀ p ∈ P, 0 < p ∧ p ≤ Q) (hD : 1 ≤ D) (hz : 1 ≤ z) :
    (∑ m ∈ Finset.Icc 1 (Q * (z * D ^ 2)),
      primeDivisorConvolution P (lowerSieveCoefficient D z) m / (m : ℝ)) =
        (∑ p ∈ P, (p : ℝ)⁻¹) * canonicalLowerMain D z := by
  rw [primeDivisorConvolution_main P _ hP (fun _ hd ↦ lowerSieveCoefficient_support hD hz hd),
    lowerSieveCoefficient_main_sum hD hz]

end Erdos421
