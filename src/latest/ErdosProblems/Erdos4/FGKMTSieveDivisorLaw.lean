import ErdosProblems.Erdos4.FGKMTGoodDivisorProbability
import ErdosProblems.Erdos4.FGKMTSieveProfileParameters
import ErdosProblems.Erdos4.FGKMTHarmonicModulusSize

/-! The explicit profile family instantiated in the genuine finite divisor law. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open BoundedGaps.Maynard

noncomputable def sieveSlope (j R : ℕ) : ℝ := sieveProfileScale j / Real.log (R : ℝ)

theorem sieveSlope_pos {j R : ℕ} (hj : 1 ≤ j) (hR : 2 ≤ R) : 0 < sieveSlope j R := by
  exact div_pos (zero_lt_one.trans_le (sieveProfileScale_ge_one hj))
    (Real.log_pos (by exact_mod_cast hR))

theorem sieveSlope_mul_log {R : ℕ} (hR : 2 ≤ R) (j : ℕ) :
    sieveSlope j R * Real.log (R : ℝ) = sieveProfileScale j := by
  unfold sieveSlope
  exact div_mul_cancel₀ _ (Real.log_pos (by exact_mod_cast hR)).ne'

theorem sieveDivisorLaw_good_probability {j R D B : ℕ} (hj : 16 ≤ j) (hR : 2 ≤ R) (hD : 2 ≤ D)
    (hB : B = 1 ∨ B.Prime)
    (hcollision : 4 * sieveDimension j ^ 2 ≤ D - 1)
    (herror : harmonicTransferError (harmonicModulus D B) ≤
      coprimeHarmonicDensity (harmonicModulus D B) * Real.log (R : ℝ) /
        (2 * (1 + sieveProfileScale j))) :
    (1 / 2 : ℝ) ≤
      (FiniteLaw.independent (fun _ : Fin (sieveDimension j) =>
        rationalSquareLaw (harmonicModulus D B) (sieveSlope j R) R (by omega))).prob
          (fun a => (∑ i, Real.log (a i : ℕ)) ≤ Real.log (R : ℝ) / 2 ∧
            Pairwise (fun i l => (a i : ℕ).Coprime (a l : ℕ))) := by
  have hb := sieveSlope_pos (by omega : 1 ≤ j) hR
  have hlog : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast hR)
  apply rationalProduct_good_probability_half (Fin (sieveDimension j)) (harmonicModulus D B)
    hb (by omega) hD (fun p hp hpD => small_prime_dvd_harmonicModulus D B hp hpD) (by positivity)
  · simp only [Fintype.card_fin]
    apply rationalMass_moment_budget (harmonicModulus_pos D hB) (harmonicModulus_squarefree D hB) hR hb
    · rw [sieveSlope_mul_log hR]
      exact sieveProfileScale_ge_one (by omega)
    · simpa only [sieveSlope_mul_log hR] using herror
    · simpa only [sieveSlope_mul_log hR] using sieveProfileScale_moment_budget hj
  · simpa only [Fintype.card_fin] using hcollision

end Erdos4.FGKMT
