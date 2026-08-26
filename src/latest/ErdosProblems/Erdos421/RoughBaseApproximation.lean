import ErdosProblems.Erdos421.PrimeIntervalAsymptotic
import ErdosProblems.Erdos421.InverseLogInterval
import ErdosProblems.Erdos421.RoughClippedBase
import ErdosProblems.Erdos421.FiniteBuchstabFunction

/-! # The actual rough-number base approximation, including cutoff clipping -/

namespace Erdos421

open MeasureTheory

theorem rough_base_main_identity {b : ℝ} {z : ℕ} (hz : 2 ≤ z) (hzb : (z : ℝ) ≤ b)
    (Y : ℝ) :
    Y / Real.log z * finiteBuchstab 0 (Real.log b / Real.log z) = Y / Real.log b := by
  have hzp : (0 : ℝ) < z := by exact_mod_cast (by omega : 0 < z)
  have hlz : 0 < Real.log z := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  have hlb : 0 < Real.log b := hlz.trans_le (Real.log_le_log hzp hzb)
  have hs : 1 ≤ Real.log b / Real.log z :=
    (le_div_iff₀ hlz).mpr (by simpa only [one_mul] using Real.log_le_log hzp hzb)
  rw [finiteBuchstab, max_eq_right hs]
  field_simp

theorem rough_base_interval_approximation {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ X₀ > 1, ∀ a b : ℝ, X₀ ≤ a → a ≤ b → ∀ z : ℕ, 2 ≤ z → (z : ℝ) ≤ b →
      b ≤ (z : ℝ) ^ 2 →
      |((roughInRealInterval a b z).card : ℝ) -
        (b - max a z) / Real.log z * finiteBuchstab 0 (Real.log b / Real.log z)| ≤
        2 + ε * b / (Real.log a) ^ A + (b - a) ^ 2 / (a * (Real.log a) ^ 2) := by
  obtain ⟨X₀, hX₀, hprime⟩ := prime_interval_logarithmic_integral hA hε
  refine ⟨X₀, hX₀, ?_⟩
  intro a b ha hab z hz hzb hbz
  have ha1 : 1 < a := hX₀.trans_le ha
  have hap : 0 < a := by linarith
  have hbp : 0 < b := hap.trans_le hab
  have hlap := Real.log_pos ha1
  let c : ℝ := max a z
  have hac : a ≤ c := le_max_left _ _
  have hcb : c ≤ b := max_le hab hzb
  have hc1 : 1 < c := ha1.trans_le hac
  have hlcp := Real.log_pos hc1
  have hlogac := Real.log_le_log hap hac
  have hp := hprime c b (ha.trans hac) hcb
  have hp' : |((primesInRealInterval c b).card : ℝ) - (∫ t in c..b, (Real.log t)⁻¹)| ≤
      ε * b / (Real.log a) ^ A := hp.trans
    (div_le_div_of_nonneg_left (mul_nonneg hε.le hbp.le) (Real.rpow_pos_of_pos hlap A)
      (Real.rpow_le_rpow hlap.le hlogac hA))
  have hi := inverse_log_integral_freeze hc1 hcb
  have hi' : |(∫ t in c..b, (Real.log t)⁻¹) - (b - c) / Real.log b| ≤
      (b - a) ^ 2 / (a * (Real.log a) ^ 2) := by
    apply hi.trans
    gcongr
  have hr := rough_real_interval_clipped_prime_error ha1.le hab hzb hbz
  rw [rough_base_main_identity hz hzb]
  change |((roughInRealInterval a b z).card : ℝ) - (b - c) / Real.log b| ≤ _
  calc
    _ = |(((roughInRealInterval a b z).card : ℝ) - (primesInRealInterval c b).card) +
        (((primesInRealInterval c b).card : ℝ) - (∫ t in c..b, (Real.log t)⁻¹)) +
        ((∫ t in c..b, (Real.log t)⁻¹) - (b - c) / Real.log b)| := by congr 1; ring
    _ ≤ |((roughInRealInterval a b z).card : ℝ) - (primesInRealInterval c b).card| +
        |((primesInRealInterval c b).card : ℝ) - (∫ t in c..b, (Real.log t)⁻¹)| +
        |(∫ t in c..b, (Real.log t)⁻¹) - (b - c) / Real.log b| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add hr hp') hi'

end Erdos421
