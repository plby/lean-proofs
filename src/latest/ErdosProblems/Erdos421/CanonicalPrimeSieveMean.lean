import ErdosProblems.Erdos421.CanonicalPrimeSieve
import ErdosProblems.Erdos421.PrimeConvolutionGrowth

/-! # Type-I mean squares for the actual convolved upper and lower sieve coefficients -/

namespace Erdos421

open MeasureTheory Filter Topology

theorem canonicalPrimeUpper_window_mean {k : ℕ} (hk : 0 < k) (A : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ Q D z w : ℕ, 0 < Q → 0 < D → 0 < w →
      Q * D ^ 2 < w ^ k → ((Q * D ^ 2 : ℕ) : ℝ) ≤ (X : ℝ) ^ (21 / 40 : ℝ) →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ w ≤ p) →
      ∀ Y u v : ℝ, (X : ℝ) ^ (1 / 10 : ℝ) ≤ Y → u ≤ v → v - u ≤ X →
      (∫ x in u..v, ‖sieveWindowError (Q * D ^ 2)
        (primeDivisorConvolution P (canonicalUpperSieve D z)) Y x‖ ^ 2) ≤
          ε * X / (Real.log X) ^ A := by
  obtain ⟨C, hC, hb⟩ := uniform_upper_sieve_coefficient_growth
    (by norm_num : (0 : ℝ) < 1 / 100)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  filter_upwards [weighted_divisor_window_subpower_log_saving oneSidedSchwartzWindow
    (mul_pos hkR hC) A hε] with X hX
  intro Q D z w hQ hD hw hcut hlevel P hP Y u v hY huv hlen
  have hcoef : ∀ m ∈ Finset.Icc 1 (Q * D ^ 2),
      ‖(primeDivisorConvolution P (canonicalUpperSieve D z) m : ℂ)‖ ≤
        ((k : ℝ) * C) * (m : ℝ) ^ (1 / 100 : ℝ) := by
    intro m hm
    obtain ⟨hmpos, hmle⟩ := Finset.mem_Icc.mp hm
    rw [Complex.norm_real, Real.norm_eq_abs]
    apply primeDivisorConvolution_abs_le P _ hw hmpos (hmle.trans_lt hcut) hP hC.le
      (by norm_num : (0 : ℝ) ≤ 1 / 100)
    intro d hd
    simpa only [canonicalUpperSieve] using hb
      (primeProductBelow z) (primeProductBelow_squarefree z) D hD d hd
  have h := hX (Finset.Icc 1 (Q * D ^ 2))
    (fun m ↦ (primeDivisorConvolution P (canonicalUpperSieve D z) m : ℂ))
    (Q * D ^ 2) (Nat.mul_pos hQ (pow_pos hD _)) hlevel
    (fun m hm ↦ Finset.mem_Icc.mp hm) hcoef Y u v hY huv hlen
  simpa only [oneSidedSchwartzWindow_integral, mul_one, sieveWindowError] using h

theorem canonicalPrimeLower_window_mean {k : ℕ} (hk : 0 < k) (A : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ Q D z w : ℕ, 0 < Q → 0 < D → 0 < z → 0 < w →
      Q * (z * D ^ 2) < w ^ k →
      ((Q * (z * D ^ 2) : ℕ) : ℝ) ≤ (X : ℝ) ^ (21 / 40 : ℝ) →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ w ≤ p) →
      ∀ Y u v : ℝ, (X : ℝ) ^ (1 / 10 : ℝ) ≤ Y → u ≤ v → v - u ≤ X →
      (∫ x in u..v, ‖sieveWindowError (Q * (z * D ^ 2))
        (primeDivisorConvolution P (lowerSieveCoefficient D z)) Y x‖ ^ 2) ≤
          ε * X / (Real.log X) ^ A := by
  obtain ⟨C, hC, hb⟩ := lowerSieveCoefficient_subpower
    (by norm_num : (0 : ℝ) < 1 / 100)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  filter_upwards [weighted_divisor_window_subpower_log_saving oneSidedSchwartzWindow
    (mul_pos hkR hC) A hε] with X hX
  intro Q D z w hQ hD hz hw hcut hlevel P hP Y u v hY huv hlen
  have hcoef : ∀ m ∈ Finset.Icc 1 (Q * (z * D ^ 2)),
      ‖(primeDivisorConvolution P (lowerSieveCoefficient D z) m : ℂ)‖ ≤
        ((k : ℝ) * C) * (m : ℝ) ^ (1 / 100 : ℝ) := by
    intro m hm
    obtain ⟨hmpos, hmle⟩ := Finset.mem_Icc.mp hm
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact primeDivisorConvolution_abs_le P _ hw hmpos (hmle.trans_lt hcut) hP hC.le
      (by norm_num : (0 : ℝ) ≤ 1 / 100) (hb D hD z)
  have h := hX (Finset.Icc 1 (Q * (z * D ^ 2)))
    (fun m ↦ (primeDivisorConvolution P (lowerSieveCoefficient D z) m : ℂ))
    (Q * (z * D ^ 2)) (Nat.mul_pos hQ (Nat.mul_pos hz (pow_pos hD _))) hlevel
    (fun m hm ↦ Finset.mem_Icc.mp hm) hcoef Y u v hY huv hlen
  simpa only [oneSidedSchwartzWindow_integral, mul_one, sieveWindowError] using h

end Erdos421
