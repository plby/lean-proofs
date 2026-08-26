import ErdosProblems.Erdos421.LowerSieveDivisorSum
import ErdosProblems.Erdos421.SubpowerDivisorWindows
import ErdosProblems.Erdos421.PositiveDivisorWindows

/-! # Mean-square estimates for the actual upper and lower sieve windows -/

namespace Erdos421

open MeasureTheory Filter Topology

theorem canonicalUpper_window_mean (A : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ D z : ℕ, 0 < D →
      ((D ^ 2 : ℕ) : ℝ) ≤ (X : ℝ) ^ (21 / 40 : ℝ) →
      ∀ Y u v : ℝ, (X : ℝ) ^ (1 / 10 : ℝ) ≤ Y → u ≤ v → v - u ≤ X →
      (∫ x in u..v, ‖∑ m ∈ Finset.Icc 1 (D ^ 2), (canonicalUpperSieve D z m : ℂ) *
        (additiveDivisorWindow oneSidedSchwartzWindow Y x m - (m : ℂ)⁻¹)‖ ^ 2) ≤
          ε * X / (Real.log X) ^ A := by
  obtain ⟨C, hC, hb⟩ := uniform_upper_sieve_coefficient_growth
    (by norm_num : (0 : ℝ) < 1 / 100)
  filter_upwards [weighted_divisor_window_subpower_log_saving oneSidedSchwartzWindow hC A hε]
    with X hX
  intro D z hD hDX Y u v hY huv hlen
  have hcoef : ∀ m ∈ Finset.Icc 1 (D ^ 2), ‖(canonicalUpperSieve D z m : ℂ)‖ ≤
      C * (m : ℝ) ^ (1 / 100 : ℝ) := by
    intro m hm
    simpa only [canonicalUpperSieve, Complex.norm_real, Real.norm_eq_abs] using
      hb (primeProductBelow z) (primeProductBelow_squarefree z) D hD m (Finset.mem_Icc.mp hm).1
  have h := hX (Finset.Icc 1 (D ^ 2)) (fun m ↦ (canonicalUpperSieve D z m : ℂ)) (D ^ 2)
    (pow_pos hD _) hDX (fun m hm ↦ Finset.mem_Icc.mp hm) hcoef Y u v hY huv hlen
  simpa only [oneSidedSchwartzWindow_integral, mul_one] using h

theorem canonicalLower_window_mean (A : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ D z : ℕ, 0 < D → 0 < z →
      ((z * D ^ 2 : ℕ) : ℝ) ≤ (X : ℝ) ^ (21 / 40 : ℝ) →
      ∀ Y u v : ℝ, (X : ℝ) ^ (1 / 10 : ℝ) ≤ Y → u ≤ v → v - u ≤ X →
      (∫ x in u..v, ‖∑ m ∈ Finset.Icc 1 (z * D ^ 2), (lowerSieveCoefficient D z m : ℂ) *
        (additiveDivisorWindow oneSidedSchwartzWindow Y x m - (m : ℂ)⁻¹)‖ ^ 2) ≤
          ε * X / (Real.log X) ^ A := by
  obtain ⟨C, hC, hb⟩ := lowerSieveCoefficient_subpower
    (by norm_num : (0 : ℝ) < 1 / 100)
  filter_upwards [weighted_divisor_window_subpower_log_saving oneSidedSchwartzWindow hC A hε]
    with X hX
  intro D z hD hz hDX Y u v hY huv hlen
  have hcoef : ∀ m ∈ Finset.Icc 1 (z * D ^ 2), ‖(lowerSieveCoefficient D z m : ℂ)‖ ≤
      C * (m : ℝ) ^ (1 / 100 : ℝ) := by
    intro m hm
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hb D hD z m (Finset.mem_Icc.mp hm).1
  have h := hX (Finset.Icc 1 (z * D ^ 2)) (fun m ↦ (lowerSieveCoefficient D z m : ℂ)) (z * D ^ 2)
    (Nat.mul_pos hz (pow_pos hD _)) hDX (fun m hm ↦ Finset.mem_Icc.mp hm) hcoef Y u v hY huv hlen
  simpa only [oneSidedSchwartzWindow_integral, mul_one] using h

end Erdos421
