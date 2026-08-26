import ErdosProblems.Erdos67b.MRTResidueReindex

/-! # Averaging the exact residue reindexing, including every boundary term -/

open scoped BigOperators
open Finset

namespace Erdos67b

noncomputable section

theorem mrtSum_norm_residueShortSum_le_divisor_mean {blocks : Finset (ℕ × ℕ)}
    {d q b : ℕ} (hd : 0 < d) (hdq : d ∣ q) (hdb : d ∣ b)
    (hlarge : ∀ I ∈ blocks, ∀ p ∈ primesInBlock I, d < p)
    {f : ℕ → ℂ} (hmul : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ m, 0 < m → ‖f m‖ ≤ 1) (Z Y h : ℕ) {B : ℝ}
    (hmain : (∑ t ∈ Finset.Ioc (Y / d) (2 * (Y / d)),
      ‖mrtResidueShortSum blocks (Z / d) f t (h / d) (q / d) (b / d)‖) ≤ B) :
    (∑ n ∈ Finset.Ioc Y (2 * Y), ‖mrtResidueShortSum blocks Z f n h q b‖) ≤
      (d : ℝ) * (B + 2 * (h / d : ℕ)) + Y := by
  let G := fun t ↦ ‖mrtResidueShortSum blocks (Z / d) f t (h / d) (q / d) (b / d)‖
  have hG : ∀ t, 0 ≤ G t := fun _ ↦ norm_nonneg _
  have hends : ∀ t, G t ≤ (h / d : ℕ) := fun t ↦
    mrtNorm_residueShortSum_le blocks (Z / d) t (h / d) (q / d) (b / d) hbound
  calc
    _ ≤ ∑ n ∈ Finset.Ioc Y (2 * Y), (G (n / d) + 1) :=
      Finset.sum_le_sum fun n _ ↦
        mrtNorm_residueShortSum_divisor_le hd hdq hdb hlarge hmul hbound Z n h
    _ = (∑ n ∈ Finset.Ioc Y (2 * Y), G (n / d)) + Y := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, card_Ioc_self_two_mul, mul_one]
    _ ≤ _ := add_le_add (mrtSum_divided_starts_le_dyadic_add_boundary G hG Y hd
      hmain (hends _) (hends _)) (le_refl _)

theorem mrtDivisor_mean_budget_le (Y h : ℕ) {d : ℕ} {V : ℝ} (hV : 0 < V) :
    (d : ℝ) * (((h / d : ℕ) : ℝ) * (Y / d : ℕ) / V + 2 * (h / d : ℕ)) + Y ≤
      (h : ℝ) * Y / V + 2 * h + Y := by
  have hdh : (d : ℝ) * (h / d : ℕ) ≤ h := by
    exact_mod_cast (show d * (h / d) ≤ h by
      simpa only [mul_comm] using Nat.div_mul_le_self h d)
  have hNY : ((Y / d : ℕ) : ℝ) ≤ Y := by exact_mod_cast Nat.div_le_self Y d
  have hprod := mul_le_mul hdh hNY (Nat.cast_nonneg (Y / d)) (Nat.cast_nonneg h)
  have hdiv := div_le_div_of_nonneg_right hprod hV.le
  calc
    _ = ((d : ℝ) * (h / d : ℕ)) * (Y / d : ℕ) / V +
        2 * ((d : ℝ) * (h / d : ℕ)) + Y := by ring
    _ ≤ _ := add_le_add (add_le_add hdiv
      (mul_le_mul_of_nonneg_left hdh (by norm_num))) (le_refl _)

theorem mrtSum_norm_residueShortSum_le_divisor_power {blocks : Finset (ℕ × ℕ)}
    {d q b : ℕ} (hd : 0 < d) (hdq : d ∣ q) (hdb : d ∣ b)
    (hlarge : ∀ I ∈ blocks, ∀ p ∈ primesInBlock I, d < p)
    {f : ℕ → ℂ} (hmul : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ m, 0 < m → ‖f m‖ ≤ 1) (Z Y h : ℕ) {V : ℝ} (hV : 0 < V)
    (hmain : (∑ t ∈ Finset.Ioc (Y / d) (2 * (Y / d)),
      ‖mrtResidueShortSum blocks (Z / d) f t (h / d) (q / d) (b / d)‖) ≤
        ((h / d : ℕ) : ℝ) * (Y / d : ℕ) / V) :
    (∑ n ∈ Finset.Ioc Y (2 * Y), ‖mrtResidueShortSum blocks Z f n h q b‖) ≤
      (h : ℝ) * Y / V + 2 * h + Y := by
  exact (mrtSum_norm_residueShortSum_le_divisor_mean hd hdq hdb hlarge hmul hbound
    Z Y h hmain).trans (mrtDivisor_mean_budget_le Y h hV)

end

end Erdos67b
