import ErdosProblems.Erdos67b.MRLemma14DyadicTail
import ErdosProblems.Erdos67b.MRTypicalShortBoundary

/-! # A finite short-interval budget at a fixed proportional frequency cutoff -/

open Finset MeasureTheory Set

namespace Erdos67b

noncomputable section

def mrShortIntervalTailCost (c : ℝ) : ℝ :=
  1024 * lemma14UniversalScaledHighConstant * (c⁻¹ + Real.pi / c ^ 2)

theorem mrShortIntervalTailCost_nonneg {c : ℝ} (hc : 0 < c) :
    0 ≤ mrShortIntervalTailCost c := by
  unfold mrShortIntervalTailCost
  exact mul_nonneg
    (mul_nonneg (by norm_num) lemma14UniversalScaledHighConstant_nonneg) (by positivity)

/-- The dyadic short-sum estimate after the exact scale cancellations. -/
theorem mrDyadicShortInterval_le_energy_meanTail
    (S : Finset ℕ) {f : ℕ → ℂ} (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {X H : ℕ} (hH : 0 < H) (hHX : H ≤ X) {c e : ℝ} (hc : 0 < c) (he : 0 ≤ e)
    (henergy : (∫ t in -(c * X)..(c * X),
      Complex.normSq (dyadicVerticalDirichletPolynomial S f X t)) ≤ e) :
    uncenteredShortIntervalMeanSquare (dyadicRestrictedCoefficient S f X) X H ≤
      4 * lemma14UniversalScaledLowConstant * e * (H : ℝ) ^ 2 * X +
      512 * lemma14UniversalScaledHighConstant * X * (c⁻¹ + Real.pi / c ^ 2) := by
  have hX : 0 < X := hH.trans_le hHX
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hXone : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hXp : (X : ℝ) + 1 ≤ 2 * X := by linarith
  have hL := lemma14UniversalScaledLowConstant_nonneg
  have hR := lemma14UniversalScaledHighConstant_nonneg
  have hbase := normalized_uncenteredShortIntervalMeanSquare_le_scaled_low_add_meanTail
    S hf hX hH hHX (mul_pos hc hXR)
  have hcentral := mul_le_mul_of_nonneg_left henergy
    (show 0 ≤ 2 * lemma14UniversalScaledLowConstant * ((X : ℝ) + 1) by positivity)
  have hcentral' :
      2 * lemma14UniversalScaledLowConstant * ((X : ℝ) + 1) * e ≤
        4 * lemma14UniversalScaledLowConstant * e * X := by
    calc
      _ ≤ 2 * lemma14UniversalScaledLowConstant * (2 * X) * e := by gcongr
      _ = _ := by ring
  have hscaled := (div_le_iff₀ (sq_pos_of_pos hHR)).1
    (hbase.trans (add_le_add (hcentral.trans hcentral') (le_refl _)))
  have hnormalize :
      (4 * lemma14UniversalScaledLowConstant * e * X +
        4 * (lemma14UniversalScaledHighConstant * ((X : ℝ) + 1) ^ 3 / (H : ℝ) ^ 2) *
          (16 / ((X : ℝ) * (c * X)) + 16 * Real.pi / (c * X) ^ 2)) * (H : ℝ) ^ 2 =
      4 * lemma14UniversalScaledLowConstant * e * (H : ℝ) ^ 2 * X +
        64 * lemma14UniversalScaledHighConstant * ((X : ℝ) + 1) ^ 3 *
          (1 / ((X : ℝ) * (c * X)) + Real.pi / (c * X) ^ 2) := by
    field_simp [hHR.ne']
    ring
  rw [hnormalize] at hscaled
  have htail : 64 * lemma14UniversalScaledHighConstant * ((X : ℝ) + 1) ^ 3 *
      (1 / ((X : ℝ) * (c * X)) + Real.pi / (c * X) ^ 2) ≤
        512 * lemma14UniversalScaledHighConstant * X * (c⁻¹ + Real.pi / c ^ 2) := by
    calc
      _ ≤ 64 * lemma14UniversalScaledHighConstant * (2 * (X : ℝ)) ^ 3 *
          (1 / ((X : ℝ) * (c * X)) + Real.pi / (c * X) ^ 2) := by gcongr
      _ = _ := by field_simp [hc.ne', hXR.ne']; ring
  exact hscaled.trans (add_le_add (le_refl _) htail)

/-- All short-sum errors, on one actual typical family and one ambient scale. -/
theorem mrShortInterval_le_typical_energy_density
    (blocks : Finset (ℕ × ℕ)) {f : ℕ → ℂ} (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {X H : ℕ} (hH : 0 < H) (hHX : H ≤ X) {c e d : ℝ} (hc : 0 < c) (he : 0 ≤ e)
    (henergy : (∫ t in -(c * X)..(c * X), ‖mrTypicalDyadicPolynomial blocks f X t‖ ^ 2) ≤ e)
    (hdensity : ((atypicalFactorizationSet blocks (2 * X + H)).card : ℝ) ≤ d * X) :
    uncenteredShortIntervalMeanSquare f X H ≤
      (8 * lemma14UniversalScaledLowConstant * e + 2 * d) * (H : ℝ) ^ 2 * X +
        mrShortIntervalTailCost c * X + 2 * (H : ℝ) ^ 3 := by
  let S := typicalFactorizationSet blocks (2 * X + H)
  have hE : (∫ t in -(c * X)..(c * X),
      Complex.normSq (dyadicVerticalDirichletPolynomial S f X t)) ≤ e := by
    rw [integral_dyadicVerticalDirichletPolynomial_typical_eq blocks f (by omega)]
    exact henergy
  have hshort := mrDyadicShortInterval_le_energy_meanTail S hf hH hHX hc he hE
  have hfull := uncenteredShortIntervalMeanSquare_le_dyadic_typical_add_errors blocks hf X H
  have hbad := mul_le_mul_of_nonneg_left hdensity (show 0 ≤ 2 * (H : ℝ) ^ 2 by positivity)
  unfold mrShortIntervalTailCost
  dsimp only [S] at hshort
  nlinarith

end

end Erdos67b
