import ErdosProblems.Erdos239.External.Erdos67.MRGranvilleSoundararajanHR
import ErdosProblems.Erdos239.External.Erdos67.MRRealMeanStabilityReduction

/-!
# Finite Granville--Soundararajan prefix variation

This file proves the exact convolution-and-floor step behind the
Granville--Soundararajan slow-variation argument. For `g = f * μ`, a normalized
prefix mean is a finite sum of `g(d) * ⌊N/d⌋/N`. Comparing two prefix lengths
therefore costs at most `2/X` times the ordinary partial sum of `|g|`. The final
theorem composes this identity with the existing proved Halberstam--Richert
estimate.
-/

open scoped BigOperators ArithmeticFunction.Moebius
open Finset

namespace Erdos67

noncomputable section

theorem abs_natCast_div_ratio_sub_inv_le
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d) :
    |((((N / d : ℕ) : ℝ) / (N : ℝ)) - 1 / (d : ℝ))| ≤
      1 / (N : ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hfloor : (((N / d : ℕ) : ℝ)) ≤ (N : ℝ) / (d : ℝ) :=
    Nat.cast_div_le
  have hupper : (((N / d : ℕ) : ℝ) / (N : ℝ)) ≤ 1 / (d : ℝ) := by
    rw [div_le_iff₀ hNR]
    simpa [div_eq_mul_inv, mul_comm] using hfloor
  have hnatlt : N < (N / d + 1) * d := by
    exact (Nat.div_lt_iff_lt_mul hd).mp (by omega)
  have hreal_lt : (N : ℝ) < (((N / d + 1) * d : ℕ) : ℝ) := by
    exact_mod_cast hnatlt
  have hlower : 1 / (d : ℝ) - 1 / (N : ℝ) ≤
      (((N / d : ℕ) : ℝ) / (N : ℝ)) := by
    have : 1 / (d : ℝ) <
        (((N / d : ℕ) : ℝ) / (N : ℝ)) + 1 / (N : ℝ) := by
      rw [div_lt_iff₀ hdR]
      field_simp [ne_of_gt hNR]
      push_cast at hreal_lt ⊢
      exact hreal_lt
    linarith
  rw [abs_of_nonpos (sub_nonpos.mpr hupper)]
  linarith

noncomputable def gsFloorRatio (N d : ℕ) : ℂ :=
  ((N / d : ℕ) : ℂ) / (N : ℂ)

theorem norm_gsFloorRatio_sub_inv_le
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d) :
    ‖gsFloorRatio N d - ((d : ℂ)⁻¹)‖ ≤ 1 / (N : ℝ) := by
  have h := abs_natCast_div_ratio_sub_inv_le hN hd
  have heq : gsFloorRatio N d - ((d : ℂ)⁻¹) =
      ((((N / d : ℕ) : ℝ) / (N : ℝ) - 1 / (d : ℝ) : ℝ) : ℂ) := by
    simp only [gsFloorRatio, div_eq_mul_inv]
    push_cast
    simp
  rw [heq]
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact h

theorem norm_gsFloorRatio_sub_le_two_div
    {X Z d : ℕ} (hX : 0 < X) (hXZ : X ≤ Z) (hd : 0 < d) :
    ‖gsFloorRatio Z d - gsFloorRatio X d‖ ≤ 2 / (X : ℝ) := by
  have hZ : 0 < Z := hX.trans_le hXZ
  have hZX : (1 : ℝ) / Z ≤ 1 / X := by
    apply one_div_le_one_div_of_le
    · exact_mod_cast hX
    · exact_mod_cast hXZ
  calc
    ‖gsFloorRatio Z d - gsFloorRatio X d‖ =
        ‖(gsFloorRatio Z d - (d : ℂ)⁻¹) -
          (gsFloorRatio X d - (d : ℂ)⁻¹)‖ := by ring_nf
    _ ≤ ‖gsFloorRatio Z d - (d : ℂ)⁻¹‖ +
        ‖gsFloorRatio X d - (d : ℂ)⁻¹‖ := norm_sub_le _ _
    _ ≤ 1 / (Z : ℝ) + 1 / (X : ℝ) :=
      add_le_add (norm_gsFloorRatio_sub_inv_le hZ hd)
        (norm_gsFloorRatio_sub_inv_le hX hd)
    _ ≤ 1 / (X : ℝ) + 1 / (X : ℝ) := add_le_add hZX le_rfl
    _ = 2 / (X : ℝ) := by ring

theorem positivePrefixSum_eq_sum_Ioc_gsMoebius_mul_div
    (f : ℕ → ℂ) (N : ℕ) :
    positivePrefixSum f N =
      ∑ d ∈ Finset.Ioc 0 N,
        gsMoebiusCoefficient f d * ((N / d : ℕ) : ℂ) := by
  have hprefix :
      positivePrefixSum f N = ∑ n ∈ Finset.Ioc 0 N, f n := by
    have h := sum_Ioc_eq_positivePrefixSum_sub f (Nat.zero_le N)
    simpa [positivePrefixSum] using h.symm
  rw [hprefix]
  calc
    (∑ n ∈ Finset.Ioc 0 N, f n) =
        ∑ n ∈ Finset.Ioc 0 N,
          ∑ d ∈ n.divisors, gsMoebiusCoefficient f d := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn0 : n ≠ 0 := ne_of_gt (Finset.mem_Ioc.mp hn).1
      calc
        f n = positiveArithmeticFunction f n :=
          (positiveArithmeticFunction_apply hn0).symm
        _ = (gsMoebiusCoefficient f *
            (ArithmeticFunction.zeta : ArithmeticFunction ℂ)) n := by
              rw [gsMoebiusCoefficient_mul_zeta]
        _ = ∑ d ∈ n.divisors, gsMoebiusCoefficient f d := by
              rw [ArithmeticFunction.coe_mul_zeta_apply]
    _ = ∑ n ∈ Finset.Ioc 0 N,
          ∑ d ∈ (Finset.Ioc 0 N).filter (fun d ↦ d ∣ n),
            gsMoebiusCoefficient f d := by
      apply Finset.sum_congr rfl
      intro n hn
      refine Finset.sum_congr ?_ ?_
      · ext d
        simp only [Finset.mem_filter, Finset.mem_Ioc]
        have hnpos : 0 < n := (Finset.mem_Ioc.mp hn).1
        have hnN : n ≤ N := (Finset.mem_Ioc.mp hn).2
        have hn0 : n ≠ 0 := ne_of_gt hnpos
        constructor
        · intro hd
          have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
          have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hnpos
          exact ⟨⟨hdpos, (Nat.le_of_dvd hnpos hdvd).trans hnN⟩, hdvd⟩
        · rintro ⟨⟨_hdpos, _hdN⟩, hdvd⟩
          exact Nat.mem_divisors.mpr ⟨hdvd, hn0⟩
      · intro d _hd
        rfl
    _ = ∑ d ∈ Finset.Ioc 0 N,
          ∑ n ∈ (Finset.Ioc 0 N).filter (fun n ↦ d ∣ n),
            gsMoebiusCoefficient f d := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
    _ = ∑ d ∈ Finset.Ioc 0 N,
        gsMoebiusCoefficient f d * ((N / d : ℕ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro d _hd
      rw [Finset.sum_const]
      rw [Nat.Ioc_filter_dvd_card_eq_div]
      ring

theorem positivePrefixMean_eq_sum_Ioc_gsMoebius_mul_floorRatio
    (f : ℕ → ℂ) {N : ℕ} (_hN : 0 < N) :
    positivePrefixMean f N =
      ∑ d ∈ Finset.Ioc 0 N,
        gsMoebiusCoefficient f d * gsFloorRatio N d := by
  rw [positivePrefixMean, positivePrefixSum_eq_sum_Ioc_gsMoebius_mul_div]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d _hd
  simp only [gsFloorRatio]
  ring

theorem sum_Ioc_gsMoebius_mul_floorRatio_extend
    (f : ℕ → ℂ) {X Z : ℕ} (hXZ : X ≤ Z) :
    (∑ d ∈ Finset.Ioc 0 X,
        gsMoebiusCoefficient f d * gsFloorRatio X d) =
      ∑ d ∈ Finset.Ioc 0 Z,
        gsMoebiusCoefficient f d * gsFloorRatio X d := by
  apply Finset.sum_subset (Finset.Ioc_subset_Ioc_right hXZ)
  intro d hdZ hdX
  have hdpos : 0 < d := (Finset.mem_Ioc.mp hdZ).1
  have hXd : X < d := by
    by_contra h
    exact hdX (Finset.mem_Ioc.mpr ⟨hdpos, le_of_not_gt h⟩)
  simp [gsFloorRatio, Nat.div_eq_of_lt hXd]

theorem norm_positivePrefixMean_sub_le_gsMoebius_partialSum
    (f : ℕ → ℂ) {X Z : ℕ} (hX : 0 < X) (hXZ : X ≤ Z) :
    ‖positivePrefixMean f Z - positivePrefixMean f X‖ ≤
      (2 / (X : ℝ)) *
        HalberstamScratch.partialSum (gsMoebiusNorm f) Z := by
  have hZ : 0 < Z := hX.trans_le hXZ
  rw [positivePrefixMean_eq_sum_Ioc_gsMoebius_mul_floorRatio f hZ,
    positivePrefixMean_eq_sum_Ioc_gsMoebius_mul_floorRatio f hX,
    sum_Ioc_gsMoebius_mul_floorRatio_extend f hXZ]
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ d ∈ Finset.Ioc 0 Z,
        (gsMoebiusCoefficient f d * gsFloorRatio Z d -
          gsMoebiusCoefficient f d * gsFloorRatio X d)‖ ≤
        ∑ d ∈ Finset.Ioc 0 Z,
          ‖gsMoebiusCoefficient f d * gsFloorRatio Z d -
            gsMoebiusCoefficient f d * gsFloorRatio X d‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Ioc 0 Z,
        gsMoebiusNorm f d * (2 / (X : ℝ)) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdpos : 0 < d := (Finset.mem_Ioc.mp hd).1
      rw [← mul_sub, norm_mul]
      exact mul_le_mul_of_nonneg_left
        (norm_gsFloorRatio_sub_le_two_div hX hXZ hdpos) (norm_nonneg _)
    _ = (2 / (X : ℝ)) *
        HalberstamScratch.partialSum (gsMoebiusNorm f) Z := by
      unfold HalberstamScratch.partialSum
      have hsets : Finset.Ioc 0 Z = Finset.Icc 1 Z := by
        ext d
        simp only [Finset.mem_Ioc, Finset.mem_Icc]
        omega
      rw [hsets]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _hd
      ring

theorem norm_positivePrefixMean_sub_le_gsEulerExponent
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hone : ∀ n : ℕ, ‖f n‖ ≤ 1)
    {X Z : ℕ} (hX : 0 < X) (hXZ : X ≤ Z) (hZtwo : 2 ≤ Z) :
    ‖positivePrefixMean f Z - positivePrefixMean f X‖ ≤
      (2 / (X : ℝ)) *
        ((HalberstamScratch.explicitMassConstant 2 1 + 1) *
          (Z : ℝ) / Real.log (Z : ℝ) * Real.exp (gsEulerExponent f Z)) := by
  calc
    ‖positivePrefixMean f Z - positivePrefixMean f X‖ ≤
        (2 / (X : ℝ)) *
          HalberstamScratch.partialSum (gsMoebiusNorm f) Z :=
      norm_positivePrefixMean_sub_le_gsMoebius_partialSum f hX hXZ
    _ ≤ (2 / (X : ℝ)) *
        ((HalberstamScratch.explicitMassConstant 2 1 + 1) *
          (Z : ℝ) / Real.log (Z : ℝ) * Real.exp (gsEulerExponent f Z)) := by
      exact mul_le_mul_of_nonneg_left
        (gsMoebiusNorm_partialSum_le_exp hmul hone Z hZtwo) (by positivity)

end

end Erdos67
