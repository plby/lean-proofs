import ErdosProblems.Erdos964.Basic

/-!
# A positive integral certificate for a linear sieve weight

This file proves the analytic calculation for the candidate radial weight
`F(s) = 7 - 6s`. Relating these integrals to the arithmetic sieve sums is a
separate, still-unproved step; the certificate alone does not prove GPY.
-/

namespace Erdos964

open MeasureTheory

def linearSieveWeight (s : ℝ) : ℝ := 7 - 6 * s

noncomputable def linearSieveMass : ℝ :=
  ∫ s in (0 : ℝ)..1, s ^ 2 / 2 * linearSieveWeight s ^ 2

/-- The face integral, split where the small-prime cutoff meets the simplex
boundary. The inner integrals of `F` have already been written explicitly. -/
noncomputable def truncatedSieveFace (z : ℝ) : ℝ :=
  (∫ v in (0 : ℝ)..(1 - z), v * ((7 - 6 * v) * z - 3 * z ^ 2) ^ 2) +
    ∫ v in (1 - z)..1,
      v * ((7 - 6 * v) * (1 - v) - 3 * (1 - v) ^ 2) ^ 2

/-- The face divided by its cutoff. This polynomial extends continuously to
zero and makes nonnegativity on the unit interval explicit. -/
noncomputable def sieveFaceKernel (z : ℝ) : ℝ :=
  z / 60 * (41 + 82 * (1 - z) + 123 * (1 - z) ^ 2 + 84 * (1 - z) ^ 3)

noncomputable def linearSemiprimeIntegral : ℝ :=
  ∫ z in (0 : ℝ)..1, sieveFaceKernel z / (1 - z / 4)

theorem linearSieveMass_eq : linearSieveMass = 19 / 15 := by
  have hpoly : (fun s : ℝ => s ^ 2 / 2 * linearSieveWeight s ^ 2) =
      (fun s => (49 / 2 : ℝ) * s ^ 2 - 42 * s ^ 3 + 18 * s ^ 4) := by
    funext s
    dsimp [linearSieveWeight]
    ring
  rw [linearSieveMass, hpoly]
  simp (disch := (apply Continuous.intervalIntegrable; fun_prop)) only
    [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, integral_pow]
  norm_num

theorem truncatedSieveFace_eq (z : ℝ) :
    truncatedSieveFace z = z * sieveFaceKernel z := by
  have hfirst : (fun v : ℝ => v * ((7 - 6 * v) * z - 3 * z ^ 2) ^ 2) =
      (fun v => 36 * z ^ 2 * v ^ 3 + (36 * z ^ 3 - 84 * z ^ 2) * v ^ 2 +
        (9 * z ^ 4 - 42 * z ^ 3 + 49 * z ^ 2) * v ^ 1) := by
    funext v
    ring
  have hsecond : (fun v : ℝ =>
      v * ((7 - 6 * v) * (1 - v) - 3 * (1 - v) ^ 2) ^ 2) =
      (fun v => 9 * v ^ 5 - 42 * v ^ 4 + 73 * v ^ 3 - 56 * v ^ 2 + 16 * v ^ 1) := by
    funext v
    ring
  rw [truncatedSieveFace, hfirst, hsecond]
  simp (disch := (apply Continuous.intervalIntegrable; fun_prop)) only
    [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, integral_pow]
  dsimp [sieveFaceKernel]
  ring

theorem sieveFaceKernel_nonneg {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ sieveFaceKernel z := by
  have hz0 := hz.1
  have hz1 : 0 ≤ 1 - z := sub_nonneg.mpr hz.2
  unfold sieveFaceKernel
  positivity

private noncomputable def geometricLower (z : ℝ) : ℝ :=
  1 + z / 4 + (z / 4) ^ 2 + (z / 4) ^ 3

private theorem geometricLower_le {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    geometricLower z ≤ 1 / (1 - z / 4) := by
  have hd : 0 < 1 - z / 4 := by linarith [hz.2]
  apply (le_div_iff₀ hd).mpr
  have hidentity : geometricLower z * (1 - z / 4) = 1 - (z / 4) ^ 4 := by
    dsimp [geometricLower]
    ring
  rw [hidentity]
  exact sub_le_self _ (pow_nonneg (by linarith [hz.1]) 4)

private theorem integral_geometricLower :
    (∫ z in (0 : ℝ)..1, sieveFaceKernel z * geometricLower z) = 252551 / 268800 := by
  have hpoly : (fun z : ℝ => sieveFaceKernel z * geometricLower z) =
      (fun z => -(7 / 320 : ℝ) * z ^ 7 + (13 / 1280 : ℝ) * z ^ 6 -
        (53 / 480 : ℝ) * z ^ 5 - (683 / 1920 : ℝ) * z ^ 4 +
        (401 / 96 : ℝ) * z ^ 3 - (199 / 24 : ℝ) * z ^ 2 + (11 / 2 : ℝ) * z ^ 1) := by
    funext z
    dsimp [sieveFaceKernel, geometricLower]
    ring
  rw [hpoly]
  simp (disch := (apply Continuous.intervalIntegrable; fun_prop)) only
    [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, integral_pow]
  norm_num

theorem linearSemiprimeIntegral_lower :
    252551 / 268800 ≤ linearSemiprimeIntegral := by
  rw [← integral_geometricLower]
  have hcont : ContinuousOn (fun z : ℝ => sieveFaceKernel z / (1 - z / 4))
      (Set.Icc (0 : ℝ) 1) := by
    apply ContinuousOn.div (by unfold sieveFaceKernel; fun_prop) (by fun_prop)
    intro z hz
    linarith [hz.2]
  apply intervalIntegral.integral_mono_on (by norm_num)
    (by apply Continuous.intervalIntegrable; unfold sieveFaceKernel geometricLower; fun_prop)
    (hcont.intervalIntegrable_of_Icc (by norm_num))
  intro z hz
  simpa only [mul_one_div] using
    mul_le_mul_of_nonneg_left (geometricLower_le hz) (sieveFaceKernel_nonneg hz)

/-- An exact positive margin, with all integrals and the logarithm checked by
Lean. No numerical quadrature or external numerical oracle is used. -/
theorem linear_sieve_integral_positive_margin :
    linearSieveMass + 1 / 1000 <
      (3 / 4 : ℝ) * (linearSemiprimeIntegral + Real.log 3 * truncatedSieveFace 1) := by
  rw [linearSieveMass_eq, truncatedSieveFace_eq]
  norm_num [sieveFaceKernel]
  nlinarith [linearSemiprimeIntegral_lower, Real.log_three_gt_d9]

private theorem integral_sieveFaceKernel_mul_pow (n : ℕ) :
    (∫ z in (0 : ℝ)..1, sieveFaceKernel z * z ^ n) =
      (11 / 2 : ℝ) / (n + 2) - (29 / 3 : ℝ) / (n + 3) +
        (25 / 4 : ℝ) / (n + 4) - (7 / 5 : ℝ) / (n + 5) := by
  have hpoly : (fun z : ℝ => sieveFaceKernel z * z ^ n) =
      (fun z => (11 / 2 : ℝ) * z ^ (n + 1) - (29 / 3 : ℝ) * z ^ (n + 2) +
        (25 / 4 : ℝ) * z ^ (n + 3) - (7 / 5 : ℝ) * z ^ (n + 4)) := by
    funext z
    dsimp [sieveFaceKernel]
    simp only [pow_add]
    ring
  rw [hpoly]
  simp (disch := (apply Continuous.intervalIntegrable; fun_prop)) only
    [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, integral_pow]
  simp
  ring

private noncomputable def geometricLowerAt (a z : ℝ) : ℝ :=
  1 + a * z + (a * z) ^ 2 + (a * z) ^ 3

private theorem geometricLowerAt_le {a z : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) (1 / 4))
    (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    geometricLowerAt a z ≤ 1 / (1 - a * z) ∧ 1 / (1 - a * z) ≤ 4 / 3 := by
  have haq : 0 ≤ a * z := mul_nonneg ha.1 hz.1
  have haq' : a * z ≤ 1 / 4 := by nlinarith [ha.1, ha.2, hz.1, hz.2]
  have hd : 0 < 1 - a * z := by linarith
  constructor
  · apply (le_div_iff₀ hd).mpr
    have heq : geometricLowerAt a z * (1 - a * z) = 1 - (a * z) ^ 4 := by
      dsimp [geometricLowerAt]
      ring
    rw [heq]
    exact sub_le_self _ (pow_nonneg haq 4)
  · apply (div_le_iff₀ hd).mpr
    nlinarith

private theorem integral_geometricLowerAt (a : ℝ) :
    (∫ z in (0 : ℝ)..1, sieveFaceKernel z * geometricLowerAt a z) =
      2917 / 3600 + a * (13 / 30) + a ^ 2 * (17 / 60) + a ^ 3 * (521 / 2520) := by
  have hpoly : (fun z : ℝ => sieveFaceKernel z * geometricLowerAt a z) =
      (fun z => sieveFaceKernel z * z ^ 0 + a * (sieveFaceKernel z * z ^ 1) +
        a ^ 2 * (sieveFaceKernel z * z ^ 2) + a ^ 3 * (sieveFaceKernel z * z ^ 3)) := by
    funext z
    dsimp [geometricLowerAt]
    ring
  rw [hpoly]
  simp (disch := (apply Continuous.intervalIntegrable; unfold sieveFaceKernel; fun_prop)) only
    [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      integral_sieveFaceKernel_mul_pow]
  norm_num

private theorem sieveFaceKernel_le {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    sieveFaceKernel z ≤ (11 / 2) * z := by
  have h0 : 0 ≤ 1 - z := by linarith [hz.2]
  have h1 : 1 - z ≤ 1 := by linarith [hz.1]
  have h2 := pow_le_one₀ (n := 2) h0 h1
  have h3 := pow_le_one₀ (n := 3) h0 h1
  have hsum : 41 + 82 * (1 - z) + 123 * (1 - z) ^ 2 + 84 * (1 - z) ^ 3 ≤ 330 := by
    linarith
  unfold sieveFaceKernel
  calc
    _ ≤ z / 60 * 330 := mul_le_mul_of_nonneg_left hsum (by linarith [hz.1])
    _ = _ := by ring

private theorem integral_small_cutoff_le (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) (1 / 4)) :
    (∫ z in (0 : ℝ)..(1 / 100), sieveFaceKernel z * geometricLowerAt a z) ≤ 11 / 15000 := by
  have hbound : (∫ z in (0 : ℝ)..(1 / 100),
      sieveFaceKernel z * geometricLowerAt a z) ≤ ∫ _ in (0 : ℝ)..(1 / 100), (11 / 150 : ℝ) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      (by apply Continuous.intervalIntegrable; unfold sieveFaceKernel geometricLowerAt; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)
    intro z hz
    have hzunit : z ∈ Set.Icc (0 : ℝ) 1 := ⟨hz.1, by linarith [hz.2]⟩
    have hkernel := sieveFaceKernel_nonneg hzunit
    have hkle : sieveFaceKernel z ≤ 11 / 200 := by
      have := sieveFaceKernel_le hzunit
      linarith [hz.2]
    have hg := (geometricLowerAt_le ha hzunit).1.trans (geometricLowerAt_le ha hzunit).2
    calc
      _ ≤ sieveFaceKernel z * (4 / 3) := mul_le_mul_of_nonneg_left hg hkernel
      _ ≤ (11 / 200) * (4 / 3) := mul_le_mul_of_nonneg_right hkle (by norm_num)
      _ = _ := by norm_num
  convert hbound using 1
  norm_num

/-- A radius exponent strictly below one quarter, leaving room for a
distribution level strictly below one half. -/
noncomputable def sieveRadiusExponent : ℝ := 24999 / 100000

noncomputable def subcriticalSemiprimeIntegral : ℝ :=
  ∫ z in (1 / 100 : ℝ)..1, sieveFaceKernel z / (1 - sieveRadiusExponent * z)

theorem subcriticalSemiprimeIntegral_lower :
    2917 / 3600 + sieveRadiusExponent * (13 / 30) + sieveRadiusExponent ^ 2 * (17 / 60) +
      sieveRadiusExponent ^ 3 * (521 / 2520) - 11 / 15000 ≤ subcriticalSemiprimeIntegral := by
  have ha : sieveRadiusExponent ∈ Set.Icc (0 : ℝ) (1 / 4) := by
    norm_num [sieveRadiusExponent]
  have hci : Continuous
      (fun z : ℝ => sieveFaceKernel z * geometricLowerAt sieveRadiusExponent z) := by
    unfold sieveFaceKernel geometricLowerAt
    fun_prop
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hci.intervalIntegrable 0 (1 / 100)) (hci.intervalIntegrable (1 / 100) 1)
  have hlower : 2917 / 3600 + sieveRadiusExponent * (13 / 30) +
      sieveRadiusExponent ^ 2 * (17 / 60) +
      sieveRadiusExponent ^ 3 * (521 / 2520) - 11 / 15000 ≤
      ∫ z in (1 / 100 : ℝ)..1, sieveFaceKernel z * geometricLowerAt sieveRadiusExponent z := by
    rw [integral_geometricLowerAt] at hsplit
    linarith [integral_small_cutoff_le sieveRadiusExponent ha]
  apply hlower.trans
  have hcont : ContinuousOn
      (fun z : ℝ => sieveFaceKernel z / (1 - sieveRadiusExponent * z))
      (Set.Icc (1 / 100 : ℝ) 1) := by
    apply ContinuousOn.div (by unfold sieveFaceKernel; fun_prop) (by fun_prop)
    intro z hz
    norm_num [sieveRadiusExponent] at *
    linarith [hz.2]
  apply intervalIntegral.integral_mono_on (by norm_num)
    (hci.intervalIntegrable _ _) (hcont.intervalIntegrable_of_Icc (by norm_num))
  intro z hz
  have hzunit : z ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hz.1], hz.2⟩
  simpa only [mul_one_div] using
    mul_le_mul_of_nonneg_left (geometricLowerAt_le ha hzunit).1 (sieveFaceKernel_nonneg hzunit)

/-- The certificate still has positive margin with a positive lower cutoff
on the small prime and a strictly subcritical sieve radius. -/
theorem subcritical_sieve_integral_positive_margin :
    linearSieveMass + 1 / 10000 < 3 * sieveRadiusExponent *
      (subcriticalSemiprimeIntegral +
        Real.log ((1 - sieveRadiusExponent) / sieveRadiusExponent) * truncatedSieveFace 1) := by
  have hlog : Real.log 3 < Real.log ((1 - sieveRadiusExponent) / sieveRadiusExponent) := by
    apply Real.log_lt_log (by norm_num)
    norm_num [sieveRadiusExponent]
  have hlower := subcriticalSemiprimeIntegral_lower
  rw [linearSieveMass_eq, truncatedSieveFace_eq]
  norm_num [sieveRadiusExponent, sieveFaceKernel] at hlog hlower ⊢
  nlinarith [Real.log_three_gt_d9]

end Erdos964
