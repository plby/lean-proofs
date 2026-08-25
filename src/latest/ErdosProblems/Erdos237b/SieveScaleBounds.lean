import ErdosProblems.Erdos237b.SieveCollisionLimits
import ErdosProblems.Erdos237b.YWeightBounds
import BoundedGaps.Maynard.ConcreteS2TauAsymptotics

/-!
# Generic normalization and negligible S1 counting errors

The scale and estimates here allow arbitrary finite tuples. A coarse bound
for the coefficients suffices for every fixed radius exponent below `1/4`.
-/

namespace Erdos237b

open Finset Filter BoundedGaps.Maynard
open scoped BigOperators

noncomputable def sieveScale (H : Finset ℕ) (alpha : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) / engelsmaMaynardModulus N * sieveCoordinateScale alpha N ^ Fintype.card H

theorem eventually_sieveScale_pos (H : Finset ℕ) {alpha : ℝ} (halpha : 0 < alpha) :
    ∀ᶠ N : ℕ in atTop, 0 < sieveScale H alpha N := by
  filter_upwards [eventually_sieveCoordinateScale_pos halpha, eventually_gt_atTop 0]
    with N hA hN
  have hW : (0 : ℝ) < engelsmaMaynardModulus N := by exact_mod_cast primorial_pos _
  unfold sieveScale
  positivity

theorem eventually_sieveScale_ge_modulus (H : Finset ℕ) {alpha : ℝ}
    (halpha : 0 < alpha) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) / (engelsmaMaynardModulus N : ℝ) ^ (Fintype.card H + 1) ≤
        sieveScale H alpha N := by
  filter_upwards [(tendsto_log_engelsmaMaynardRadius_atTop halpha).eventually_ge_atTop 1]
    with N hlog
  have hW : (0 : ℝ) < engelsmaMaynardModulus N := by exact_mod_cast primorial_pos _
  have hphi : (1 : ℝ) ≤ Nat.totient (engelsmaMaynardModulus N) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.totient_pos.mpr (primorial_pos _))
  have hA : 1 / (engelsmaMaynardModulus N : ℝ) ≤ sieveCoordinateScale alpha N := by
    unfold sieveCoordinateScale
    rw [preSieveSingularSeries_eq_totient_div]
    change _ ≤ (Nat.totient (engelsmaMaynardModulus N) : ℝ) /
      engelsmaMaynardModulus N * _
    calc
      _ = (1 / (engelsmaMaynardModulus N : ℝ)) * 1 := by ring
      _ ≤ _ := mul_le_mul (div_le_div_of_nonneg_right hphi hW.le) hlog (by norm_num)
        (by positivity)
  calc
    _ = (N : ℝ) / engelsmaMaynardModulus N *
        (1 / (engelsmaMaynardModulus N : ℝ)) ^ Fintype.card H := by
      rw [div_pow, one_pow, pow_succ]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hA _)
      (by positivity)

theorem eventually_radius_cast_le_rpow {alpha : ℝ} (halpha : 0 ≤ alpha) :
    ∀ᶠ N : ℕ in atTop, (engelsmaMaynardRadius alpha N : ℝ) ≤ (N : ℝ) ^ alpha := by
  filter_upwards [] with N
  calc
    _ ≤ ((N - 1 : ℕ) : ℝ) ^ alpha := Nat.floor_le (Real.rpow_nonneg (by positivity) _)
    _ ≤ _ := Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.sub_le N 1) halpha

theorem tendsto_log_pow_mul_rpow_div (t : ℕ) {alpha : ℝ} (halpha : alpha < 1 / 4) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ)) ^ t * ((N : ℝ) ^ alpha) ^ 4 / N)
      atTop (nhds 0) := by
  have hgap : 0 < 1 - alpha * 4 := by linarith
  have h := (isLittleO_log_rpow_rpow_atTop (t : ℝ) hgap).tendsto_div_nhds_zero
    |>.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [Function.comp_apply, Real.rpow_natCast]
  rw [Real.rpow_sub hn, Real.rpow_one, Real.rpow_mul hn.le]
  norm_num only [Real.rpow_ofNat, div_div_eq_mul_div]

theorem tendsto_normalized_coefficient_mass {H : Finset ℕ} {alpha B : ℝ}
    (halpha : 0 < alpha) (halpha' : alpha < 1 / 4) (hB : 0 ≤ B)
    (y : ℕ → (H → ℕ) → ℝ)
    (hy : ∀ N, IsSupportedMaynardY H (engelsmaMaynardRadius alpha N)
      (engelsmaMaynardModulus N) (y N))
    (hbound : ∀ N r, |y N r| ≤ B) :
    Tendsto (fun N : ℕ =>
      compatibleDivisorPairCoefficientMass H
        (maynardDivisorTupleSupport H (engelsmaMaynardRadius alpha N)
          (engelsmaMaynardModulus N))
        (maynardCoefficientFromY H (engelsmaMaynardRadius alpha N)
          (engelsmaMaynardModulus N) (y N)) / sieveScale H alpha N)
      atTop (nhds 0) := by
  let k := Fintype.card H
  let C : ℝ := B ^ 2 * (1 + alpha) ^ (6 * k)
  have hlim : Tendsto (fun N : ℕ => C *
      ((Real.log (N : ℝ)) ^ (9 * k + 3) * ((N : ℝ) ^ alpha) ^ 4 / N))
      atTop (nhds 0) := by
    simpa using (tendsto_log_pow_mul_rpow_div (9 * k + 3) halpha').const_mul C
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_sieveScale_pos H halpha] with N hS
    apply div_nonneg ?_ hS.le
    unfold compatibleDivisorPairCoefficientMass
    positivity
  · filter_upwards [eventually_sieveScale_ge_modulus H halpha,
      eventually_radius_cast_le_rpow halpha.le,
      eventually_one_add_log_engelsmaMaynardRadius_le halpha,
      eventually_engelsmaMaynardModulus_le_log_cube,
      eventually_gt_atTop 0] with N hS hR hlog hW hN
    have hn : (0 : ℝ) < N := by exact_mod_cast hN
    have hw : (0 : ℝ) < engelsmaMaynardModulus N := by exact_mod_cast primorial_pos _
    have hmass := coefficientFromY_mass_le_log (hy N) hB (hbound N)
    calc
      _ ≤ ((engelsmaMaynardRadius alpha N : ℝ) ^ 4 * B ^ 2 *
          (1 + Real.log (engelsmaMaynardRadius alpha N)) ^ (6 * k)) /
            ((N : ℝ) / (engelsmaMaynardModulus N : ℝ) ^ (k + 1)) :=
        div_le_div₀ (by positivity) hmass (by positivity) hS
      _ = ((engelsmaMaynardRadius alpha N : ℝ) ^ 4 * B ^ 2 *
          (1 + Real.log (engelsmaMaynardRadius alpha N)) ^ (6 * k)) *
            (engelsmaMaynardModulus N : ℝ) ^ (k + 1) / N := by
        rw [div_div_eq_mul_div]
      _ ≤ (((N : ℝ) ^ alpha) ^ 4 * B ^ 2 *
          ((1 + alpha) * Real.log (N : ℝ)) ^ (6 * k)) *
            ((Real.log (N : ℝ)) ^ 3) ^ (k + 1) / N := by gcongr
      _ = _ := by simp only [C, mul_pow]; ring

end Erdos237b
