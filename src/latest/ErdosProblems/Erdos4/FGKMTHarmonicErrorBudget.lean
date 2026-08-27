import ErdosProblems.Erdos4.FGKMTSieveDivisorLaw
import ErdosProblems.Erdos4.FGKMTLogarithmicAbsorption

/-! Uniform harmonic accuracy for all the growing sieve parameters. -/

namespace Erdos4.FGKMT

open Filter Asymptotics BoundedGaps.Maynard

theorem eventually_sieve_harmonic_error :
    ∀ᶠ x : ℕ in atTop, ∀ j R D B : ℕ, ∀ a : ℝ,
      16 ≤ j → 2 ≤ R → 2 ≤ D → a ≤ 1 / 4 →
      (sieveDimension j : ℝ) ≤ Real.log (x : ℝ) ^ (1 / 16 : ℝ) →
      (D : ℝ) ≤ Real.log (x : ℝ) ^ (1 / 4 : ℝ) →
      Real.log (x : ℝ) / 100 ≤ Real.log (R : ℝ) →
      (B = 1 ∨ B.Prime) → B ≤ exponentialConductorCutoff a x →
      harmonicTransferError (harmonicModulus D B) ≤
        coprimeHarmonicDensity (harmonicModulus D B) * Real.log (R : ℝ) /
          (2 * (1 + sieveProfileScale j)) := by
  obtain ⟨c, hc, hdensity⟩ := exists_harmonicModulus_density_lower
  let K₀ := 2 * (uniformHarmonicConstant + 1)
  let C := K₀ * (2 + Real.log 4)
  have hK₀ : 0 < K₀ := by
    have hh := uniformHarmonicConstant_pos
    unfold K₀
    positivity
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hC : 0 < C := by unfold C; positivity
  have hlogTop := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hdom := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 8)).comp_tendsto
    hlogTop).bound (show 0 < c / (200 * C) by positivity)
  filter_upwards [hdom, hlogTop.eventually (eventually_ge_atTop 2)] with x hdom hlarge
  let L := Real.log (x : ℝ)
  change 2 ≤ L at hlarge
  have hL : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hdom' : Real.log L ≤ (c / (200 * C)) * L ^ (3 / 8 : ℝ) := by
    change ‖Real.log L‖ ≤ (c / (200 * C)) * ‖L ^ (3 / 8 : ℝ)‖ at hdom
    simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg hlogL,
      abs_of_nonneg (Real.rpow_nonneg hL.le (3 / 8 : ℝ))] using hdom
  intro j R D B a hj hR hD ha hk hDx hRx hB hBx
  change (sieveDimension j : ℝ) ≤ L ^ (1 / 16 : ℝ) at hk
  change (D : ℝ) ≤ L ^ (1 / 4 : ℝ) at hDx
  change L / 100 ≤ Real.log (R : ℝ) at hRx
  have hu1 : 1 ≤ Real.sqrt L := (Real.one_le_sqrt).mpr hL1
  have hu0 : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
  have hDu : (D : ℝ) ≤ Real.sqrt L := by
    apply hDx.trans
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hDL : (D : ℝ) ≤ L := hDx.trans
    ((Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (1 / 4 : ℝ) ≤ 1)).trans_eq (Real.rpow_one L))
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hlogDpos : 0 < Real.log (D : ℝ) := Real.log_pos (by exact_mod_cast hD)
  have hlogD : Real.log (D : ℝ) ≤ Real.log L := Real.log_le_log hDpos hDL
  have hE : harmonicTransferError (harmonicModulus D B) ≤ C * Real.sqrt L := by
    have hh := harmonicTransferError_excision D hB hBx
    change harmonicTransferError (harmonicModulus D B) ≤
      K₀ * (1 + Real.log 4 * (D : ℝ) + a * Real.sqrt L) at hh
    have hDmul := mul_le_mul_of_nonneg_left hDu hlog4
    have hamul := mul_le_mul_of_nonneg_right ha hu0
    have hinner : 1 + Real.log 4 * (D : ℝ) + a * Real.sqrt L ≤
        (2 + Real.log 4) * Real.sqrt L := by nlinarith
    exact hh.trans ((mul_le_mul_of_nonneg_left hinner hK₀.le).trans_eq (by unfold C; ring))
  have hksq : (sieveDimension j : ℝ) ^ 2 ≤ L ^ (1 / 8 : ℝ) := by
    apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hk 2).trans_eq
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    norm_num
  have hz : 0 ≤ 1 + sieveProfileScale j := by
    have hh := sieveProfileScale_ge_one (by omega : 1 ≤ j)
    linarith
  have hzupper : 1 + sieveProfileScale j ≤ L ^ (1 / 8 : ℝ) := (sieveProfileScale_le_square hj).trans hksq
  have hpow : L ^ (1 / 8 : ℝ) * Real.sqrt L = L ^ (5 / 8 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hL]
    norm_num
  have hleft : 2 * (1 + sieveProfileScale j) * harmonicTransferError (harmonicModulus D B) ≤
      2 * C * L ^ (5 / 8 : ℝ) := by
    calc
      _ ≤ 2 * (1 + sieveProfileScale j) * (C * Real.sqrt L) :=
        mul_le_mul_of_nonneg_left hE (by positivity)
      _ ≤ (2 * L ^ (1 / 8 : ℝ)) * (C * Real.sqrt L) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzupper (by norm_num)) (by positivity)
      _ = 2 * C * (L ^ (1 / 8 : ℝ) * Real.sqrt L) := by ring
      _ = _ := by rw [hpow]
  have hdominates : (2 * C * L ^ (5 / 8 : ℝ)) * Real.log L ≤ c * L / 100 := by
    calc
      _ ≤ (2 * C * L ^ (5 / 8 : ℝ)) * ((c / (200 * C)) * L ^ (3 / 8 : ℝ)) :=
        mul_le_mul_of_nonneg_left hdom' (by positivity)
      _ = (c / 100) * (L ^ (5 / 8 : ℝ) * L ^ (3 / 8 : ℝ)) := by field_simp; ring
      _ = _ := by rw [← Real.rpow_add hL]; norm_num; ring
  have hρ := hdensity D B hD hB
  have hcρ : c ≤ coprimeHarmonicDensity (harmonicModulus D B) * Real.log (D : ℝ) :=
    (div_le_iff₀ hlogDpos).mp hρ
  have hRlog : 0 ≤ Real.log (R : ℝ) := Real.log_natCast_nonneg R
  have hright : c * L / 100 ≤ coprimeHarmonicDensity (harmonicModulus D B) *
      Real.log (R : ℝ) * Real.log (D : ℝ) := by
    calc
      _ = c * (L / 100) := by ring
      _ ≤ c * Real.log (R : ℝ) := mul_le_mul_of_nonneg_left hRx hc.le
      _ ≤ (coprimeHarmonicDensity (harmonicModulus D B) * Real.log (D : ℝ)) * Real.log (R : ℝ) :=
        mul_le_mul_of_nonneg_right hcρ hRlog
      _ = _ := by ring
  have hcombined := (mul_le_mul hleft hlogD hlogDpos.le (by positivity)).trans (hdominates.trans hright)
  have hfinal := (mul_le_mul_iff_left₀ hlogDpos).mp hcombined
  apply (le_div_iff₀ (by have hh := sieveProfileScale_ge_one (by omega : 1 ≤ j); positivity)).mpr
  simpa only [mul_comm] using hfinal

end Erdos4.FGKMT
