/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSourceSmallPrimes
import ErdosProblems.Erdos4b.FGKMTSmoothEuler

/-! # The Rankin exponent on the full source parameter ray -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

def sourceSmoothDelta (a : ℝ) (x : ℕ) : ℝ :=
  a * Real.log (Real.log (x : ℝ)) / (2 * Real.log (x : ℝ))

theorem sourceSmoothDelta_mul_log {a : ℝ} {x : ℕ} (hL : Real.log (x : ℝ) ≠ 0) :
    sourceSmoothDelta a x * Real.log (x : ℝ) =
      (a / 2) * Real.log (Real.log (x : ℝ)) := by
  unfold sourceSmoothDelta
  field_simp

theorem sourceSmoothDelta_mul_log_upper {a : ℝ} {x : ℕ} (ha : a ≠ 0)
    (hL : Real.log (x : ℝ) ≠ 0) (hℓ : Real.log (Real.log (x : ℝ)) ≠ 0) :
    sourceSmoothDelta a x * Real.log (sourceSmallPrimeUpper a x) =
      Real.log (Real.log (Real.log (x : ℝ))) / 2 := by
  rw [sourceSmoothDelta, log_sourceSmallPrimeUpper]
  field_simp

theorem eventually_sourceSmoothDelta_ranges {a : ℝ} (ha : 2 ≤ a) :
    ∀ᶠ x : ℕ in atTop,
      1 ≤ Real.log (x : ℝ) ∧ 1 ≤ Real.log (Real.log (x : ℝ)) ∧
      0 < sourceSmoothDelta a x ∧ sourceSmoothDelta a x ≤ 1 / 2 ∧
      (sourceSmoothDelta a x)⁻¹ ≤ Real.log (x : ℝ) ∧
      0 < ⌊sourceSmallPrimeUpper a x⌋₊ ∧
      (⌊sourceSmallPrimeUpper a x⌋₊ : ℝ) ^ sourceSmoothDelta a x ≤
        Real.log (Real.log (x : ℝ)) := by
  have hapos : 0 < a := by linarith
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog := Real.tendsto_log_atTop.comp hlog
  have hsmall := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).comp_tendsto
    hlog).def (by positivity : 0 < 1 / a)
  filter_upwards [hsmall, eventually_sourceSmallPrime_ranges hapos,
    hlog.eventually_ge_atTop 1, hloglog.eventually_ge_atTop 1] with x hs hz hL hℓ
  let L := Real.log (x : ℝ)
  let ℓ := Real.log L
  let δ := sourceSmoothDelta a x
  change 1 ≤ L at hL
  change 1 ≤ ℓ at hℓ
  change ‖ℓ‖ ≤ (1 / a) * ‖L ^ (1 : ℝ)‖ at hs
  have hLpos : 0 < L := by linarith
  have hℓpos : 0 < ℓ := by linarith
  have hδ : 0 < δ := div_pos (mul_pos hapos hℓpos) (mul_pos (by norm_num) hLpos)
  have hs' : ℓ ≤ L / a := by
    simpa only [Function.comp_apply, Real.rpow_one, Real.norm_eq_abs,
      abs_of_pos hLpos, abs_of_pos hℓpos, one_div, div_eq_mul_inv, mul_comm, mul_one] using hs
  have haℓ : a * ℓ ≤ L := by
    have h := (le_div_iff₀ hapos).mp hs'
    nlinarith
  have hδhalf : δ ≤ 1 / 2 := by
    change a * ℓ / (2 * L) ≤ 1 / 2
    apply (div_le_iff₀ (by positivity : 0 < 2 * L)).mpr
    linarith
  have hinv : δ⁻¹ ≤ L := by
    have hid : δ⁻¹ = 2 * L / (a * ℓ) := by
      change (a * ℓ / (2 * L))⁻¹ = _
      rw [inv_div]
    rw [hid]
    apply (div_le_iff₀ (mul_pos hapos hℓpos)).mpr
    have haℓ2 : 2 ≤ a * ℓ := by
      have hh := mul_le_mul_of_nonneg_left hℓ hapos.le
      change a * 1 ≤ a * ℓ at hh
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left haℓ2 hLpos.le]
  have hzpos : 0 < sourceSmallPrimeUpper a x := Real.exp_pos _
  have hZ : 0 < ⌊sourceSmallPrimeUpper a x⌋₊ := by
    have hz1 : (1 : ℝ) ≤ sourceSmallPrimeUpper a x := by linarith [hz.1, hz.2.1]
    exact Nat.succ_le_iff.mp ((Nat.le_floor_iff hzpos.le).mpr (by simpa using hz1))
  have hZpow : (⌊sourceSmallPrimeUpper a x⌋₊ : ℝ) ^ δ ≤ ℓ := by
    calc
      _ ≤ (sourceSmallPrimeUpper a x) ^ δ :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hzpos.le) hδ.le
      _ = Real.exp (Real.log ℓ / 2) := by
        rw [Real.rpow_def_of_pos hzpos, mul_comm,
          sourceSmoothDelta_mul_log_upper hapos.ne' hLpos.ne' hℓpos.ne']
      _ ≤ Real.exp (Real.log ℓ) := Real.exp_le_exp.mpr (by
        have ht : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ
        linarith)
      _ = ℓ := Real.exp_log hℓpos
  exact ⟨hL, hℓ, hδ, hδhalf, hinv, hZ, hZpow⟩

end

end Erdos4b.FGKMT
