/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Numerical conditions for the intended growing-dimensional profile

The scale choices are exactly `T = k log k` and `U = 1 / sqrt k`.
A fixed explicit mathematical threshold discharges the first-moment
condition for every smaller dimension at once.
-/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

def sieveProfileScale (k : ℕ) : ℝ := (k : ℝ) * Real.log k

def sieveProfileWidth (k : ℕ) : ℝ := 1 / Real.sqrt k

theorem log_le_fiftieth_of_large {x : ℝ} (hx : 10000 ≤ x) : Real.log x ≤ x / 50 := by
  have hx0 : 0 < x := by linarith
  have hs0 := Real.sqrt_nonneg x
  have hs2 := Real.sq_sqrt hx0.le
  have hs : 100 ≤ Real.sqrt x := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hs hs0
  have hl := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx0)
  rw [Real.log_sqrt hx0.le] at hl
  nlinarith

theorem sieveProfileScale_mul_width {k : ℕ} (hk : 0 < k) :
    sieveProfileScale k * sieveProfileWidth k = Real.sqrt k * Real.log k := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hs : 0 < Real.sqrt k := Real.sqrt_pos.mpr hkR
  unfold sieveProfileScale sieveProfileWidth
  rw [mul_one_div]
  apply (div_eq_iff hs.ne').mpr
  calc
    (k : ℝ) * Real.log k = Real.sqrt k ^ 2 * Real.log k := by rw [Real.sq_sqrt hkR.le]
    _ = _ := by ring

theorem profile_scales_bounds {k : ℕ} (hk : 0 < k) (hlog : 10000 ≤ Real.log k) :
    1 ≤ sieveProfileScale k ∧ 0 < sieveProfileWidth k ∧ sieveProfileWidth k ≤ 1 / 10 ∧
      1000 ≤ sieveProfileScale k * sieveProfileWidth k := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hklarge : 10000 ≤ (k : ℝ) := by linarith [Real.log_le_sub_one_of_pos hkR]
  have hs0 := Real.sqrt_nonneg (k : ℝ)
  have hs : 100 ≤ Real.sqrt k := by nlinarith [Real.sq_sqrt hkR.le]
  have hspos : 0 < Real.sqrt k := Real.sqrt_pos.mpr hkR
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold sieveProfileScale
    calc
      (1 : ℝ) = 1 * 1 := by norm_num
      _ ≤ (k : ℝ) * Real.log k :=
        mul_le_mul (by linarith) (by linarith) (by norm_num) hkR.le
  · unfold sieveProfileWidth
    positivity
  · unfold sieveProfileWidth
    apply (div_le_iff₀ hspos).mpr
    nlinarith
  · rw [sieveProfileScale_mul_width hk]
    have h := mul_le_mul hs hlog (by norm_num : (0 : ℝ) ≤ 10000) hs0
    nlinarith

theorem profile_scales_log_bound {k : ℕ} (hk : 0 < k) (hlog : 10000 ≤ Real.log k) :
    Real.log (1 + sieveProfileScale k * sieveProfileWidth k) ≤ (11 / 20) * Real.log k := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hs : 0 < Real.sqrt k := Real.sqrt_pos.mpr hkR
  have hL : 0 < Real.log k := by linarith
  have hTU := (profile_scales_bounds hk hlog).2.2.2
  have hz : 0 < sieveProfileScale k * sieveProfileWidth k := by linarith
  calc
    _ ≤ Real.log (2 * (sieveProfileScale k * sieveProfileWidth k)) :=
      Real.log_le_log (by linarith) (by linarith)
    _ = Real.log 2 + Real.log (Real.sqrt k) + Real.log (Real.log k) := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hz.ne', sieveProfileScale_mul_width hk,
        Real.log_mul hs.ne' hL.ne']
      ring
    _ ≤ _ := by
      rw [Real.log_sqrt hkR.le]
      nlinarith [log_le_fiftieth_of_large hlog,
        Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]

theorem profile_scales_moment_condition {k j : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) (hj : j ≤ k) :
    (j : ℝ) *
        (Real.log (1 + sieveProfileScale k * sieveProfileWidth k) / sieveProfileScale k ^ 2) ≤
      (3 / 5) * (((9 / 10) * sieveProfileWidth k) /
        (1 + sieveProfileScale k * ((9 / 10) * sieveProfileWidth k))) := by
  let T := sieveProfileScale k
  let U := sieveProfileWidth k
  let b : ℝ := (9 / 10) * U
  have hbds := profile_scales_bounds hk hlog
  have hT : 0 < T := zero_lt_one.trans_le hbds.1
  have hU : 0 < U := hbds.2.1
  have hTU : 1000 ≤ T * U := hbds.2.2.2
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hL : 0 < Real.log k := by linarith
  have hb : 0 < b := by dsimp only [b]; positivity
  have hlower : (99 / 100 : ℝ) / T ≤ b / (1 + T * b) := by
    apply (div_le_div_iff₀ hT (by positivity)).mpr
    dsimp only [b]
    nlinarith
  have hupper : (k : ℝ) * (Real.log (1 + T * U) / T ^ 2) ≤ (11 / 20) / T := by
    calc
      _ ≤ (k : ℝ) * (((11 / 20) * Real.log k) / T ^ 2) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (profile_scales_log_bound hk hlog) (sq_nonneg T)) hkR.le
      _ = _ := by
        dsimp only [T, sieveProfileScale]
        field_simp [hkR.ne', hL.ne']
  have hlog0 : 0 ≤ Real.log (1 + T * U) := Real.log_nonneg (by linarith)
  change (j : ℝ) * (Real.log (1 + T * U) / T ^ 2) ≤ (3 / 5) * (b / (1 + T * b))
  calc
    _ ≤ (k : ℝ) * (Real.log (1 + T * U) / T ^ 2) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hj) (div_nonneg hlog0 (sq_nonneg T))
    _ ≤ (11 / 20) / T := hupper
    _ ≤ (3 / 5) * ((99 / 100) / T) := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (by norm_num) hT.le
    _ ≤ _ := mul_le_mul_of_nonneg_left hlower (by norm_num)

theorem eventually_profile_scale_hypotheses :
    ∀ᶠ k : ℕ in atTop, 0 < k ∧ 10000 ≤ Real.log k := by
  have hlog : Tendsto (fun k : ℕ => Real.log (k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlog.eventually (eventually_ge_atTop 10000)]
    with k hk hl
  exact ⟨by omega, hl⟩

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.profile_scales_moment_condition
#print axioms Erdos4b.FGKMT.eventually_profile_scale_hypotheses
