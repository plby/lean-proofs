/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSourceScales

/-! # Exact stronger gap scale and loss from rounding the covered interval -/

namespace Erdos4b

noncomputable section

def fgkmtScale (X : ℝ) : ℝ :=
  Real.log X * Real.log (Real.log X) * Real.log (Real.log (Real.log (Real.log X))) /
    Real.log (Real.log (Real.log X))

theorem strongThreshold_eq_fgkmtScale (c : ℝ) (n : ℕ) :
    strongThreshold c n = c * fgkmtScale n := by
  unfold strongThreshold fgkmtScale
  ring

namespace FGKMT

open Filter

theorem eventually_source_gap_length_lower {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop, sourceIntervalLength c x / 2 ≤
      ((⌊sourceIntervalLength c x⌋₊ - x : ℕ) : ℝ) := by
  filter_upwards [eventually_sourceIntervalLength_bounds (by positivity : 0 < c / 4),
    eventually_ge_atTop (1 : ℕ)] with x hy hx
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hscale : sourceIntervalLength (c / 4) x = sourceIntervalLength c x / 4 := by
    unfold sourceIntervalLength
    ring
  rw [hscale] at hy
  have hy4 : 4 * (x : ℝ) ≤ sourceIntervalLength c x := by linarith [hy.1]
  have hy0 : 0 ≤ sourceIntervalLength c x := by linarith
  have hxY : x ≤ ⌊sourceIntervalLength c x⌋₊ :=
    (Nat.le_floor_iff hy0).mpr (by linarith)
  rw [Nat.cast_sub hxY]
  have hfloor := Nat.lt_floor_add_one (sourceIntervalLength c x)
  linarith

theorem fgkmtScale_le_source_envelope {B X : ℝ} {x : ℕ} (hB : 1 ≤ B)
    (hx : 2 * B ≤ (x : ℝ)) (hL : 1 ≤ Real.log (x : ℝ))
    (hℓ : 1 ≤ Real.log (Real.log (x : ℝ)))
    (ht : 1 ≤ Real.log (Real.log (Real.log (x : ℝ))))
    (hlo : Real.exp (B * x) ≤ X) (hhi : X ≤ Real.exp (2 * B * x)) :
    fgkmtScale X ≤ 8 * B * sourceIntervalLength 1 x := by
  let L := Real.log (x : ℝ)
  let ℓ := Real.log L
  let t := Real.log ℓ
  let A := Real.log X
  let V := Real.log A
  let W := Real.log V
  let T := Real.log W
  have hBpos : 0 < B := by linarith
  have hxpos : (0 : ℝ) < x := by linarith
  have hLpos : 0 < L := by change 0 < Real.log (x : ℝ); linarith
  have hℓpos : 0 < ℓ := by change 0 < Real.log (Real.log (x : ℝ)); linarith
  have htpos : 0 < t := by change 0 < Real.log (Real.log (Real.log (x : ℝ))); linarith
  have hXpos : 0 < X := (Real.exp_pos _).trans_le hlo
  have hAlo : (x : ℝ) ≤ A := by
    have hh := (Real.le_log_iff_exp_le hXpos).mpr hlo
    have hBx := mul_le_mul_of_nonneg_right hB hxpos.le
    change B * x ≤ A at hh
    nlinarith
  have hAhi : A ≤ 2 * B * x := (Real.log_le_iff_le_exp hXpos).mpr hhi
  have hApos : 0 < A := hxpos.trans_le hAlo
  have hVlo : L ≤ V := Real.log_le_log hxpos hAlo
  have hVpos : 0 < V := hLpos.trans_le hVlo
  have hVhi : V ≤ 2 * L := by
    have hh := Real.log_le_log hApos hAhi
    rw [Real.log_mul (by positivity : 2 * B ≠ 0) hxpos.ne'] at hh
    have hBLog := Real.log_le_log (by positivity : 0 < 2 * B) hx
    change Real.log (2 * B) ≤ L at hBLog
    change V ≤ Real.log (2 * B) + L at hh
    linarith
  have hWlo : ℓ ≤ W := Real.log_le_log hLpos hVlo
  have hWpos : 0 < W := hℓpos.trans_le hWlo
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hWhi : W ≤ 2 * ℓ := by
    have hh := Real.log_le_log hVpos hVhi
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hLpos.ne'] at hh
    change W ≤ Real.log 2 + ℓ at hh
    change 1 ≤ ℓ at hℓ
    linarith
  have hT0 : 0 ≤ T := Real.log_nonneg (hℓ.trans hWlo)
  have hThi : T ≤ 2 * t := by
    have hh := Real.log_le_log hWpos hWhi
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hℓpos.ne'] at hh
    change T ≤ Real.log 2 + t at hh
    change 1 ≤ t at ht
    linarith
  have hnum : A * V * T ≤ (2 * B * x) * (2 * L) * (2 * t) :=
    mul_le_mul (mul_le_mul hAhi hVhi hVpos.le (by positivity)) hThi hT0 (by positivity)
  calc
    fgkmtScale X = A * V * T / W := rfl
    _ ≤ ((2 * B * x) * (2 * L) * (2 * t)) / W :=
      div_le_div_of_nonneg_right hnum hWpos.le
    _ ≤ ((2 * B * x) * (2 * L) * (2 * t)) / ℓ :=
      div_le_div_of_nonneg_left (by positivity) hℓpos hWlo
    _ = 8 * B * sourceIntervalLength 1 x := by
      unfold sourceIntervalLength
      dsimp [L, ℓ, t]
      ring

end FGKMT

end

end Erdos4b
