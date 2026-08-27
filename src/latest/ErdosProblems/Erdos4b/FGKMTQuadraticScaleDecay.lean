/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTQuadraticScaleBound

/-! # Uniform power decay of the finite quadratic error -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

theorem eventually_dimensionScale_cube_le_rpow {K beta : ℝ} (hK : 0 < K) (hb : 0 < beta) :
    ∀ᶠ x : ℕ in atTop,
      K * dimensionLogLossScale x ^ 3 ≤ Real.log (x : ℝ) ^ beta := by
  have hlogTop : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall := ((isLittleO_log_rpow_rpow_atTop ((3 : ℕ) : ℝ) hb).comp_tendsto
    hlogTop).def (by positivity : 0 < 1 / (27 * K))
  filter_upwards [hsmall, hlogTop.eventually (eventually_ge_atTop (2 : ℝ)),
    (Real.tendsto_log_atTop.comp hlogTop).eventually (eventually_ge_atTop (1 : ℝ))] with
      x hsmall hL hlogL
  let L := Real.log (x : ℝ)
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hlogL1 : 1 ≤ Real.log L := hlogL
  have hscale : dimensionLogLossScale x ≤ 3 * Real.log L := by
    have harg : 1 + L ≤ L ^ 2 := by change 2 ≤ L at hL; nlinarith
    have h := Real.log_le_log (by positivity : 0 < 1 + L) harg
    rw [Real.log_pow] at h
    change 1 + Real.log (1 + L) ≤ _
    norm_num at h
    linarith
  have hsmall' : Real.log L ^ 3 ≤ (1 / (27 * K)) * L ^ beta := by
    change ‖Real.log L ^ ((3 : ℕ) : ℝ)‖ ≤ (1 / (27 * K)) * ‖L ^ beta‖ at hsmall
    simpa only [Real.rpow_natCast, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (by linarith : 0 ≤ Real.log L) 3),
      abs_of_nonneg (Real.rpow_nonneg hLpos.le beta)] using hsmall
  calc
    _ ≤ K * (3 * Real.log L) ^ 3 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (zero_le_one.trans (one_le_dimensionLogLossScale x)) hscale 3) hK.le
    _ = (27 * K) * Real.log L ^ 3 := by ring
    _ ≤ (27 * K) * ((1 / (27 * K)) * L ^ beta) :=
      mul_le_mul_of_nonneg_left hsmall' (by positivity)
    _ = _ := by
      change (27 * K) * ((1 / (27 * K)) * L ^ beta) = L ^ beta
      field_simp

theorem eventually_uniform_sieveQuadraticError_small {a H b C : ℝ}
    (ha : 0 ≤ a) (hH : 0 ≤ H) (hb : 0 < b) (hC : 0 < C) :
    ∀ᶠ x : ℕ in atTop, ∀ k B W R : ℕ,
      0 < B → 0 < W → 0 < R → R ≤ x →
      (B : ℝ) ≤ Real.exp (a * Real.sqrt (Real.log (x : ℝ))) →
      (W : ℝ) ≤ Real.exp (H * (k : ℝ) ^ 2) →
      (k : ℝ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ) →
      b * Real.log (x : ℝ) ≤ Real.log (R : ℝ) →
      C * sieveQuadraticErrorScale k (B * W) R ≤ Real.log (x : ℝ) ^ (-1 / 4 : ℝ) ∧
      C * sieveQuadraticErrorScale k (B * W) R ≤ 1 := by
  let A := a + H + 9
  let K := C * ((A ^ 3 + 1) / b)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hlogTop : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_dimensionScale_cube_le_rpow hK (by norm_num : (0 : ℝ) < 1 / 4),
    hlogTop.eventually (eventually_ge_atTop (1 : ℝ))] with x hsmall hL
  intro k B W R hB hW hR hRx hBsize hWsize hk hRlower
  have hLpos : 0 < Real.log (x : ℝ) := by linarith
  have hmod := quadraticModulusLogScale_le ha hH hL hB hW hR hRx hBsize hWsize hk
  have hbound := sieveQuadraticErrorScale_le_logEnvelope hA hb hLpos hmod hRlower hk
  have hfinal : C * sieveQuadraticErrorScale k (B * W) R ≤
      Real.log (x : ℝ) ^ (-1 / 4 : ℝ) := by
    calc
      _ ≤ C * (((A ^ 3 + 1) / b) * dimensionLogLossScale x ^ 3 *
          Real.log (x : ℝ) ^ (-1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hbound hC.le
      _ = (K * dimensionLogLossScale x ^ 3) * Real.log (x : ℝ) ^ (-1 / 2 : ℝ) := by
        dsimp only [K]
        ring
      _ ≤ Real.log (x : ℝ) ^ (1 / 4 : ℝ) * Real.log (x : ℝ) ^ (-1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hLpos.le _)
      _ = _ := by
        rw [← Real.rpow_add hLpos]
        norm_num
  exact ⟨hfinal, hfinal.trans (Real.rpow_le_one_of_one_le_of_nonpos hL (by norm_num))⟩

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.eventually_dimensionScale_cube_le_rpow
#print axioms Erdos4b.FGKMT.eventually_uniform_sieveQuadraticError_small
