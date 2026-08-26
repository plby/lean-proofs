import ErdosProblems.Erdos421.SmoothedVonMangoldtBound
import ErdosProblems.Erdos421.PerronPowerBounds
import ErdosProblems.Erdos421.PerronContourAlgebra

/-! # Uniform smoothed prime-weighted bounds across polynomial frequency ranges -/

namespace Erdos421

open Filter Topology

theorem exists_smoothedVonMangoldt_power_majorant (K : ℕ) :
    ∃ C > 0, ∃ T₁ > 1, ∀ᶠ x : ℝ in atTop, ∀ t : ℝ, T₁ ≤ |t| → |t| ≤ x ^ K →
      ‖smoothedVonMangoldtSum x t‖ / x ≤ C *
        (Real.exp (-perronWidthCoefficient K * (Real.log x) ^ (1 / 16 : ℝ)) * (Real.log x) ^ 2 +
          (Real.log x) ^ 2 / |t|) := by
  obtain ⟨B, hB, r, hr, T₀, hT₀, hbound⟩ := exists_smoothedVonMangoldt_numeric_bound
  let Q : ℝ := (2 : ℝ) ^ 52 * ((K : ℝ) + 1) ^ 2
  let C : ℝ := 4 * Real.pi * Q + 16 * Real.exp 1 * Q + 4 * Real.exp 1 * (B + 1)
  let T₁ : ℝ := max (2 * T₀) (Real.exp 1)
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hT₁ : 1 < T₁ := (by linarith : 1 < 2 * T₀).trans_le (le_max_left _ _)
  refine ⟨C, hC, T₁, hT₁, ?_⟩
  have hinv := Real.tendsto_log_atTop.const_div_atTop (1 : ℝ)
  have hlogs : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  filter_upwards [eventually_ge_atTop (2 : ℝ), hlogs,
    hinv.eventually (gt_mem_nhds hr), perronShiftWidth_covers_inverse_log_eventually K]
    with x hx hlog hinv hcover
  intro t ht htupper
  let T : ℝ := |t|
  let δ : ℝ := perronShiftWidth T
  let a : ℝ := 1 - δ
  let b : ℝ := 1 + 1 / Real.log x
  let E : ℝ := Real.exp (-perronWidthCoefficient K * (Real.log x) ^ (1 / 16 : ℝ))
  let Z : ℝ := (2 : ℝ) ^ 52 * (Real.log (T + T / 2)) ^ 2
  have hxp : 0 < x := by linarith
  have hlogp : 0 < Real.log x := by linarith
  have hTp : 1 < T := hT₁.trans_le ht
  have hTe : Real.exp 1 ≤ T := (le_max_right _ _).trans ht
  have hTlarge : 2 * T₀ ≤ T := (le_max_left _ _).trans ht
  have hδp : 0 < δ := perronShiftWidth_pos hTp
  have hδsmall : δ ≤ 1 / 64 := perronShiftWidth_le hTe
  have hcoverT : 1 / Real.log x ≤ δ := hcover T hTp htupper
  have ha : 1 / 2 ≤ a := by dsimp only [a]; linarith
  have hinvpos : 0 < 1 / Real.log x := one_div_pos.mpr hlogp
  have hb : 1 < b := by dsimp only [b]; linarith
  have hab : a ≤ b := by dsimp only [a, b]; linarith
  have hbr : b < 1 + r := by dsimp only [b]; linarith
  have hbδ : b ≤ 1 + δ := by dsimp only [b]; linarith
  have hH : 0 < T / 2 := by linarith
  have htime : T₀ + T / 2 ≤ |t| := by change T₀ + T / 2 ≤ T; linarith
  have hd : 0 ≤ b - a := sub_nonneg.mpr hab
  have hd2 : b - a ≤ 2 := by
    have hi : 1 / Real.log x ≤ 1 := (div_le_one hlogp).mpr hlog
    dsimp only [a, b]
    linarith
  have hraw := hbound x t a b (T / 2) δ (by linarith) ha hab hb hbr hH le_rfl hbδ htime
    (perronShiftWidth_fits_half_height hTp)
  have hbpower : x ^ b = Real.exp 1 * x := perron_right_power_identity (by linarith)
  have hbinv : 1 / (b - 1) = Real.log x := by
    dsimp only [b]
    rw [add_sub_cancel_left, one_div_div]
    simp only [div_one]
  have hpower : x ^ a ≤ x * E := perronShiftWidth_power_saving hx hTp K htupper
  have hZ : Z ≤ Q * (Real.log x) ^ 2 := perron_height_majorant_le hx hTp K htupper
  change ‖smoothedVonMangoldtSum x t‖ ≤ (1 / (2 * Real.pi)) *
    (4 * Real.pi * x ^ a * Z + 2 * (b - a) * (x ^ b * Z / (T / 2) ^ 2) +
      2 * (x ^ b * (1 / (b - 1) + B)) / (T / 2)) at hraw
  rw [hbpower, hbinv] at hraw
  have hEn : 0 ≤ E := (Real.exp_pos _).le
  have hZn : 0 ≤ Z := by
    exact mul_nonneg (pow_nonneg (by norm_num) 52) (sq_nonneg _)
  have halgebra := perron_contour_expression_bound
    (x := x) (E := E) (L := Real.log x) (T := T) (B := B) (Q := Q)
    (A := x ^ a) (Z := Z) (d := b - a) hxp.le hEn hlog hTp.le
    hB.le hQ.le (Real.rpow_nonneg hxp.le a) hpower hZn hZ hd hd2
  have hnorm := hraw.trans halgebra
  apply (div_le_iff₀ hxp).mpr
  exact hnorm.trans_eq (by dsimp only [C, E, T]; ac_rfl)

end Erdos421
