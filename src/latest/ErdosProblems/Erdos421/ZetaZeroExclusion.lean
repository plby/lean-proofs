import ErdosProblems.Erdos421.ZetaZeroDetector

/-! # Quantitative exclusion of zeros from local norm bounds

The disk norm bounds in this file are explicit hypotheses of an analytic
lemma. Instantiating them uniformly from growth estimates remains a separate
step; no zero-free region is assumed.
-/

namespace Erdos421

open Complex Metric

theorem riemannZeta_ne_zero_of_disk_norm_bounds {u R A B t β : ℝ}
    (hu : 0 < u) (hR : 2 * u < R) (hA : 0 < A) (ht : R < |t|)
    (hpole : -(logDeriv riemannZeta ((1 + u : ℝ) : ℂ)).re ≤ 1 / u + B)
    (herror : u * (3 * B + 8 * u / R ^ 2 + 20 * A / R) ≤ 1 / 2)
    (hM1 : ∀ z ∈ sphere (0 : ℂ) R,
      ‖riemannZeta (((1 + u : ℝ) : ℂ) + t * I + z)‖ ≤
        Real.exp A * ‖riemannZeta (((1 + u : ℝ) : ℂ) + t * I)‖)
    (hM2 : ∀ z ∈ sphere (0 : ℂ) R,
      ‖riemannZeta (((1 + u : ℝ) : ℂ) + (2 * t : ℝ) * I + z)‖ ≤
        Real.exp A * ‖riemannZeta (((1 + u : ℝ) : ℂ) + (2 * t : ℝ) * I)‖)
    (hβ : 1 - u / 10 ≤ β) : riemannZeta ((β : ℂ) + t * I) ≠ 0 := by
  by_cases hβ1 : 1 ≤ β
  · exact riemannZeta_ne_zero_of_one_le_re (by simpa using hβ1)
  intro hz
  let d := 1 + u - β
  have hd : 0 < d := by dsimp only [d]; linarith
  have hdu : d ≤ 11 * u / 10 := by dsimp only [d]; linarith
  have hd2 : d < 2 * u := by linarith
  have hR0 : 0 < R := by linarith
  have hzero : riemannZeta (((1 + u : ℝ) : ℂ) + t * I - d) = 0 := by
    convert hz using 1
    congr 1
    dsimp only [d]
    push_cast
    ring
  have hb := riemannZeta_zero_three_four_one_bound (by linarith : 1 < 1 + u)
    hR0 hA ht hM1 hM2 hd (hd2.trans hR) hzero
  have hp : -3 * (logDeriv riemannZeta ((1 + u : ℝ) : ℂ)).re ≤ 3 / u + 3 * B := by
    calc
      _ = 3 * (-(logDeriv riemannZeta ((1 + u : ℝ) : ℂ)).re) := by ring
      _ ≤ 3 * (1 / u + B) := mul_le_mul_of_nonneg_left hpole (by norm_num)
      _ = _ := by ring
  have hsq : 4 * d / R ^ 2 ≤ 8 * u / R ^ 2 :=
    div_le_div_of_nonneg_right (by linarith) (sq_nonneg R)
  have hb' : 4 / d ≤ 3 / u + (3 * B + 8 * u / R ^ 2 + 20 * A / R) := by
    linarith only [hb, hp, hsq]
  have hmul := mul_le_mul_of_nonneg_left hb' hu.le
  have he : u * (3 / u + (3 * B + 8 * u / R ^ 2 + 20 * A / R)) =
      3 + u * (3 * B + 8 * u / R ^ 2 + 20 * A / R) := by
    rw [mul_add]
    congr 1
    field_simp
  rw [he] at hmul
  have hmul' : 4 * u / d ≤ 3 + u * (3 * B + 8 * u / R ^ 2 + 20 * A / R) := by
    calc
      4 * u / d = u * (4 / d) := by ring
      _ ≤ _ := hmul
  have hsmall : 4 * u / d ≤ 7 / 2 := by linarith only [hmul', herror]
  have hcontr := (div_le_iff₀ hd).mp hsmall
  nlinarith only [hcontr, hdu, hu]

theorem zeta_zero_detection_scale {R A B : ℝ} (hR : 0 < R) (hA : 0 < A) (hB : 0 ≤ B) :
    let u := R / (100 * (A + B * R + 1))
    0 < u ∧ 2 * u < R ∧ u * (3 * B + 8 * u / R ^ 2 + 20 * A / R) ≤ 1 / 2 := by
  let C := A + B * R + 1
  let u := R / (100 * C)
  have hC : 0 < C := by dsimp only [C]; positivity
  have hu : 0 < u := by dsimp only [u]; positivity
  have hCA : A ≤ C := by dsimp only [C]; nlinarith [mul_nonneg hB hR.le]
  have hCB : B * R ≤ C := by dsimp only [C]; linarith
  have hC1 : 1 ≤ C := by dsimp only [C]; nlinarith [mul_nonneg hB hR.le]
  have he : 100 * C * u = R := by dsimp only [u]; field_simp
  have huR : 100 * u ≤ R := by nlinarith [mul_le_mul_of_nonneg_right hC1 hu.le]
  have hAu : 100 * A * u ≤ R := by nlinarith [mul_le_mul_of_nonneg_right hCA hu.le]
  have hBu : 100 * B * u ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_right hCB hu.le
    nlinarith
  have hratio : u / R ≤ 1 / 100 := (div_le_iff₀ hR).mpr (by linarith)
  have hAratio : A * u / R ≤ 1 / 100 := (div_le_iff₀ hR).mpr (by linarith)
  have hBratio : B * u ≤ 1 / 100 := by linarith
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ u / R) hratio 2
  have herror : u * (3 * B + 8 * u / R ^ 2 + 20 * A / R) ≤ 1 / 2 := by
    have hid : u * (3 * B + 8 * u / R ^ 2 + 20 * A / R) =
        3 * (B * u) + 8 * (u / R) ^ 2 + 20 * (A * u / R) := by ring
    rw [hid]
    nlinarith
  exact ⟨hu, by linarith, herror⟩

end Erdos421
