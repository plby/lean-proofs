import ErdosProblems.Erdos421.ZetaDiskGrowth
import ErdosProblems.Erdos421.ZetaZeroExclusion

/-! # A zero-exclusion criterion from the proved growth envelope

The final theorem has only numerical hypotheses on its parameters. The
analytic disk bounds, local factorization, and pole estimate are all supplied
by proved results. Optimizing its parameters to obtain the prime-weighted
estimate required by the main problem is not asserted here.
-/

namespace Erdos421

open Complex Metric

theorem riemannZeta_norm_relative_to_center {s c : ℂ} {M : ℝ}
    (hc : 1 < c.re) (hM : 0 ≤ M) (hs : ‖riemannZeta s‖ ≤ M) :
    ‖riemannZeta s‖ ≤ M * (1 + 1 / (c.re - 1)) * ‖riemannZeta c‖ := by
  have hn : riemannZeta c ≠ 0 := riemannZeta_ne_zero_of_one_le_re hc.le
  have hq := norm_inv_riemannZeta_right_halfPlane_le hc
  have hunit : 1 ≤ (1 + 1 / (c.re - 1)) * ‖riemannZeta c‖ := by
    have h := mul_le_mul_of_nonneg_right hq (norm_nonneg (riemannZeta c))
    rwa [← norm_mul, inv_mul_cancel₀ hn, norm_one] at h
  calc
    ‖riemannZeta s‖ ≤ M := hs
    _ ≤ M * ((1 + 1 / (c.re - 1)) * ‖riemannZeta c‖) :=
      le_mul_of_one_le_right hM hunit
    _ = _ := by ring

theorem riemannZeta_two_disks_norm_bound (r K : ℕ) (hK : 2 * r + 4 ≤ K) (hK8 : 8 ≤ K)
    {R A u t v : ℝ} (hR : 0 < R) (hRD : R ≤ logarithmicSavingExponent r K / 2)
    (hu : 0 < u) (hlo : (2 : ℝ) ^ (r + 1) + R ≤ |t|)
    (hvlo : |t| ≤ |v|) (hvhi : |v| ≤ 2 * |t|)
    (hexp : zetaStripEnvelope r K R (2 * |t| + R) * (1 + 1 / u) ≤ Real.exp A) :
    ∀ z ∈ sphere (0 : ℂ) R,
      ‖riemannZeta (((1 + u : ℝ) : ℂ) + v * I + z)‖ ≤
        Real.exp A * ‖riemannZeta (((1 + u : ℝ) : ℂ) + v * I)‖ := by
  have hbase : (1 : ℝ) ≤ 2 ^ (r + 1) := one_le_pow₀ (by norm_num)
  have hT : 1 ≤ 2 * |t| + R := by linarith [abs_nonneg t]
  have hM := (zetaStripEnvelope_pos r K R hT).le
  have hc : 1 < (((1 + u : ℝ) : ℂ) + v * I).re := by simp; linarith
  have hc0 : 1 ≤ (((1 + u : ℝ) : ℂ) + v * I).re := hc.le
  have hlow : (2 : ℝ) ^ (r + 1) + R ≤ |(((1 + u : ℝ) : ℂ) + v * I).im| := by
    simpa using hlo.trans hvlo
  have hhigh : |(((1 + u : ℝ) : ℂ) + v * I).im| + R ≤ 2 * |t| + R := by
    simpa using add_le_add hvhi (le_refl R)
  intro z hz
  have hb := riemannZeta_disk_envelope r K hK hK8 hR.le hRD hc0 hlow hhigh
    (sphere_subset_closedBall hz)
  have hrel : ‖riemannZeta (((1 + u : ℝ) : ℂ) + v * I + z)‖ ≤
      (zetaStripEnvelope r K R (2 * |t| + R) * (1 + 1 / u)) *
        ‖riemannZeta (((1 + u : ℝ) : ℂ) + v * I)‖ := by
    simpa using riemannZeta_norm_relative_to_center hc hM hb
  exact hrel.trans (mul_le_mul_of_nonneg_right hexp (norm_nonneg _))

/-- A quantitative nonvanishing result with no unproved analytic inputs.
`B` and `r₀` are fixed constants obtained from the proved local pole estimate. -/
theorem exists_riemannZeta_growth_zero_exclusion :
    ∃ B > 0, ∃ r₀ > 0, ∀ r K : ℕ, 2 * r + 4 ≤ K → 8 ≤ K →
      ∀ R A t β : ℝ, 0 < R → R ≤ logarithmicSavingExponent r K / 2 → 0 < A →
        (2 : ℝ) ^ (r + 1) + R ≤ |t| →
        let u := R / (100 * (A + B * R + 1))
        u < r₀ → zetaStripEnvelope r K R (2 * |t| + R) * (1 + 1 / u) ≤ Real.exp A →
          1 - u / 10 ≤ β → riemannZeta ((β : ℂ) + t * I) ≠ 0 := by
  obtain ⟨B, hB, r₀, hr₀, hpole⟩ := exists_riemannZeta_logDeriv_pole_bound
  refine ⟨B, hB, r₀, hr₀, ?_⟩
  intro r K hK hK8 R A t β hR hRD hA hlo
  let u := R / (100 * (A + B * R + 1))
  change u < r₀ → _
  intro hur hexp hβ
  obtain ⟨hu, huR, he⟩ := zeta_zero_detection_scale hR hA hB.le
  have hpu : -(logDeriv riemannZeta ((1 + u : ℝ) : ℂ)).re ≤ 1 / u + B := by
    simpa only [add_sub_cancel_left] using
      hpole (1 + u) (by linarith : 1 < 1 + u) (by linarith : 1 + u < 1 + r₀)
  have ht : R < |t| := by
    have hpos : (0 : ℝ) < 2 ^ (r + 1) := by positivity
    linarith only [hlo, hpos]
  apply riemannZeta_ne_zero_of_disk_norm_bounds hu huR hA ht hpu he
  · exact riemannZeta_two_disks_norm_bound r K hK hK8 hR hRD hu hlo le_rfl
      (by linarith [abs_nonneg t]) hexp
  · exact riemannZeta_two_disks_norm_bound r K hK hK8 hR hRD hu hlo
      (by rw [abs_mul]; norm_num; linarith [abs_nonneg t])
      (by rw [abs_mul]; norm_num) hexp
  · exact hβ

end Erdos421
