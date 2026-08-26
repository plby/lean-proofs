import ErdosProblems.Erdos421.ZeroDetector
import ErdosProblems.Erdos421.ZetaLogDerivativePositivity
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! # Applying the local zero detector to the Riemann zeta function -/

namespace Erdos421

open Complex Filter Metric Topology

theorem logDeriv_translate (f : ℂ → ℂ) (c : ℂ) :
    logDeriv (fun z ↦ f (c + z)) 0 = logDeriv f c := by
  simp only [logDeriv_apply, deriv_comp_const_add, add_zero]

theorem analyticOnNhd_riemannZeta_disk {c : ℂ} {R : ℝ} (hsep : R < ‖c - 1‖) :
    AnalyticOnNhd ℂ (fun z ↦ riemannZeta (c + z)) (closedBall 0 R) := by
  intro z hz
  have hn : c + z ≠ 1 := by
    intro he
    have he' : c - 1 = -z := by linear_combination he
    rw [he', norm_neg] at hsep
    exact (not_lt_of_ge (mem_closedBall_zero_iff.mp hz)) hsep
  exact (analyticOn_riemannZeta (c + z) hn).comp (by fun_prop)

theorem riemannZeta_disk_zeros_re_nonpos {c : ℂ} (hc : 1 < c.re) (R : ℝ) :
    ∀ z ∈ ball (0 : ℂ) R, riemannZeta (c + z) = 0 → z.re ≤ 0 := by
  intro z _ hz
  by_contra! hp
  have hlarge : 1 ≤ (c + z).re := by simp only [Complex.add_re]; linarith
  exact riemannZeta_ne_zero_of_one_le_re hlarge hz

theorem riemannZeta_logDeriv_re_lower_bound {c : ℂ} {R A : ℝ}
    (hc : 1 < c.re) (hR : 0 < R) (hA : 0 < A) (hsep : R < ‖c - 1‖)
    (hM : ∀ z ∈ sphere 0 R, ‖riemannZeta (c + z)‖ ≤ Real.exp A * ‖riemannZeta c‖) :
    -(4 * A / R) ≤ (logDeriv riemannZeta c).re := by
  have hf0 : riemannZeta (c + 0) ≠ 0 := by
    simpa only [add_zero] using riemannZeta_ne_zero_of_one_le_re hc.le
  have hb := logDeriv_re_lower_bound hR hA (analyticOnNhd_riemannZeta_disk hsep)
    hf0 (by simpa only [add_zero] using hM) (riemannZeta_disk_zeros_re_nonpos hc R)
  rwa [logDeriv_translate] at hb

theorem riemannZeta_zero_reciprocal_bound {c : ℂ} {R A d : ℝ}
    (hc : 1 < c.re) (hR : 0 < R) (hA : 0 < A) (hsep : R < ‖c - 1‖)
    (hM : ∀ z ∈ sphere 0 R, ‖riemannZeta (c + z)‖ ≤ Real.exp A * ‖riemannZeta c‖)
    (hd : 0 < d) (hdR : d < R) (hz : riemannZeta (c - d) = 0) :
    1 / d - d / R ^ 2 ≤ (logDeriv riemannZeta c).re + 4 * A / R := by
  have hf0 : riemannZeta (c + 0) ≠ 0 := by
    simpa only [add_zero] using riemannZeta_ne_zero_of_one_le_re hc.le
  have hb := real_zero_reciprocal_bound hR hA (analyticOnNhd_riemannZeta_disk hsep)
    hf0 (by simpa only [add_zero] using hM) (riemannZeta_disk_zeros_re_nonpos hc R)
    hd hdR (by simpa only [sub_eq_add_neg] using hz)
  rwa [logDeriv_translate] at hb

theorem riemannZeta_zero_three_four_one_bound {σ t R A d : ℝ}
    (hσ : 1 < σ) (hR : 0 < R) (hA : 0 < A) (ht : R < |t|)
    (hM1 : ∀ z ∈ sphere (0 : ℂ) R,
      ‖riemannZeta ((σ : ℂ) + t * I + z)‖ ≤
        Real.exp A * ‖riemannZeta ((σ : ℂ) + t * I)‖)
    (hM2 : ∀ z ∈ sphere (0 : ℂ) R,
      ‖riemannZeta ((σ : ℂ) + (2 * t : ℝ) * I + z)‖ ≤
        Real.exp A * ‖riemannZeta ((σ : ℂ) + (2 * t : ℝ) * I)‖)
    (hd : 0 < d) (hdR : d < R) (hz : riemannZeta ((σ : ℂ) + t * I - d) = 0) :
    4 / d ≤ -3 * (logDeriv riemannZeta (σ : ℂ)).re + 4 * d / R ^ 2 + 20 * A / R := by
  have hc1 : 1 < ((σ : ℂ) + t * I).re := by simpa using hσ
  have hc2 : 1 < ((σ : ℂ) + (2 * t : ℝ) * I).re := by simpa using hσ
  have hs1 : R < ‖(σ : ℂ) + t * I - 1‖ := by
    exact ht.trans_le (by simpa using Complex.abs_im_le_norm ((σ : ℂ) + t * I - 1))
  have hs2 : R < ‖(σ : ℂ) + (2 * t : ℝ) * I - 1‖ := by
    have h2 : R < |2 * t| := by rw [abs_mul]; norm_num; linarith [abs_nonneg t]
    exact h2.trans_le (by simpa using
      Complex.abs_im_le_norm ((σ : ℂ) + (2 * t : ℝ) * I - 1))
  have h1 := riemannZeta_zero_reciprocal_bound hc1 hR hA hs1 hM1 hd hdR hz
  have h2 := riemannZeta_logDeriv_re_lower_bound hc2 hR hA hs2 hM2
  have h3 := riemannZeta_logDeriv_trigonometric_bound hσ t
  ring_nf at h1 h2 h3 ⊢
  linarith only [h1, h2, h3]

theorem exists_riemannZeta_logDeriv_pole_bound :
    ∃ B > 0, ∃ r > 0, ∀ σ : ℝ, 1 < σ → σ < 1 + r →
      -(logDeriv riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + B := by
  obtain ⟨B, hB, hb⟩ := log_deriv_riemannZeta_add_inv_sub_bounded.exists_pos
  have hnear : ∀ᶠ s in 𝓝[≠] (1 : ℂ),
      ‖logDeriv riemannZeta s + (s - 1)⁻¹‖ ≤ B := by
    simpa only [logDeriv_apply, norm_one, mul_one] using hb.bound
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhdsWithin_iff.mp hnear
  refine ⟨B, hB, r, hr, ?_⟩
  intro σ hσ hσr
  have hsball : (σ : ℂ) ∈ ball 1 r := by
    rw [mem_ball, dist_eq_norm, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hσ)]
    linarith
  have hsne : (σ : ℂ) ≠ 1 := by
    intro he
    have he' := congrArg Complex.re he
    simp only [Complex.ofReal_re, Complex.one_re] at he'
    linarith
  have hn := hball ⟨hsball, hsne⟩
  have hre := (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans hn)
  have he : ((σ : ℂ) - 1)⁻¹.re = 1 / (σ - 1) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_inv,
      Complex.ofReal_re, one_div]
  rw [Complex.add_re, he] at hre
  linarith

end Erdos421
