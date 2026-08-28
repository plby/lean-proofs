import Wikipedia.HopfProblem.RiemannBoundaryIdeal

/-!
# Exact exponential and logarithmic half-strip coordinates

These formulas identify the logarithmic coordinate used at an ideal
triangle vertex with the actual exponential parameter, including its
horizontal period and its upper-half-plane image.
-/

noncomputable section

open Complex Filter Metric Set
open scoped Topology

namespace Wikipedia.HopfProblem.RiemannBoundary

/-- The exponential parameter inverse to `logHalfStrip` on its strip. -/
def halfStripExp (a c : ℝ) (z : ℂ) : ℂ := exp (I * (z - a) / c)

theorem halfStripExp_logHalfStrip (a : ℝ) {c : ℝ} (hc : c ≠ 0)
    {q : ℂ} (hq : q ≠ 0) : halfStripExp a c (logHalfStrip a c q) = q := by
  have hcC : (c : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc
  have he : I * (logHalfStrip a c q - a) / c = log q := by
    unfold logHalfStrip
    field_simp
    ring_nf
    simp
  rw [halfStripExp, he, exp_log hq]

theorem logHalfStrip_halfStripExp (a : ℝ) {c : ℝ} (hc : 0 < c) {z : ℂ}
    (hz : z.re ∈ Ioo a (a + c * Real.pi)) :
    logHalfStrip a c (halfStripExp a c z) = z := by
  have hcC : (c : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc.ne'
  have him : (I * (z - a) / c).im = (z.re - a) / c := by simp
  have hpos : 0 < (I * (z - a) / c).im := by
    rw [him]
    exact div_pos (sub_pos.mpr hz.1) hc
  have hpi : (I * (z - a) / c).im < Real.pi := by
    rw [him, div_lt_iff₀ hc]
    linarith [hz.2]
  rw [logHalfStrip, halfStripExp, log_exp (by linarith [Real.pi_pos]) hpi.le]
  field_simp
  ring_nf
  simp

@[simp] theorem norm_halfStripExp (a c : ℝ) (z : ℂ) :
    ‖halfStripExp a c z‖ = Real.exp (-z.im / c) := by
  simp [halfStripExp, norm_exp]

theorem halfStripExp_im_pos (a : ℝ) {c : ℝ} (hc : 0 < c) {z : ℂ}
    (hz : z.re ∈ Ioo a (a + c * Real.pi)) : 0 < (halfStripExp a c z).im := by
  rw [halfStripExp, exp_im]
  apply mul_pos (Real.exp_pos _)
  apply Real.sin_pos_of_pos_of_lt_pi
  · simp only [div_ofReal_im, mul_im, I_re, sub_im, ofReal_im, zero_mul,
      I_im, sub_re, ofReal_re, one_mul, zero_add]
    exact div_pos (sub_pos.mpr hz.1) hc
  · simp only [div_ofReal_im, mul_im, I_re, sub_im, ofReal_im, zero_mul,
      I_im, sub_re, ofReal_re, one_mul, zero_add]
    rw [div_lt_iff₀ hc]
    linarith [hz.2]

/-- The exponential coordinate has the horizontal period of the full
reflected strip, twice the width of the original half-strip. -/
theorem halfStripExp_add_period (a : ℝ) {c : ℝ} (hc : c ≠ 0) (z : ℂ) :
    halfStripExp a c (z + (2 * c * Real.pi : ℝ)) = halfStripExp a c z := by
  have hcC : (c : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc
  have he : I * (z + (2 * c * Real.pi : ℝ) - a) / c =
      I * (z - a) / c + 2 * Real.pi * I := by
    push_cast
    field_simp
    ring
  rw [halfStripExp, he, exp_periodic]
  rfl

end Wikipedia.HopfProblem.RiemannBoundary
