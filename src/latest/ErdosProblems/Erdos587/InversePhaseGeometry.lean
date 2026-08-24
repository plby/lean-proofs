import ErdosProblems.Erdos587.FirstDerivativeSum

/-! The inverse phase increment on one interval between consecutive integers. -/

namespace Erdos587

lemma nearestIntDist_lower_on_unit_strip {δ x : ℝ} (hδ : 0 ≤ δ)
    (hxlo : δ ≤ x) (hxhi : x ≤ 1 - δ) : δ ≤ nearestIntDist x := by
  have hx0 : 0 ≤ x := hδ.trans hxlo
  have hx1 : x ≤ 1 := by linarith
  have hrange := abs_le.mp (abs_sub_round x)
  have hr0 : (0 : ℤ) ≤ round x := by
    have hh : (-1 : ℝ) < (round x : ℝ) := by linarith [hrange.2]
    have hh' : (-1 : ℤ) < round x := by exact_mod_cast hh
    omega
  have hr1 : round x ≤ (1 : ℤ) := by
    have hh : (round x : ℝ) < 2 := by linarith [hrange.1]
    have hh' : round x < (2 : ℤ) := by exact_mod_cast hh
    omega
  have hr : round x = 0 ∨ round x = 1 := by omega
  rcases hr with hr | hr
  · simp only [nearestIntDist, hr, Int.cast_zero, sub_zero, abs_of_nonneg hx0]
    exact hxlo
  · simp only [nearestIntDist, hr, Int.cast_one, abs_of_nonpos (sub_nonpos.mpr hx1)]
    linarith

lemma inverse_phase_increment_norm_bound {δ x : ℝ} (hδ : 0 < δ)
    (hxlo : δ ≤ x) (hxhi : x ≤ 1 - δ) :
    phase x ≠ 1 ∧ ‖(phase x - 1)⁻¹‖ ≤ 1 / (4 * δ) := by
  have hd := nearestIntDist_lower_on_unit_strip hδ.le hxlo hxhi
  have hchord : 4 * δ ≤ ‖phase x - 1‖ :=
    (mul_le_mul_of_nonneg_left hd (by norm_num)).trans
      (four_mul_nearestIntDist_le_norm_fourierChar_sub_one x)
  have hn : 0 < ‖phase x - 1‖ := lt_of_lt_of_le (by positivity) hchord
  refine ⟨sub_ne_zero.mp (norm_pos_iff.mp hn), ?_⟩
  rw [norm_inv, ← one_div]
  exact one_div_le_one_div_of_le (by positivity) hchord

lemma inverse_unit_sub_one_re {z : ℂ} (hz : ‖z‖ = 1) (hne : z ≠ 1) :
    ((z - 1)⁻¹).re = -(1 / 2 : ℝ) := by
  have hnorm : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hz]; norm_num
  have hd : Complex.normSq (z - 1) ≠ 0 := by
    intro hh
    exact sub_ne_zero.mpr hne (Complex.normSq_eq_zero.mp hh)
  rw [Complex.inv_re, div_eq_iff hd]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, sub_zero] at hnorm ⊢
  nlinarith

lemma phase_re_im (x : ℝ) :
    (phase x).re = Real.cos (2 * Real.pi * x) ∧
      (phase x).im = Real.sin (2 * Real.pi * x) := by
  simp [phase, Real.fourierChar_apply, Complex.exp_re, Complex.exp_im]

lemma normSq_phase_sub_one (x : ℝ) :
    Complex.normSq (phase x - 1) = 4 * Real.sin (Real.pi * x) ^ 2 := by
  obtain ⟨hre, him⟩ := phase_re_im x
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, sub_zero, hre, him]
  have hcos := Real.cos_two_mul (Real.pi * x)
  have hsq := Real.sin_sq_add_cos_sq (2 * Real.pi * x)
  have hsq' := Real.sin_sq_add_cos_sq (Real.pi * x)
  rw [show 2 * (Real.pi * x) = 2 * Real.pi * x by ring] at hcos
  nlinarith

lemma inverse_phase_increment_im {x : ℝ} (hx : Real.sin (Real.pi * x) ≠ 0) :
    ((phase x - 1)⁻¹).im = -Real.cos (Real.pi * x) / (2 * Real.sin (Real.pi * x)) := by
  rw [Complex.inv_im, normSq_phase_sub_one, Complex.sub_im, Complex.one_im, sub_zero,
    (phase_re_im x).2, show 2 * Real.pi * x = 2 * (Real.pi * x) by ring, Real.sin_two_mul]
  field_simp
  ring

lemma sin_pi_mul_pos_of_mem_unit_interval {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    0 < Real.sin (Real.pi * x) := by
  apply Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hx.1)
  nlinarith [Real.pi_pos, hx.2]

lemma hasDerivAt_neg_half_cot {x : ℝ} (hx : Real.sin (Real.pi * x) ≠ 0) :
    HasDerivAt (fun y : ℝ => -Real.cos (Real.pi * y) / (2 * Real.sin (Real.pi * y)))
      (Real.pi / (2 * Real.sin (Real.pi * x) ^ 2)) x := by
  have ha : HasDerivAt (fun y : ℝ => Real.pi * y) Real.pi x := hasDerivAt_const_mul _
  have hh := ha.cos.neg.div (ha.sin.const_mul 2) (mul_ne_zero (by norm_num) hx)
  apply hh.congr_deriv
  simp only [Pi.neg_apply]
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi * x)]

theorem monotoneOn_inverse_phase_increment_im :
    MonotoneOn (fun x : ℝ => ((phase x - 1)⁻¹).im) (Set.Ioo 0 1) := by
  let ψ (x : ℝ) := -Real.cos (Real.pi * x) / (2 * Real.sin (Real.pi * x))
  have hderiv (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
      HasDerivAt ψ (Real.pi / (2 * Real.sin (Real.pi * x) ^ 2)) x :=
    hasDerivAt_neg_half_cot (sin_pi_mul_pos_of_mem_unit_interval hx).ne'
  have hcont : ContinuousOn ψ (Set.Ioo (0 : ℝ) 1) :=
    fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn ψ (Set.Ioo (0 : ℝ) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo 0 1) hcont
    intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := interior_subset hx
    rw [(hderiv x hx').deriv]
    exact div_pos Real.pi_pos (mul_pos (by norm_num)
      (sq_pos_of_pos (sin_pi_mul_pos_of_mem_unit_interval hx')))
  intro x hx y hy hxy
  change ((phase x - 1)⁻¹).im ≤ ((phase y - 1)⁻¹).im
  rw [inverse_phase_increment_im (sin_pi_mul_pos_of_mem_unit_interval hx).ne',
    inverse_phase_increment_im (sin_pi_mul_pos_of_mem_unit_interval hy).ne']
  exact hmono.monotoneOn hx hy hxy

end Erdos587
