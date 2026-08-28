import Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductTrace

/-! # The unique closed-unit-disk solution of the selected trace equation -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

def traceRoot : ℂ := ⟨-(Real.sqrt 2 / 2), 1 - Real.sqrt 2 / 2⟩

theorem trace_equation_unique (v : ℂ) (hv : ‖v‖ ≤ 1)
    (he : v ^ 2 + 2 * star v = -1 - Complex.I) : v = traceRoot := by
  have hs : (Real.sqrt (2 : ℝ) / 2) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hspos : 0 < Real.sqrt (2 : ℝ) / 2 := by positivity
  have hnorm : v.re ^ 2 + v.im ^ 2 ≤ 1 := by
    have hn : ‖v‖ ^ 2 ≤ (1 : ℝ) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg v) zero_le_one).mpr hv
    rw [Complex.sq_norm, Complex.normSq_apply] at hn
    nlinarith [hn]
  have hr := congrArg Complex.re he
  have hi := congrArg Complex.im he
  norm_num [pow_two, Complex.mul_re, Complex.mul_im, Complex.star_def] at hr hi
  have hp : (v.re + 1 - v.im) * (v.re + 1 + v.im) = 0 := by nlinarith [hr]
  rcases mul_eq_zero.mp hp with hplus | hminus
  · have hy : v.im = v.re + 1 := by linarith
    have hx2 : v.re ^ 2 = 1 / 2 := by nlinarith [hi]
    have hx0 : v.re ≤ 0 := by nlinarith [hnorm]
    have hx : -v.re = Real.sqrt 2 / 2 :=
      (sq_eq_sq₀ (neg_nonneg.mpr hx0) (le_of_lt hspos)).mp (by nlinarith [hx2, hs])
    apply Complex.ext
    · change v.re = -(Real.sqrt 2 / 2)
      linarith
    · change v.im = 1 - Real.sqrt 2 / 2
      linarith
  · have hy : v.im = -(v.re + 1) := by linarith
    nlinarith [hi, hnorm, sq_nonneg v.im]

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
