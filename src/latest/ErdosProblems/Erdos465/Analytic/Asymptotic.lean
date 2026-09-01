/-
This analytic helper is adapted from the fully proved Q776 development at
https://github.com/l-pommeret/rms-math-proofs, revision
a5c24c8190191bc9491259035073a9230b9f6727, for Lean/Mathlib v4.33.0.
-/

import ErdosProblems.Erdos465.Analytic.Bessel

/-!
# Q776 — the stationary phase expansion of `f 2` on the negative axis

We assemble the pieces built in the previous modules into the two–term stationary phase
expansion of `J₀`, hence of `f 2 (-R²)`.

The route is:

* `besselJ0_eq_re` writes `J₀ y` as the real part of `∫_{-π}^{π} exp (i y cos t) dt`;
* `circle_decomp` splits that integral with the partition `chiA + chiB + psi`;
* `BB_eq` identifies the contribution of the saddle `t = π` with `AA (-y)`;
* `AA_eq` performs the exact change of variables `u = 2 sin (t/2)`, turning the
  contribution of the saddle `t = 0` into the model integral `Iof (i y/2) Gfun`;
* `model_expansion` supplies the two-term expansion of the model integral.
-/

open scoped Real
open Complex MeasureTheory intervalIntegral

namespace Q776

/-- The order-zero Bessel kernel in Hansen's real integral form. -/
noncomputable def besselJ0 (y : ℝ) : ℝ :=
  1 / (2 * Real.pi) * ∫ θ in (-Real.pi)..Real.pi, Real.cos (y * Real.sin θ)

/-! ## Periodicity bookkeeping -/

theorem periodic_shift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → E} (hp : Function.Periodic F (2 * π)) (a : ℝ) :
    (∫ t in a..(a + 2*π), F t) = ∫ t in (-π)..π, F t := by
  have h := hp.intervalIntegral_add_eq a (-π)
  rw [h]; ring_nf

theorem chiA_periodic : Function.Periodic chiA (2*π) := by
  intro t
  simp only [chiA, show (t + 2*π)/2 = t/2 + π by ring, Real.sin_add_pi]
  rw [show 2 * -Real.sin (t/2) = -(2*Real.sin (t/2)) by ring, cutoff_even]

theorem osc_periodic (y : ℝ) : Function.Periodic (osc y) (2*π) := by
  intro t; simp [osc, Real.cos_add_two_pi]

theorem chiB_eq_chiA_pi_sub (x : ℝ) : chiB (π - x) = chiA x := by
  simp only [chiB, chiA, show (π - x)/2 = π/2 - x/2 by ring, Real.cos_pi_div_two_sub]

theorem osc_pi_sub (y x : ℝ) : osc y (π - x) = osc (-y) x := by
  simp only [osc, Real.cos_pi_sub]
  congr 1
  push_cast
  ring

/-! ## The Bessel function as a real part -/

theorem besselJ0_eq_re (y : ℝ) :
    besselJ0 y = 1/(2*π) * (∫ t in (-π)..π, osc y t).re := by
  have hre : (∫ t in (-π)..π, osc y t).re = ∫ t in (-π)..π, (osc y t).re := by
    rw [← Complex.reCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm]
    · rfl
    · exact ((continuous_osc y).intervalIntegrable _ _)
  have hpt : ∀ t : ℝ, (osc y t).re = Real.cos (y * Real.cos t) := by
    intro t
    rw [osc]
    rw [show Complex.I * (y:ℂ) * (Real.cos t : ℂ) = ((y * Real.cos t : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    exact Complex.exp_ofReal_mul_I_re _
  have hG : Function.Periodic (fun θ : ℝ => Real.cos (y * Real.sin θ)) (2*π) := by
    intro θ; simp [Real.sin_add_two_pi]
  have hshift : (∫ t in (-π)..π, Real.cos (y * Real.cos t))
      = ∫ θ in (-π)..π, Real.cos (y * Real.sin θ) := by
    have e1 : ∀ t : ℝ, Real.cos (y * Real.cos t)
        = (fun θ : ℝ => Real.cos (y * Real.sin θ)) (t - π/2) := by
      intro t
      simp [Real.sin_sub, Real.sin_pi_div_two, Real.cos_pi_div_two]
    rw [intervalIntegral.integral_congr
      (g := fun t => (fun θ : ℝ => Real.cos (y * Real.sin θ)) (t - π/2)) (fun t _ => e1 t)]
    rw [intervalIntegral.integral_comp_sub_right (fun θ : ℝ => Real.cos (y * Real.sin θ)) (π/2)]
    rw [show (π:ℝ) - π/2 = -π - π/2 + 2*π from by ring]
    exact periodic_shift hG (-π - π/2)
  rw [besselJ0, ← hshift, hre]
  simp only [hpt]

/-! ## The partition of the circle integral -/

/-- The localized integral at the stationary point `t = 0`. -/
noncomputable def AA (y : ℝ) : ℂ := ∫ t in (-π)..π, osc y t * (chiA t : ℂ)

theorem BB_eq (y : ℝ) : (∫ t in (-π)..π, osc y t * (chiB t : ℂ)) = AA (-y) := by
  have h := intervalIntegral.integral_comp_sub_left
    (f := fun t : ℝ => osc y t * (chiB t : ℂ)) (a := (0:ℝ)) (b := 2*π) π
  rw [show π - 2*π = -π from by ring, sub_zero] at h
  rw [← h]
  have e : ∀ x : ℝ, osc y (π - x) * ((chiB (π - x) : ℝ) : ℂ) = osc (-y) x * (chiA x : ℂ) := by
    intro x; rw [osc_pi_sub, chiB_eq_chiA_pi_sub]
  rw [intervalIntegral.integral_congr (fun x _ => e x)]
  have hp : Function.Periodic (fun x : ℝ => osc (-y) x * (chiA x : ℂ)) (2*π) := by
    intro x
    simp only [osc_periodic (-y) x, chiA_periodic x]
  rw [AA, ← periodic_shift hp 0]
  simp

theorem circle_decomp (y : ℝ) :
    (∫ t in (-π)..π, osc y t)
      = AA y + AA (-y) + ∫ t in (-π)..π, osc y t * (psi t : ℂ) := by
  have hA : Continuous fun t : ℝ => osc y t * (chiA t : ℂ) :=
    (continuous_osc y).mul (Complex.continuous_ofReal.comp chiA_smooth.continuous)
  have hB : Continuous fun t : ℝ => osc y t * (chiB t : ℂ) :=
    (continuous_osc y).mul (Complex.continuous_ofReal.comp chiB_smooth.continuous)
  have hP : Continuous fun t : ℝ => osc y t * (psi t : ℂ) :=
    (continuous_osc y).mul (Complex.continuous_ofReal.comp psi_smooth.continuous)
  have hAB : IntervalIntegrable
      (fun t : ℝ => osc y t * (chiA t : ℂ) + osc y t * (chiB t : ℂ)) volume (-π) π :=
    ((hA.add hB).intervalIntegrable _ _)
  rw [← BB_eq, AA,
    ← intervalIntegral.integral_add (hA.intervalIntegrable _ _) (hB.intervalIntegrable _ _),
    ← intervalIntegral.integral_add hAB (hP.intervalIntegrable _ _)]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  have hsum : (chiA t : ℂ) + (chiB t : ℂ) + (psi t : ℂ) = 1 := by
    have h : psi t = 1 - chiA t - chiB t := rfl
    rw [h]; push_cast; ring
  linear_combination (-(osc y t)) * hsum

/-! ## The change of variables at the saddle `t = 0` -/

theorem AA_restrict (y : ℝ) : AA y = ∫ t in (-(π/2))..(π/2), osc y t * (chiA t : ℂ) := by
  have hc : Continuous fun t : ℝ => osc y t * (chiA t : ℂ) :=
    (continuous_osc y).mul (Complex.continuous_ofReal.comp chiA_smooth.continuous)
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun t : ℝ => osc y t * (chiA t : ℂ)) volume a b :=
    fun a b => hc.intervalIntegrable a b
  have hz : ∀ t : ℝ, Real.cos t ≤ 0 → osc y t * (chiA t : ℂ) = 0 := by
    intro t ht; rw [chiA_zero_of_cos_nonpos ht]; simp
  have h1 : (∫ t in (-π)..(-(π/2)), osc y t * (chiA t : ℂ)) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℂ)) ?_]
    · simp
    · intro t ht
      rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at ht
      refine hz t ?_
      rw [← Real.cos_neg]
      exact Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith [ht.2])
        (by linarith [ht.1, Real.pi_pos])
  have h2 : (∫ t in (π/2)..π, osc y t * (chiA t : ℂ)) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℂ)) ?_]
    · simp
    · intro t ht
      rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at ht
      exact hz t (Real.cos_nonpos_of_pi_div_two_le_of_le ht.1 (by linarith [ht.2, Real.pi_pos]))
  have e1 := intervalIntegral.integral_add_adjacent_intervals (hi (-π) (-(π/2)))
    (hi (-(π/2)) (π/2))
  have e2 := intervalIntegral.integral_add_adjacent_intervals (hi (-π) (π/2)) (hi (π/2) π)
  rw [AA, ← e2, ← e1, h1, h2]
  ring

/-- The exact Jacobian identity of the change of variables `u = 2 sin (t/2)`. -/
theorem cos_half_mul_amp {t : ℝ} (ht : |t| ≤ π / 2) :
    Real.cos (t/2) * amp (2 * Real.sin (t/2)) = 1 := by
  have habs : |t/2| ≤ π/4 := by rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]; linarith
  have hc : 0 < Real.cos (t/2) := by
    have h1 := abs_le.1 habs
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, h1.1], by linarith [Real.pi_pos, h1.2]⟩
  have hsr : sroot (2 * Real.sin (t/2)) = Real.cos (t/2) := by
    rw [sroot, show 1 - (2*Real.sin (t/2))^2/4 = (Real.cos (t/2))^2 by
      nlinarith [Real.sin_sq_add_cos_sq (t/2)]]
    exact Real.sqrt_sq hc.le
  rw [amp, hsr]
  field_simp

/-- **The exact reduction to the model integral.** -/
theorem AA_eq (y : ℝ) : AA y = Complex.exp (Complex.I * y) * Iof (Complex.I * y / 2) Gfun := by
  set g : ℝ → ℂ := fun u => Complex.exp (Complex.I * y) *
    (Complex.exp (-(Complex.I * y / 2) * (u:ℂ)^2) * (Gfun u : ℂ)) with hg
  have hgc : Continuous g := by
    refine continuous_const.mul (Continuous.mul ?_ ?_)
    · exact (Complex.continuous_exp.comp (by fun_prop))
    · exact Complex.continuous_ofReal.comp csfun_Gfun.smooth.continuous
  have hderiv : ∀ x ∈ Set.uIcc (-(π/2)) (π/2),
      HasDerivAt (fun t : ℝ => 2 * Real.sin (t/2)) (Real.cos (x/2)) x := by
    intro x _
    have h := ((Real.hasDerivAt_sin (x/2)).comp x ((hasDerivAt_id x).div_const 2)).const_mul (2:ℝ)
    simpa using h.congr_deriv (by ring)
  have hcv := intervalIntegral.integral_deriv_smul_comp (a := -(π/2)) (b := π/2)
    (f := fun t : ℝ => 2 * Real.sin (t/2)) (f' := fun t : ℝ => Real.cos (t/2)) (g := g)
    hderiv (Real.continuous_cos.comp (continuous_id.div_const 2)).continuousOn hgc
  have hsq : Real.sin (π/4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
  have hep : (fun t : ℝ => 2 * Real.sin (t/2)) (π/2) = Real.sqrt 2 := by
    simp only [show (π/2)/2 = π/4 by ring, hsq]; ring
  have hem : (fun t : ℝ => 2 * Real.sin (t/2)) (-(π/2)) = -Real.sqrt 2 := by
    simp only [show (-(π/2))/2 = -(π/4) by ring, Real.sin_neg, hsq]; ring
  change _ = ∫ x in (fun t : ℝ ↦ 2 * Real.sin (t/2)) (-(π/2))..
    (fun t : ℝ ↦ 2 * Real.sin (t/2)) (π/2), g x at hcv
  rw [hep, hem] at hcv
  have hlhs : ∀ t ∈ Set.uIcc (-(π/2)) (π/2),
      osc y t * (chiA t : ℂ) = Real.cos (t/2) • (g ∘ (fun s : ℝ => 2 * Real.sin (s/2))) t := by
    intro t ht
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at ht
    have htabs : |t| ≤ π/2 := abs_le.2 ⟨ht.1, ht.2⟩
    have hkey : Real.cos (t/2) * amp (2 * Real.sin (t/2)) = 1 := cos_half_mul_amp htabs
    have hG : (Real.cos (t/2) : ℝ) * Gfun (2 * Real.sin (t/2)) = chiA t := by
      rw [Gfun, chiA]
      rw [show cutoff (2*Real.sin (t/2)) * amp (2*Real.sin (t/2))
          = amp (2*Real.sin (t/2)) * cutoff (2*Real.sin (t/2)) by ring, ← mul_assoc, hkey, one_mul]
    have hcos : Complex.exp (Complex.I * y) *
        Complex.exp (-(Complex.I * y / 2) * ((2 * Real.sin (t/2) : ℝ):ℂ)^2) = osc y t := by
      rw [← Complex.exp_add, osc]
      congr 1
      have h2 : (Real.cos t : ℝ) = 1 - 2 * Real.sin (t/2)^2 := by
        have := sin_half_sq t; linarith
      rw [h2]; push_cast; ring
    simp only [Function.comp_apply, hg, Complex.real_smul]
    rw [← hG, Complex.ofReal_mul, ← hcos]
    ring
  rw [AA_restrict, intervalIntegral.integral_congr hlhs, hcv]
  have hsupp : ∀ u : ℝ, (1:ℝ) ≤ |u| → g u = 0 := by
    intro u hu
    simp only [hg, Gfun, cutoff_zero hu]
    simp
  have h1lt : (1:ℝ) < Real.sqrt 2 := by
    have : Real.sqrt 1 < Real.sqrt 2 := by apply Real.sqrt_lt_sqrt <;> norm_num
    simpa using this
  rw [show (-Real.sqrt 2 : ℝ) = -(Real.sqrt 2) from rfl, integral_eq_of_supp h1lt hsupp]
  rw [Iof, ← MeasureTheory.integral_const_mul]

/-- The nonstationary contribution is `O(y^{-3})`. -/
theorem nsfun_psi : NSFun (1/4) (fun t => (psi t : ℂ)) := by
  refine ⟨Complex.ofRealCLM.contDiff.comp psi_smooth, by norm_num, ?_⟩
  intro t ht
  rw [psi_zero_of_sin_small ht]
  simp


/-! ## Explicit evaluation of the square roots on the imaginary axis -/

theorem cpow_half_mul_I {A : ℝ} (hA : 0 < A) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    ((A:ℂ) * (s * Complex.I))^(1/2:ℂ)
      = (Real.sqrt A : ℂ) * Complex.exp (((s * π/4 : ℝ) : ℂ) * Complex.I) := by
  have hsne : s ≠ 0 := by rcases hs with h | h <;> simp [h]
  have hz : ((A:ℂ) * (s * Complex.I)) ≠ 0 := by
    apply mul_ne_zero (Complex.ofReal_ne_zero.2 hA.ne') (mul_ne_zero _ Complex.I_ne_zero)
    exact_mod_cast Complex.ofReal_ne_zero.2 hsne
  rw [Complex.cpow_def_of_ne_zero hz]
  have hnorm : ‖(A:ℂ) * (s * Complex.I)‖ = A := by
    rw [norm_mul, norm_mul]
    simp only [Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_pos hA]
    rcases hs with h | h <;> simp [h]
  have harg : ((A:ℂ) * (s * Complex.I)).arg = s * π/2 := by
    rw [Complex.arg_real_mul _ hA]
    rcases hs with h | h
    · subst h; simp [Complex.arg_I]
    · subst h
      rw [show ((-1:ℝ):ℂ) * Complex.I = -Complex.I by push_cast; ring, Complex.arg_neg_I]
      ring
  have hlog : Complex.log ((A:ℂ) * (s * Complex.I))
      = (Real.log A : ℂ) + (s * π/2 : ℝ) * Complex.I := by
    change (Real.log ‖(A:ℂ) * (s * Complex.I)‖ : ℂ)
      + (((A:ℂ) * (s*Complex.I)).arg : ℝ) * Complex.I = _
    rw [hnorm, harg]
  rw [hlog]
  have hsplit : ((Real.log A : ℂ) + ((s * π/2 : ℝ):ℂ) * Complex.I) * (1/2 : ℂ)
      = ((Real.log (Real.sqrt A) : ℝ) : ℂ) + ((s * π/4 : ℝ):ℂ) * Complex.I := by
    rw [Real.log_sqrt hA.le]; push_cast; ring
  rw [hsplit, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log (Real.sqrt_pos.2 hA)]

/-- The two saddle contributions combine into a real cosine plus its correction. -/
theorem main_sum (y : ℝ) (hy : 0 < y) :
    Complex.exp (Complex.I * y) * ((1 + 1/(16*(Complex.I*y/2))) * ((π:ℂ)/(Complex.I*y/2))^(1/2:ℂ))
    + Complex.exp (Complex.I * (-y:ℝ)) *
        ((1 + 1/(16*(Complex.I*(-y:ℝ)/2))) * ((π:ℂ)/(Complex.I*(-y:ℝ)/2))^(1/2:ℂ))
      = ((2 * Real.sqrt (2*π/y) *
          (Real.cos (y - π/4) + Real.sin (y - π/4)/(8*y)) : ℝ) : ℂ) := by
  have hyc : (y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy.ne'
  have hA : (0:ℝ) < 2*π/y := by positivity
  set S : ℝ := Real.sqrt (2*π/y) with hS
  have e1 : (π:ℂ)/(Complex.I*y/2) = ((2*π/y : ℝ):ℂ) * (((-1:ℝ):ℂ) * Complex.I) := by
    push_cast; field_simp; ring_nf; linear_combination Complex.I_sq
  have e2 : (π:ℂ)/(Complex.I*(-y:ℝ)/2) = ((2*π/y : ℝ):ℂ) * (((1:ℝ):ℂ) * Complex.I) := by
    push_cast; field_simp; ring_nf; linear_combination -Complex.I_sq
  rw [e1, e2, cpow_half_mul_I hA (-1) (Or.inr rfl), cpow_half_mul_I hA 1 (Or.inl rfl)]
  set φ : ℝ := y - π/4 with hφ
  have g1 : Complex.exp (Complex.I * y) * Complex.exp ((((-1:ℝ) * π/4 : ℝ):ℂ) * Complex.I)
      = Complex.exp ((φ:ℂ) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast [hφ]; ring
  have g2 : Complex.exp (Complex.I * (-y:ℝ)) * Complex.exp ((((1:ℝ) * π/4 : ℝ):ℂ) * Complex.I)
      = Complex.exp ((-(φ:ℂ)) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast [hφ]; ring
  have hcp : Complex.exp ((φ:ℂ) * Complex.I) = (Real.cos φ : ℂ) + (Real.sin φ : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  have hcm : Complex.exp ((-(φ:ℂ)) * Complex.I)
      = (Real.cos φ : ℂ) - (Real.sin φ : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg, Complex.ofReal_cos,
      Complex.ofReal_sin]
    ring
  have key : Complex.exp (Complex.I * y) * ((1 + 1/(16*(Complex.I*y/2))) * ((S:ℂ) *
        Complex.exp ((((-1:ℝ) * π/4 : ℝ):ℂ) * Complex.I)))
      + Complex.exp (Complex.I * (-y:ℝ)) * ((1 + 1/(16*(Complex.I*(-y:ℝ)/2))) * ((S:ℂ) *
        Complex.exp ((((1:ℝ) * π/4 : ℝ):ℂ) * Complex.I)))
      = (1 + 1/(16*(Complex.I*y/2))) * (S:ℂ) * Complex.exp ((φ:ℂ) * Complex.I)
        + (1 + 1/(16*(Complex.I*(-y:ℝ)/2))) * (S:ℂ) * Complex.exp ((-(φ:ℂ)) * Complex.I) := by
    rw [← g1, ← g2]; ring
  rw [key, hcp, hcm]
  have hcoef1 : (1 : ℂ) + 1/(16*(Complex.I*y/2)) = 1 - (1/(8*y) : ℝ) * Complex.I := by
    rw [show (16:ℂ)*(Complex.I*y/2) = 8 * Complex.I * y by ring]
    push_cast; field_simp; ring_nf; rw [Complex.I_sq]; ring
  have hcoef2 : (1 : ℂ) + 1/(16*(Complex.I*(-y:ℝ)/2)) = 1 + (1/(8*y) : ℝ) * Complex.I := by
    rw [show (16:ℂ)*(Complex.I*(-y:ℝ)/2) = -(8 * Complex.I * y) by push_cast; ring]
    push_cast; field_simp; ring_nf; rw [Complex.I_sq]; ring
  rw [hcoef1, hcoef2]
  push_cast
  linear_combination (-2 * (S:ℂ) * (1/(8*(y:ℂ))) * Complex.sin (φ:ℂ)) * Complex.I_sq

theorem norm_exp_I_mul (y : ℝ) : ‖Complex.exp (Complex.I * y)‖ = 1 := by
  rw [Complex.norm_exp]; simp [Complex.mul_re]

theorem sqrt_two_pi_div (y : ℝ) (hy : 0 < y) :
    1/(2*π) * (2 * Real.sqrt (2*π/y)) = Real.sqrt (2/(π*y)) := by
  have hpi := Real.pi_pos
  have h : Real.sqrt (2*π/y) = π * Real.sqrt (2/(π*y)) := by
    rw [show π = Real.sqrt (π^2) by rw [Real.sqrt_sq hpi.le], ← Real.sqrt_mul (by positivity),
      Real.sqrt_sq hpi.le]
    congr 1
    field_simp
  rw [h]; field_simp

/-- **Two-term stationary phase expansion of the Bessel function `J₀`.** -/
theorem besselJ0_expansion :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 2 ≤ y →
      |besselJ0 y - Real.sqrt (2/(π*y)) * (Real.cos (y - π/4) + Real.sin (y - π/4)/(8*y))|
        ≤ C / (y^2 * Real.sqrt y) := by
  obtain ⟨C, hC0, hC⟩ := model_expansion
  obtain ⟨K, hK0, hK⟩ := ns_bound nsfun_psi
  refine ⟨1/(2*π) * (16*C + K), by positivity, fun y hy => ?_⟩
  have hpi := Real.pi_pos
  have hy0 : (0:ℝ) < y := by linarith
  have hy1 : (1:ℝ) ≤ y := by linarith
  have hsy : (0:ℝ) < Real.sqrt y := Real.sqrt_pos.2 hy0
  have hnp : ‖Complex.I * (y:ℂ) / 2‖ = y/2 := by
    rw [norm_div, norm_mul]; simp [abs_of_pos hy0]
  have hnm : ‖Complex.I * ((-y:ℝ):ℂ) / 2‖ = y/2 := by
    rw [norm_div, norm_mul]; simp [abs_of_pos hy0]
  have hrp : (0:ℝ) ≤ (Complex.I * (y:ℂ) / 2).re := by simp [Complex.mul_re]
  have hrm : (0:ℝ) ≤ (Complex.I * ((-y:ℝ):ℂ) / 2).re := by simp [Complex.mul_re]
  have h1p : (1:ℝ) ≤ ‖Complex.I * (y:ℂ) / 2‖ := by rw [hnp]; linarith
  have h1m : (1:ℝ) ≤ ‖Complex.I * ((-y:ℝ):ℂ) / 2‖ := by rw [hnm]; linarith
  have hcmp : ∀ D : ℝ, 0 ≤ D → D / ((y/2)^2 * Real.sqrt (y/2)) ≤ 8*D/(y^2 * Real.sqrt y) := by
    intro D hD
    have hs : Real.sqrt y / 2 ≤ Real.sqrt (y/2) := by
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ y/2 by linarith), Real.sqrt_nonneg (y/2),
        Real.sqrt_nonneg y, Real.sq_sqrt hy0.le]
    have hlow : y^2 * Real.sqrt y / 8 ≤ (y/2)^2 * Real.sqrt (y/2) := by
      rw [show (y/2)^2 = y^2/4 by ring]
      nlinarith [Real.sqrt_nonneg y, sq_nonneg y]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [Real.sqrt_nonneg y, sq_nonneg y]
  have hAp : ‖AA y - Complex.exp (Complex.I*(y:ℂ)) *
      ((1 + 1/(16*(Complex.I*(y:ℂ)/2))) * ((π:ℂ)/(Complex.I*(y:ℂ)/2))^(1/2:ℂ))‖
      ≤ 8*C/(y^2*Real.sqrt y) := by
    rw [AA_eq y, ← mul_sub, norm_mul, norm_exp_I_mul, one_mul]
    refine le_trans (hC (Complex.I*(y:ℂ)/2) hrp h1p) ?_
    rw [hnp]; exact hcmp C hC0
  have hAm : ‖AA (-y) - Complex.exp (Complex.I*((-y:ℝ):ℂ)) *
      ((1 + 1/(16*(Complex.I*((-y:ℝ):ℂ)/2))) * ((π:ℂ)/(Complex.I*((-y:ℝ):ℂ)/2))^(1/2:ℂ))‖
      ≤ 8*C/(y^2*Real.sqrt y) := by
    rw [AA_eq (-y), ← mul_sub, norm_mul, norm_exp_I_mul, one_mul]
    refine le_trans (hC (Complex.I*((-y:ℝ):ℂ)/2) hrm h1m) ?_
    rw [hnm]; exact hcmp C hC0
  have hNs : ‖∫ t in (-π)..π, osc y t * (psi t : ℂ)‖ ≤ K/(y^2*Real.sqrt y) := by
    refine le_trans (hK y hy1) ?_
    have hle : y^2 * Real.sqrt y ≤ y^3 := by
      nlinarith [Real.sq_sqrt hy0.le, Real.sqrt_nonneg y, sq_nonneg (Real.sqrt y - 1)]
    exact div_le_div_of_nonneg_left hK0 (by positivity) hle
  have htot : ‖(∫ t in (-π)..π, osc y t)
      - ((2 * Real.sqrt (2*π/y) * (Real.cos (y-π/4) + Real.sin (y-π/4)/(8*y)) : ℝ) : ℂ)‖
      ≤ (16*C + K)/(y^2*Real.sqrt y) := by
    rw [circle_decomp y, ← main_sum y hy0]
    have hrw : (AA y + AA (-y) + ∫ t in (-π)..π, osc y t * (psi t : ℂ))
        - (Complex.exp (Complex.I*(y:ℂ)) *
            ((1 + 1/(16*(Complex.I*(y:ℂ)/2))) * ((π:ℂ)/(Complex.I*(y:ℂ)/2))^(1/2:ℂ))
          + Complex.exp (Complex.I*((-y:ℝ):ℂ)) *
            ((1 + 1/(16*(Complex.I*((-y:ℝ):ℂ)/2))) *
              ((π:ℂ)/(Complex.I*((-y:ℝ):ℂ)/2))^(1/2:ℂ)))
        = (AA y - Complex.exp (Complex.I*(y:ℂ)) *
            ((1 + 1/(16*(Complex.I*(y:ℂ)/2))) * ((π:ℂ)/(Complex.I*(y:ℂ)/2))^(1/2:ℂ)))
          + (AA (-y) - Complex.exp (Complex.I*((-y:ℝ):ℂ)) *
            ((1 + 1/(16*(Complex.I*((-y:ℝ):ℂ)/2))) *
              ((π:ℂ)/(Complex.I*((-y:ℝ):ℂ)/2))^(1/2:ℂ)))
          + ∫ t in (-π)..π, osc y t * (psi t : ℂ) := by ring
    rw [hrw]
    refine le_trans (norm_add_le _ _) ?_
    refine le_trans (add_le_add (norm_add_le _ _) (le_refl _)) ?_
    refine le_trans (add_le_add (add_le_add hAp hAm) hNs) (le_of_eq ?_)
    field_simp
    ring
  have hre : besselJ0 y - Real.sqrt (2/(π*y)) * (Real.cos (y-π/4) + Real.sin (y-π/4)/(8*y))
      = 1/(2*π) * ((∫ t in (-π)..π, osc y t)
        - ((2 * Real.sqrt (2*π/y) * (Real.cos (y-π/4) + Real.sin (y-π/4)/(8*y)) : ℝ) : ℂ)).re := by
    rw [besselJ0_eq_re, Complex.sub_re, Complex.ofReal_re, ← sqrt_two_pi_div y hy0]
    ring
  rw [hre, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1/(2*π))]
  have h1 := Complex.abs_re_le_norm ((∫ t in (-π)..π, osc y t)
        - ((2 * Real.sqrt (2*π/y) * (Real.cos (y-π/4) + Real.sin (y-π/4)/(8*y)) : ℝ) : ℂ))
  calc 1/(2*π) * |((∫ t in (-π)..π, osc y t)
        - ((2 * Real.sqrt (2*π/y) * (Real.cos (y-π/4) + Real.sin (y-π/4)/(8*y)) : ℝ) : ℂ)).re|
      ≤ 1/(2*π) * ((16*C + K)/(y^2*Real.sqrt y)) :=
        mul_le_mul_of_nonneg_left (le_trans h1 htot) (by positivity)
    _ = 1/(2*π) * (16*C + K) / (y^2 * Real.sqrt y) := by ring

end Q776
