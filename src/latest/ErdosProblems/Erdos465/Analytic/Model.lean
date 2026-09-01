/-
This analytic helper is adapted from the fully proved Q776 development at
https://github.com/l-pommeret/rms-math-proofs, revision
a5c24c8190191bc9491259035073a9230b9f6727, for Lean/Mathlib v4.33.0.
-/

import ErdosProblems.Erdos465.Analytic.Fresnel

/-!
# Q776 — the local Gaussian model at the saddle point

Here we prove the two-term expansion of the model integral

  `∫ u, exp (-b u²) * (cutoff u * amp u) du = (π/b)^{1/2} (1 + 1/(16 b)) + O(‖b‖^{-5/2})`

uniformly for `0 ≤ re b`, `1 ≤ ‖b‖`.  Here `amp u = (1-u²/4)^{-1/2}` is the exact amplitude
produced by the change of variables `u = 2 sin (θ/2)` in the Bessel integral, so that `1/16`
is the coefficient responsible for the `1/(16R)` correction in the final asymptotics.
-/

open scoped Real
open Complex MeasureTheory

namespace Q776

/-! ## Smooth compactly supported functions -/

/-- Smooth and supported in `[-1,1]`. -/
structure CSFun (W : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) W
  supp : ∀ u, 1 < |u| → W u = 0

namespace CSFun

variable {W : ℝ → ℝ}

theorem differentiable (h : CSFun W) : Differentiable ℝ W :=
  (contDiff_infty_iff_deriv.1 h.smooth).1

theorem hasDerivAt' (h : CSFun W) (u : ℝ) : HasDerivAt W (deriv W u) u :=
  (h.differentiable u).hasDerivAt

theorem deriv' (h : CSFun W) : CSFun (deriv W) := by
  refine ⟨(contDiff_infty_iff_deriv.1 h.smooth).2, ?_⟩
  intro u hu
  have hev : W =ᶠ[nhds u] fun _ => (0:ℝ) := by
    have hset : {v : ℝ | 1 < |v|} ∈ nhds u :=
      IsOpen.mem_nhds (isOpen_lt continuous_const continuous_abs) hu
    filter_upwards [hset] with v hv using h.supp v hv
  rw [Filter.EventuallyEq.deriv_eq hev]
  simp

theorem mul_id (h : CSFun W) : CSFun (fun u => u * W u) :=
  ⟨contDiff_id.mul h.smooth, fun u hu => by rw [h.supp u hu]; ring⟩

theorem const_mul (r : ℝ) (h : CSFun W) : CSFun (fun u => r * W u) :=
  ⟨contDiff_const.mul h.smooth, fun u hu => by rw [h.supp u hu]; ring⟩

theorem sq_mul (h : CSFun W) : CSFun (fun u => u^2 * W u) :=
  ⟨(contDiff_id.pow 2).mul h.smooth, fun u hu => by rw [h.supp u hu]; ring⟩

theorem bound (h : CSFun W) : ∃ M : ℝ, 0 ≤ M ∧ ∀ u, |W u| ≤ M := by
  obtain ⟨M, hM0, hM⟩ := bounded_of_supp (f := fun u => (W u : ℂ))
    (Complex.continuous_ofReal.comp h.smooth.continuous) (A := 2)
    (fun u hu => by simp [h.supp u (by linarith)])
  exact ⟨M, hM0, fun u => by simpa using hM u⟩

theorem integrable (h : CSFun W) (b : ℂ) :
    Integrable (fun u : ℝ => Complex.exp (-b * (u:ℂ)^2) * (W u : ℂ)) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (continuous_cgauss b).mul (Complex.continuous_ofReal.comp h.smooth.continuous)
  · apply HasCompactSupport.intro (isCompact_Icc (a := (-1:ℝ)) (b := 1))
    intro x hx
    have hx' : 1 < |x| := by
      rw [Set.mem_Icc] at hx
      push Not at hx
      rcases lt_or_ge x (-1) with h1 | h1
      · rw [abs_of_neg (by linarith)]; linarith
      · have := hx h1
        rw [abs_of_pos (by linarith)]; linarith
    rw [h.supp x hx']
    simp

end CSFun

/-- The model integral. -/
noncomputable def Iof (b : ℂ) (W : ℝ → ℝ) : ℂ :=
  ∫ u : ℝ, Complex.exp (-b * (u:ℂ)^2) * (W u : ℂ)

theorem Iof_congr {b : ℂ} {W1 W2 : ℝ → ℝ} (h : ∀ u, W1 u = W2 u) : Iof b W1 = Iof b W2 := by
  unfold Iof
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => by simp only [h u])

theorem Iof_add {b : ℂ} {W1 W2 : ℝ → ℝ} (h1 : CSFun W1) (h2 : CSFun W2) :
    Iof b (fun u => W1 u + W2 u) = Iof b W1 + Iof b W2 := by
  unfold Iof
  rw [← MeasureTheory.integral_add (h1.integrable b) (h2.integrable b)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  push_cast
  ring

theorem Iof_const_mul {b : ℂ} (r : ℝ) (W : ℝ → ℝ) :
    Iof b (fun u => r * W u) = (r : ℂ) * Iof b W := by
  unfold Iof
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  push_cast
  ring

theorem Iof_cutoff (b : ℂ) : Iof b cutoff = fresnelI b := rfl

/-- Integration by parts in the model integral. -/
theorem Iof_mul_id {V : ℝ → ℝ} (h : CSFun V) {b : ℂ} (hb : b ≠ 0) :
    Iof b (fun u => u * V u) = (1/(2*b)) * Iof b (deriv V) := by
  have hstep : Iof b (fun u => u * V u)
      = ∫ u : ℝ, Complex.exp (-b * (u:ℂ)^2) * ((u:ℂ) * (V u : ℂ)) := by
    unfold Iof
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    push_cast
    ring
  rw [hstep]
  exact gauss_ibp hb (A := 2) (by norm_num) (fun u => (h.hasDerivAt' u).ofReal_comp)
    (Complex.continuous_ofReal.comp h.deriv'.smooth.continuous)
    (fun u hu => by simp [h.supp u (by linarith)])

/-- The van der Corput bound in the model integral. -/
theorem Iof_vdC {W : ℝ → ℝ} (h : CSFun W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b : ℂ, 0 ≤ b.re → 1 ≤ ‖b‖ → ‖Iof b W‖ ≤ C / Real.sqrt ‖b‖ := by
  obtain ⟨M1, hM10, hM1⟩ := h.bound
  obtain ⟨M2, hM20, hM2⟩ := h.deriv'.bound
  refine ⟨max M1 M2 * (2 + 5), mul_nonneg (le_trans hM10 (le_max_left _ _)) (by norm_num),
    fun b hb hb1 => ?_⟩
  exact gauss_vdC hb hb1 (A := 2) (by norm_num)
    (W := fun u => (W u : ℂ)) (W' := fun u => ((deriv W u : ℝ) : ℂ))
    (fun u => (h.hasDerivAt' u).ofReal_comp)
    (Complex.continuous_ofReal.comp h.deriv'.smooth.continuous)
    (fun u hu => by simp [h.supp u (by linarith)])
    (fun u => by simpa using le_trans (hM1 u) (le_max_left _ _))
    (fun u => by simpa using le_trans (hM2 u) (le_max_right _ _))

theorem deriv_mul_id {V : ℝ → ℝ} (h : CSFun V) (u : ℝ) :
    deriv (fun x => x * V x) u = V u + u * deriv V u := by
  have := ((hasDerivAt_id u).mul (h.hasDerivAt' u)).deriv
  change deriv (id * V) u = V u + u * deriv V u
  simpa only [one_mul, id_eq] using this

/-! ## The second order amplitude coefficient -/

/-- The explicit smooth quotient `(Pfun u - 1/8)/u²`. -/
noncomputable def Pfun2 (u : ℝ) : ℝ :=
  (2 + sroot u) / (8 * (1 + sroot u) * (4 * sroot u + 4 - u^2))

theorem Pfun2_denom_pos {u : ℝ} (h : |u| < 2) :
    0 < 8 * (1 + sroot u) * (4 * sroot u + 4 - u^2) := by
  have h1 : 0 < sroot u := sroot_pos h
  have h3 : 0 < 4 * sroot u + 4 - u^2 := Pfun_denom_pos h
  positivity

theorem contDiffAt_Pfun2 {u : ℝ} (h : |u| < 2) : ContDiffAt ℝ (⊤:ℕ∞) Pfun2 u := by
  apply ContDiffAt.div
  · exact contDiffAt_const.add (contDiffAt_sroot h)
  · exact ((contDiffAt_const.mul (contDiffAt_const.add (contDiffAt_sroot h))).mul
      ((contDiffAt_const.mul (contDiffAt_sroot h)).add contDiffAt_const |>.sub
        ((contDiff_id.pow 2).contDiffAt)))
  · exact ne_of_gt (Pfun2_denom_pos h)

theorem Pfun_sub_eighth {u : ℝ} (h : |u| < 2) : Pfun u - 1/8 = u^2 * Pfun2 u := by
  have h1 : 0 < sroot u := sroot_pos h
  have h2 : (sroot u)^2 = 1 - u^2/4 := sroot_sq h.le
  have h3 : 0 < 4 * sroot u + 4 - u^2 := Pfun_denom_pos h
  have h4 : (0:ℝ) < 1 + sroot u := by linarith
  have hPfun : Pfun u * (4 * sroot u + 4 - u^2) = 1 := by
    rw [Pfun, inv_mul_cancel₀ (ne_of_gt h3)]
  have key : (Pfun u - 1/8) * (8 * (1 + sroot u) * (4 * sroot u + 4 - u^2))
      = u^2 * (2 + sroot u) := by
    have expand : (Pfun u - 1/8) * (8 * (1 + sroot u) * (4 * sroot u + 4 - u^2))
        = 8*(1 + sroot u)*(Pfun u * (4 * sroot u + 4 - u^2))
          - (1 + sroot u)*(4 * sroot u + 4 - u^2) := by ring
    rw [expand, hPfun]
    linear_combination (-4 : ℝ) * h2
  have hP2 : u^2 * Pfun2 u
      = (u^2 * (2 + sroot u)) / (8 * (1 + sroot u) * (4 * sroot u + 4 - u^2)) := by
    rw [Pfun2]; ring
  rw [hP2, eq_div_iff (ne_of_gt (Pfun2_denom_pos h))]
  exact key

/-! ## The three concrete profiles -/

noncomputable def Gfun (u : ℝ) : ℝ := cutoff u * amp u
noncomputable def Hfun (u : ℝ) : ℝ := cutoff u * Pfun u
noncomputable def H2fun (u : ℝ) : ℝ := cutoff u * Pfun2 u

theorem csfun_Gfun : CSFun Gfun :=
  ⟨contDiff_cutoff_mul (fun u hu => contDiffAt_amp hu), fun u hu => by
    simp [Gfun, cutoff_zero hu.le]⟩

theorem csfun_Hfun : CSFun Hfun :=
  ⟨contDiff_cutoff_mul (fun u hu => contDiffAt_Pfun hu), fun u hu => by
    simp [Hfun, cutoff_zero hu.le]⟩

theorem csfun_H2fun : CSFun H2fun :=
  ⟨contDiff_cutoff_mul (fun u hu => contDiffAt_Pfun2 hu), fun u hu => by
    simp [H2fun, cutoff_zero hu.le]⟩

theorem csfun_cutoff : CSFun cutoff :=
  ⟨cutoff_smooth, fun _ hu => cutoff_zero hu.le⟩

theorem Gfun_eq (u : ℝ) : Gfun u = cutoff u + u^2 * Hfun u := by
  by_cases hu : 1 ≤ |u|
  · simp [Gfun, Hfun, cutoff_zero hu]
  · push Not at hu
    have h2 : |u| < 2 := by linarith
    have := amp_sub_one h2
    simp only [Gfun, Hfun]
    linear_combination cutoff u * this

theorem Hfun_eq (u : ℝ) : Hfun u = (1/8) * cutoff u + u^2 * H2fun u := by
  by_cases hu : 1 ≤ |u|
  · simp [Hfun, H2fun, cutoff_zero hu]
  · push Not at hu
    have h2 : |u| < 2 := by linarith
    have := Pfun_sub_eighth h2
    simp only [Hfun, H2fun]
    linear_combination cutoff u * this

/-! ## The model expansion -/

/-- One integration by parts on a `u²`-weighted profile. -/
theorem Iof_sq_ibp {V : ℝ → ℝ} (h : CSFun V) {b : ℂ} (hb : b ≠ 0) :
    Iof b (fun u => u^2 * V u) = (1/(2*b)) * Iof b (deriv fun x => x * V x) := by
  have h1 : Iof b (fun u => u^2 * V u) = Iof b (fun u => u * (fun x => x * V x) u) :=
    Iof_congr (fun u => by ring)
  rw [h1, Iof_mul_id h.mul_id hb]

/-- The same, but keeping the leading term explicitly. -/
theorem Iof_sq_mul {V : ℝ → ℝ} (h : CSFun V) {b : ℂ} (hb : b ≠ 0) :
    Iof b (fun u => u^2 * V u)
      = (1/(2*b)) * (Iof b V + (1/(2*b)) * Iof b (deriv (deriv V))) := by
  rw [Iof_sq_ibp h hb]
  congr 1
  have h2 : Iof b (deriv fun x => x * V x) = Iof b (fun u => V u + u * deriv V u) :=
    Iof_congr (fun u => deriv_mul_id h u)
  rw [h2, Iof_add h h.deriv'.mul_id, Iof_mul_id h.deriv' hb]

/-- **The local model expansion.**  Two terms with a uniform `O(‖b‖^{-5/2})` remainder. -/
theorem model_expansion :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b : ℂ, 0 ≤ b.re → 1 ≤ ‖b‖ →
      ‖Iof b Gfun - (1 + 1/(16*b)) * ((π:ℂ)/b)^(1/2:ℂ)‖
        ≤ C / (‖b‖^2 * Real.sqrt ‖b‖) := by
  obtain ⟨C2, hC20, hC2⟩ := Iof_vdC (csfun_H2fun.mul_id.deriv')
  obtain ⟨C3, hC30, hC3⟩ := Iof_vdC (csfun_Hfun.deriv'.deriv')
  refine ⟨17 * tailConst / 128 + (C2 + C3) / 4,
    by have := tailConst_nonneg; linarith, fun b hb hb1 => ?_⟩
  have hbne : b ≠ 0 := by
    intro h0
    rw [h0] at hb1
    simp at hb1
    linarith
  have hbn : (0:ℝ) < ‖b‖ := lt_of_lt_of_le zero_lt_one hb1
  have hsq : (0:ℝ) < Real.sqrt ‖b‖ := Real.sqrt_pos.2 hbn
  set T : ℝ := ‖b‖^2 * Real.sqrt ‖b‖ with hT
  have hTpos : 0 < T := by positivity
  set S : ℂ := ((π:ℂ)/b)^(1/2:ℂ) with hS
  set X2 : ℂ := Iof b (deriv fun u => u * H2fun u) with hX2
  set X3 : ℂ := Iof b (deriv (deriv Hfun)) with hX3
  -- expand `Iof b Hfun`
  have hH : Iof b Hfun = (1/8 : ℂ) * fresnelI b + (1/(2*b)) * X2 := by
    have e0 : Iof b Hfun = Iof b (fun u => (1/8 : ℝ) * cutoff u + u^2 * H2fun u) :=
      Iof_congr Hfun_eq
    rw [e0, Iof_add (csfun_cutoff.const_mul (1/8)) csfun_H2fun.sq_mul, Iof_const_mul,
      Iof_sq_ibp csfun_H2fun hbne, Iof_cutoff, hX2]
    push_cast
    ring
  -- expand `Iof b Gfun`
  have hG : Iof b Gfun
      = fresnelI b + (1/(2*b)) * (Iof b Hfun + (1/(2*b)) * X3) := by
    have e0 : Iof b Gfun = Iof b (fun u => cutoff u + u^2 * Hfun u) := Iof_congr Gfun_eq
    rw [e0, Iof_add csfun_cutoff csfun_Hfun.sq_mul, Iof_sq_mul csfun_Hfun hbne, Iof_cutoff]
  -- combine
  have hkey : Iof b Gfun - (1 + 1/(16*b)) * S
      = (1 + 1/(16*b)) * (fresnelI b - S) + (1/(4*b^2)) * (X2 + X3) := by
    rw [hG, hH]
    field_simp
    ring
  rw [hkey]
  have hb16 : ‖(1 : ℂ) + 1/(16*b)‖ ≤ 17/16 := by
    refine le_trans (norm_add_le _ _) ?_
    have : ‖(1:ℂ)/(16*b)‖ = 1/(16*‖b‖) := by
      rw [norm_div, norm_mul]
      simp
    rw [norm_one, this]
    have h16 : 1/(16*‖b‖) ≤ 1/16 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have hE0 : ‖fresnelI b - S‖ ≤ tailConst / (8 * T) := by
    refine le_trans (fresnel_cutoff hb hbne) ?_
    have hle : T ≤ ‖b‖^3 := by
      have h1 : Real.sqrt ‖b‖ ≤ ‖b‖ := by
        nlinarith [Real.sq_sqrt hbn.le, Real.sqrt_nonneg ‖b‖,
          sq_nonneg (Real.sqrt ‖b‖ - 1)]
      calc T = ‖b‖^2 * Real.sqrt ‖b‖ := rfl
        _ ≤ ‖b‖^2 * ‖b‖ := by nlinarith [sq_nonneg ‖b‖]
        _ = ‖b‖^3 := by ring
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [tailConst_nonneg]
  have hX2b : ‖X2‖ ≤ C2 / Real.sqrt ‖b‖ := hC2 b hb hb1
  have hX3b : ‖X3‖ ≤ C3 / Real.sqrt ‖b‖ := hC3 b hb hb1
  have hquad : ‖(1:ℂ)/(4*b^2)‖ = 1/(4*‖b‖^2) := by
    rw [norm_div, norm_mul, norm_pow]
    simp
  calc ‖(1 + 1/(16*b)) * (fresnelI b - S) + (1/(4*b^2)) * (X2 + X3)‖
      ≤ ‖(1 + 1/(16*b)) * (fresnelI b - S)‖ + ‖(1/(4*b^2)) * (X2 + X3)‖ := norm_add_le _ _
    _ ≤ (17/16) * (tailConst / (8*T))
          + (1/(4*‖b‖^2)) * (C2 / Real.sqrt ‖b‖ + C3 / Real.sqrt ‖b‖) := by
        have t1 : ‖(1 + 1/(16*b)) * (fresnelI b - S)‖ ≤ (17/16) * (tailConst / (8*T)) := by
          rw [norm_mul]
          exact mul_le_mul hb16 hE0 (norm_nonneg _) (by norm_num)
        have t2 : ‖(1/(4*b^2)) * (X2 + X3)‖
            ≤ (1/(4*‖b‖^2)) * (C2 / Real.sqrt ‖b‖ + C3 / Real.sqrt ‖b‖) := by
          rw [norm_mul, hquad]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact le_trans (norm_add_le _ _) (add_le_add hX2b hX3b)
        linarith
    _ = (17 * tailConst / 128 + (C2 + C3)/4) / T := by
        field_simp
        ring

end Q776
