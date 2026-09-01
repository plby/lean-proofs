/-
This analytic helper is adapted from the fully proved Q776 development at
https://github.com/l-pommeret/rms-math-proofs, revision
a5c24c8190191bc9491259035073a9230b9f6727, for Lean/Mathlib v4.33.0.
-/

import ErdosProblems.Erdos465.Analytic.Model

/-!
# Q776 — the partition of the Bessel integral and the nonstationary estimate

We split the circle integral `∫_{-π}^{π} exp (i y cos t) dt` into a neighbourhood of the
stationary point `t = 0`, a neighbourhood of `t = π`, and a nonstationary remainder, which is
estimated by three integrations by parts.
-/

open scoped Real
open Complex MeasureTheory intervalIntegral

namespace Q776

set_option backward.isDefEq.respectTransparency false

/-! ## Half angle identities and the cutoffs on the circle -/

theorem cutoff_even (u : ℝ) : cutoff (-u) = cutoff u := bumpHalf.neg u

theorem cos_half_sq (t : ℝ) : 2 * Real.cos (t/2)^2 = 1 + Real.cos t := by
  have h := Real.cos_two_mul (t/2)
  rw [show 2 * (t/2) = t by ring] at h
  linarith

theorem sin_half_sq (t : ℝ) : 2 * Real.sin (t/2)^2 = 1 - Real.cos t := by
  have h := Real.sin_sq_add_cos_sq (t/2)
  have h2 := cos_half_sq t
  linarith

/-- Cutoff localizing at the stationary point `t = 0`. -/
noncomputable def chiA (t : ℝ) : ℝ := cutoff (2 * Real.sin (t/2))

/-- Cutoff localizing at the stationary point `t = π`. -/
noncomputable def chiB (t : ℝ) : ℝ := cutoff (2 * Real.cos (t/2))

/-- The nonstationary part of the partition of unity. -/
noncomputable def psi (t : ℝ) : ℝ := 1 - chiA t - chiB t

theorem contDiff_sinHalf : ContDiff ℝ (⊤:ℕ∞) (fun t : ℝ => 2 * Real.sin (t/2)) :=
  contDiff_const.mul (Real.contDiff_sin.comp (contDiff_id.div_const 2))

theorem contDiff_cosHalf : ContDiff ℝ (⊤:ℕ∞) (fun t : ℝ => 2 * Real.cos (t/2)) :=
  contDiff_const.mul (Real.contDiff_cos.comp (contDiff_id.div_const 2))

theorem chiA_smooth : ContDiff ℝ (⊤:ℕ∞) chiA := cutoff_smooth.comp contDiff_sinHalf
theorem chiB_smooth : ContDiff ℝ (⊤:ℕ∞) chiB := cutoff_smooth.comp contDiff_cosHalf
theorem psi_smooth : ContDiff ℝ (⊤:ℕ∞) psi :=
  (contDiff_const.sub chiA_smooth).sub chiB_smooth

theorem chiA_even (t : ℝ) : chiA (-t) = chiA t := by
  simp only [chiA, show (-t)/2 = -(t/2) by ring, Real.sin_neg]
  rw [show 2 * -Real.sin (t/2) = -(2 * Real.sin (t/2)) by ring, cutoff_even]

theorem chiB_even (t : ℝ) : chiB (-t) = chiB t := by
  simp only [chiB, show (-t)/2 = -(t/2) by ring, Real.cos_neg]

theorem psi_even (t : ℝ) : psi (-t) = psi t := by
  simp [psi, chiA_even, chiB_even]

theorem chiA_zero_of_cos_nonpos {t : ℝ} (h : Real.cos t ≤ 0) : chiA t = 0 := by
  apply cutoff_zero
  have h1 : 2 * Real.sin (t/2)^2 = 1 - Real.cos t := sin_half_sq t
  have hsq : 1 ≤ (2 * Real.sin (t/2))^2 := by nlinarith
  nlinarith [abs_nonneg (2 * Real.sin (t/2)), sq_abs (2 * Real.sin (t/2))]

theorem chiB_zero_of_cos_nonneg {t : ℝ} (h : 0 ≤ Real.cos t) : chiB t = 0 := by
  apply cutoff_zero
  have h1 : 2 * Real.cos (t/2)^2 = 1 + Real.cos t := cos_half_sq t
  have hsq : 1 ≤ (2 * Real.cos (t/2))^2 := by nlinarith
  nlinarith [abs_nonneg (2 * Real.cos (t/2)), sq_abs (2 * Real.cos (t/2))]

/-- Near every zero of `sin` the two cutoffs already add up to `1`. -/
theorem psi_zero_of_sin_small {t : ℝ} (h : |Real.sin t| ≤ 1 / 4) : psi t = 0 := by
  set p := |Real.sin (t/2)| with hp
  set q := |Real.cos (t/2)| with hq
  have hp0 : 0 ≤ p := abs_nonneg _
  have hq0 : 0 ≤ q := abs_nonneg _
  have hpq : p^2 + q^2 = 1 := by
    rw [hp, hq, sq_abs, sq_abs]
    exact Real.sin_sq_add_cos_sq (t/2)
  have hs : Real.sin t = 2 * Real.sin (t/2) * Real.cos (t/2) := by
    have h2 := Real.sin_two_mul (t/2)
    rw [show 2 * (t/2) = t by ring] at h2
    exact h2
  have habs : |Real.sin t| = 2 * (p * q) := by
    rw [hs, abs_mul, abs_mul, abs_two]
    ring
  rw [habs] at h
  have hprod : 2 * (p * q) ≤ 1/4 := h
  rcases le_total q p with hle | hle
  · -- `p` is large: `chiA = 0`, `chiB = 1`
    have hpbig : 1/2 ≤ p := by nlinarith
    have hqsmall : q ≤ 1/4 := by nlinarith
    have hA : chiA t = 0 := by
      apply cutoff_zero
      rw [abs_mul]
      simp only [abs_two]
      linarith [hp ▸ (le_refl p)]
    have hB : chiB t = 1 := by
      apply cutoff_one
      rw [abs_mul]
      simp only [abs_two]
      linarith
    simp [psi, hA, hB]
  · have hpbig : 1/2 ≤ q := by nlinarith
    have hqsmall : p ≤ 1/4 := by nlinarith
    have hB : chiB t = 0 := by
      apply cutoff_zero
      rw [abs_mul]
      simp only [abs_two]
      linarith
    have hA : chiA t = 1 := by
      apply cutoff_one
      rw [abs_mul]
      simp only [abs_two]
      linarith
    simp [psi, hA, hB]

/-! ## Nonstationary functions and integration by parts -/

/-- `NSFun a W` : `W` is smooth and vanishes wherever `|sin t| ≤ a`. -/
structure NSFun (a : ℝ) (W : ℝ → ℂ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) W
  apos : 0 < a
  zero_near : ∀ t, |Real.sin t| ≤ a → W t = 0

namespace NSFun

variable {a : ℝ} {W : ℝ → ℂ}

theorem differentiable (h : NSFun a W) : Differentiable ℝ W :=
  (contDiff_infty_iff_deriv.1 h.smooth).1

theorem hasDerivAt' (h : NSFun a W) (t : ℝ) : HasDerivAt W (deriv W t) t :=
  (h.differentiable t).hasDerivAt

theorem deriv' (h : NSFun a W) {a' : ℝ} (h1 : 0 < a') (h2 : a' < a) : NSFun a' (deriv W) := by
  refine ⟨(contDiff_infty_iff_deriv.1 h.smooth).2, h1, ?_⟩
  intro t ht
  have hev : W =ᶠ[nhds t] fun _ => (0:ℂ) := by
    have hset : {s : ℝ | |Real.sin s| < a} ∈ nhds t := by
      refine IsOpen.mem_nhds (isOpen_lt (continuous_abs.comp Real.continuous_sin)
        continuous_const) ?_
      simp only [Set.mem_ofPred_eq]
      linarith
    filter_upwards [hset] with s hs using h.zero_near s hs.le
  rw [Filter.EventuallyEq.deriv_eq hev]
  simp

/-- Dividing by `sin` preserves the class. -/
theorem div_sin (h : NSFun a W) : NSFun a (fun t => W t / Real.sin t) := by
  refine ⟨?_, h.apos, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro t
    by_cases hs : Real.sin t = 0
    · have hev : (fun s => W s / Real.sin s) =ᶠ[nhds t] fun _ => (0:ℂ) := by
        have hset : {s : ℝ | |Real.sin s| < a} ∈ nhds t := by
          refine IsOpen.mem_nhds (isOpen_lt (continuous_abs.comp Real.continuous_sin)
            continuous_const) ?_
          simp only [Set.mem_ofPred_eq, hs, abs_zero]
          exact h.apos
        filter_upwards [hset] with s hsm
        rw [h.zero_near s hsm.le]
        simp
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · have hinvR : ContDiffAt ℝ (⊤:ℕ∞) (fun s : ℝ => (Real.sin s)⁻¹) t :=
        (Real.contDiff_sin.contDiffAt).inv hs
      have hinv : ContDiffAt ℝ (⊤:ℕ∞) (fun s : ℝ => (((Real.sin s)⁻¹ : ℝ) : ℂ)) t :=
        Complex.ofRealCLM.contDiff.comp_contDiffAt t hinvR
      have hmul : ContDiffAt ℝ (⊤:ℕ∞) (fun s : ℝ => W s * (((Real.sin s)⁻¹ : ℝ) : ℂ)) t :=
        h.smooth.contDiffAt.mul hinv
      refine hmul.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      push_cast
      ring
  · intro t ht
    rw [h.zero_near t ht]
    simp

theorem sin_mul (h : NSFun a W) (t : ℝ) :
    (Real.sin t : ℂ) * (W t / Real.sin t) = W t := by
  by_cases hs : Real.sin t = 0
  · rw [h.zero_near t (by simp [hs]; linarith [h.apos])]
    simp
  · have hsc : (Real.sin t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs
    field_simp

theorem bound (h : NSFun a W) : ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc (-π) π, ‖W t‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -π) (b := π)).exists_bound_of_continuousOn
    (h.smooth.continuous.continuousOn (s := Set.Icc (-π) π))
  exact ⟨max M 0, le_max_right _ _, fun t ht => le_trans (hM t ht) (le_max_left _ _)⟩

end NSFun

/-- The oscillating factor. -/
noncomputable def osc (y : ℝ) (t : ℝ) : ℂ := Complex.exp (Complex.I * y * Real.cos t)

theorem continuous_osc (y : ℝ) : Continuous (osc y) := by
  unfold osc
  fun_prop

theorem norm_osc (y : ℝ) (t : ℝ) : ‖osc y t‖ = 1 := by
  rw [osc, Complex.norm_exp]
  have : (Complex.I * (y:ℂ) * (Real.cos t : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this]
  simp

theorem hasDerivAt_osc (y : ℝ) (t : ℝ) :
    HasDerivAt (osc y) (osc y t * (Complex.I * y * (-Real.sin t))) t := by
  have h1 : HasDerivAt (fun s : ℝ => ((Real.cos s : ℝ) : ℂ)) ((-Real.sin t : ℝ) : ℂ) t :=
    (Real.hasDerivAt_cos t).ofReal_comp
  have h2 : HasDerivAt (fun s : ℝ => Complex.I * y * ((Real.cos s : ℝ) : ℂ))
      (Complex.I * y * ((-Real.sin t : ℝ) : ℂ)) t := h1.const_mul _
  have h3 := h2.cexp
  change HasDerivAt
    (fun x : ℝ ↦ Complex.exp (Complex.I * (y : ℂ) * (Real.cos x : ℂ)))
    (Complex.exp (Complex.I * (y : ℂ) * (Real.cos t : ℂ)) *
      (Complex.I * (y : ℂ) * (-Real.sin t : ℂ))) t
  convert h3 using 1 ; try rfl
  push_cast
  ring

/-- One integration by parts against the oscillating factor `exp (i y cos t)`. -/
theorem ns_ibp {a : ℝ} {W : ℝ → ℂ} (h : NSFun a W) {y : ℝ} (hy : y ≠ 0) :
    (∫ t in (-π)..π, osc y t * W t)
      = (1/(Complex.I * y)) *
        ∫ t in (-π)..π, osc y t * deriv (fun s => W s / Real.sin s) t := by
  have hIy : Complex.I * (y:ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.2 hy)
  have hV : NSFun a (fun s => W s / Real.sin s) := h.div_sin
  have hVd : NSFun (a/2) (deriv fun s => W s / Real.sin s) :=
    hV.deriv' (by linarith [h.apos]) (by linarith [h.apos])
  have hWc : Continuous W := h.smooth.continuous
  have hVc : Continuous (deriv fun s => W s / Real.sin s) := hVd.smooth.continuous
  have hE := continuous_osc y
  -- the derivative of `osc * V`
  have hFderiv : ∀ t : ℝ, HasDerivAt (fun s => osc y s * (fun r => W r / Real.sin r) s)
      (osc y t * (Complex.I * y * (-(W t))) +
        osc y t * deriv (fun s => W s / Real.sin s) t) t := by
    intro t
    have hd := (hasDerivAt_osc y t).mul (hV.hasDerivAt' t)
    have hkey : (Real.sin t : ℂ) * (W t / Real.sin t) = W t := h.sin_mul t
    change HasDerivAt ((osc y) * fun r ↦ W r / Real.sin r)
      (osc y t * (Complex.I * y * (-(W t))) +
        osc y t * deriv (fun s ↦ W s / Real.sin s) t) t
    convert hd using 1 <;> try rfl
    linear_combination (osc y t * (Complex.I * (y:ℂ))) * hkey
  have hcont : Continuous (fun t : ℝ => osc y t * (Complex.I * y * (-(W t))) +
      osc y t * deriv (fun s => W s / Real.sin s) t) :=
    (hE.mul (continuous_const.mul hWc.neg)).add (hE.mul hVc)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s => osc y s * (fun r => W r / Real.sin r) s) (a := -π) (b := π)
    (fun t _ => hFderiv t) (hcont.intervalIntegrable _ _)
  have hVpi : W π / Real.sin π = 0 := by
    rw [h.zero_near π (by simp; linarith [h.apos])]
    simp
  have hVmpi : W (-π) / Real.sin (-π) = 0 := by
    rw [h.zero_near (-π) (by simp; linarith [h.apos])]
    simp
  simp only [hVpi, hVmpi, mul_zero, sub_zero] at hFTC
  have hsplit : (∫ t in (-π)..π, (osc y t * (Complex.I * y * (-(W t))) +
        osc y t * deriv (fun s => W s / Real.sin s) t))
      = (-(Complex.I * y)) * (∫ t in (-π)..π, osc y t * W t)
        + ∫ t in (-π)..π, osc y t * deriv (fun s => W s / Real.sin s) t := by
    have hc1 : Continuous (fun t : ℝ => Complex.I * (y:ℂ) * (-(W t))) :=
      continuous_const.mul hWc.neg
    have hI1 : IntervalIntegrable (fun t : ℝ => osc y t * (Complex.I * y * (-(W t))))
        MeasureTheory.volume (-π) π := (hE.mul hc1).intervalIntegrable _ _
    have hI2 : IntervalIntegrable
        (fun t : ℝ => osc y t * deriv (fun s => W s / Real.sin s) t)
        MeasureTheory.volume (-π) π := (hE.mul hVc).intervalIntegrable _ _
    rw [intervalIntegral.integral_add hI1 hI2]
    congr 1
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [hsplit] at hFTC
  have hzero : (-(Complex.I * (y:ℂ))) * (∫ t in (-π)..π, osc y t * W t)
      + ∫ t in (-π)..π, osc y t * deriv (fun s => W s / Real.sin s) t = 0 := by
    simpa using hFTC
  have h2 : (∫ t in (-π)..π, osc y t * deriv (fun s => W s / Real.sin s) t)
      = (Complex.I * y) * ∫ t in (-π)..π, osc y t * W t := by
    linear_combination hzero
  rw [h2, ← mul_assoc, one_div, inv_mul_cancel₀ hIy, one_mul]

/-- Iterating the integration by parts three times gives an `O(y^{-3})` bound. -/
theorem ns_bound {a : ℝ} {W : ℝ → ℂ} (h : NSFun a W) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, 1 ≤ y →
      ‖∫ t in (-π)..π, osc y t * W t‖ ≤ K / y^3 := by
  set W1 : ℝ → ℂ := deriv (fun s => W s / Real.sin s) with hW1
  set W2 : ℝ → ℂ := deriv (fun s => W1 s / Real.sin s) with hW2
  set W3 : ℝ → ℂ := deriv (fun s => W2 s / Real.sin s) with hW3
  have h1 : NSFun (a/2) W1 := h.div_sin.deriv' (by linarith [h.apos]) (by linarith [h.apos])
  have h2 : NSFun (a/4) W2 := h1.div_sin.deriv' (by linarith [h1.apos]) (by linarith [h1.apos])
  have h3 : NSFun (a/8) W3 := h2.div_sin.deriv' (by linarith [h2.apos]) (by linarith [h2.apos])
  obtain ⟨M, hM0, hM⟩ := h3.bound
  refine ⟨2 * π * M, by positivity, fun y hy => ?_⟩
  have hy0 : y ≠ 0 := by linarith
  have hypos : (0:ℝ) < y := by linarith
  rw [ns_ibp h hy0, ← hW1, ns_ibp h1 hy0, ← hW2, ns_ibp h2 hy0, ← hW3]
  have hIy : ‖(1:ℂ)/(Complex.I * y)‖ = 1/y := by
    rw [norm_div, norm_mul]
    simp [abs_of_pos hypos]
  have hlast : ‖∫ t in (-π)..π, osc y t * W3 t‖ ≤ 2 * π * M := by
    have hb : ∀ t ∈ Set.uIoc (-π) π, ‖osc y t * W3 t‖ ≤ M := by
      intro t ht
      rw [norm_mul, norm_osc, one_mul]
      apply hM
      rcases Set.mem_uIoc.1 ht with h' | h'
      · exact ⟨h'.1.le, h'.2⟩
      · exfalso; linarith [Real.pi_pos, h'.1, h'.2]
    have := intervalIntegral.norm_integral_le_of_norm_le_const hb
    calc ‖∫ t in (-π)..π, osc y t * W3 t‖ ≤ M * |π - (-π)| := this
      _ = 2 * π * M := by rw [abs_of_nonneg (by linarith [Real.pi_pos])]; ring
  rw [norm_mul, norm_mul, norm_mul, hIy]
  have hstep : 1/y * (1/y * (1/y * ‖∫ t in (-π)..π, osc y t * W3 t‖))
      ≤ 1/y * (1/y * (1/y * (2 * π * M))) := by
    have hp : (0:ℝ) ≤ 1/y := by positivity
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hlast hp) hp) hp
  refine le_trans hstep (le_of_eq ?_)
  field_simp

end Q776
