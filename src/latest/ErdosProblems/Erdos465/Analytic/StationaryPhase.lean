/-
This analytic helper is adapted from the fully proved Q776 development at
https://github.com/l-pommeret/rms-math-proofs, revision
a5c24c8190191bc9491259035073a9230b9f6727, for Lean/Mathlib v4.33.0.
-/

import Mathlib

/-!
# Q776 — a one-dimensional stationary phase toolkit

This module develops, from scratch, the analytic estimates needed for a stationary-phase
analysis of oscillatory Gaussian integrals

  `∫ u, exp (-b u²) W u`,   `0 ≤ Re b`,

which is the local model at a nondegenerate stationary point.  Everything is proved with
explicit constants and complete proof terms.

Main results of this file:

* `Q776.gauss_ibp` : the basic integration by parts
  `∫ e^{-bu²} (u · V u) du = (1/(2b)) ∫ e^{-bu²} V' u du` for compactly supported `V`;
* `Q776.gauss_vdC` : the van der Corput type bound
  `‖∫ e^{-bu²} W u du‖ ≤ M (A+4) ‖b‖^{-1/2}`;
* `Q776.gauss_tail_bound` : the nonstationary bound `‖∫_{|u| ≥ δ} e^{-bu²} du‖ ≤ …`.
-/

open scoped Real Nat
open Complex MeasureTheory intervalIntegral

namespace Q776

set_option backward.isDefEq.respectTransparency false

section OscGauss

variable {b : ℂ}

/-- On the closed right half plane the Gaussian factor has norm at most one. -/
theorem norm_cgauss_le_one (hb : 0 ≤ b.re) (u : ℝ) : ‖Complex.exp (-b * (u:ℂ)^2)‖ ≤ 1 := by
  rw [Complex.norm_exp]
  have hre : (-b * (u:ℂ)^2).re = -(b.re * u^2) := by
    simp [Complex.mul_re, ← Complex.ofReal_pow]
  rw [hre, Real.exp_le_one_iff]
  have : 0 ≤ b.re * u^2 := mul_nonneg hb (sq_nonneg u)
  linarith

theorem hasDerivAt_cgauss (b : ℂ) (u : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (-b * (t:ℂ)^2))
      (Complex.exp (-b * (u:ℂ)^2) * (-b * (2*u))) u := by
  have h0 : HasDerivAt (fun t : ℝ => (t:ℂ)) 1 u := Complex.ofRealCLM.hasDerivAt
  have h1 : HasDerivAt (fun t : ℝ => -b * (t:ℂ)^2) (-b * (2*u)) u := by
    have := (h0.pow 2).const_mul (-b)
    simpa using this
  simpa using h1.cexp

theorem continuous_cgauss (b : ℂ) : Continuous (fun t : ℝ => Complex.exp (-b * (t:ℂ)^2)) := by
  fun_prop

/-- A function vanishing on `A ≤ |u|` has vanishing derivative on `A < |u|`. -/
theorem deriv_zero_far {A : ℝ} {V V' : ℝ → ℂ} (hV : ∀ u, HasDerivAt V (V' u) u)
    (hsupp : ∀ u : ℝ, A ≤ |u| → V u = 0) {u : ℝ} (hu : A < |u|) : V' u = 0 := by
  have h0 : HasDerivAt V 0 u := by
    have : V =ᶠ[nhds u] fun _ => 0 := by
      have hset : {x : ℝ | A < |x|} ∈ nhds u :=
        IsOpen.mem_nhds (isOpen_lt continuous_const continuous_abs) hu
      filter_upwards [hset] with x hx using hsupp x hx.le
    exact (hasDerivAt_const u (0:ℂ)).congr_of_eventuallyEq this
  exact (hV u).unique h0

/-- Passing from an integral over a large interval to the integral over `ℝ`. -/
theorem integral_eq_of_supp {A B : ℝ} (hAB : A < B) {g : ℝ → ℂ}
    (hg : ∀ u : ℝ, A ≤ |u| → g u = 0) :
    (∫ u in (-B)..B, g u) = ∫ u : ℝ, g u := by
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro u hu
  simp only [Function.mem_support, ne_eq] at hu
  have h : |u| < A := by
    by_contra hc
    exact hu (hg u (not_lt.1 hc))
  have h2 := abs_lt.1 h
  exact ⟨by linarith [h2.1], by linarith [h2.2]⟩

/-- **Integration by parts** for oscillatory Gaussian integrals against a compactly
supported factor with an explicit `u` in front. -/
theorem gauss_ibp (hb : b ≠ 0) {A : ℝ} (hA : 0 < A) {V V' : ℝ → ℂ}
    (hV : ∀ u, HasDerivAt V (V' u) u) (hV'c : Continuous V')
    (hsupp : ∀ u : ℝ, A ≤ |u| → V u = 0) :
    (∫ u : ℝ, Complex.exp (-b * (u:ℂ)^2) * ((u:ℂ) * V u))
      = (1/(2*b)) * ∫ u : ℝ, Complex.exp (-b * (u:ℂ)^2) * V' u := by
  have hVc : Continuous V := continuous_iff_continuousAt.2 fun x => (hV x).continuousAt
  set B := A + 1 with hB
  have hBA : A < B := by simp [hB]
  set F : ℝ → ℂ := fun u => -(1/(2*b)) * Complex.exp (-b * (u:ℂ)^2) * V u with hF
  have hFd : ∀ u : ℝ, HasDerivAt F
      (Complex.exp (-b * (u:ℂ)^2) * ((u:ℂ) * V u)
        - (1/(2*b)) * (Complex.exp (-b * (u:ℂ)^2) * V' u)) u := by
    intro u
    have h1 := ((hasDerivAt_cgauss b u).const_mul (-(1/(2*b)))).mul (hV u)
    change HasDerivAt
      ((fun y : ℝ ↦ -(1/(2*b)) * Complex.exp (-b * (y:ℂ)^2)) * V)
      (Complex.exp (-b * (u:ℂ)^2) * ((u:ℂ) * V u)
        - (1/(2*b)) * (Complex.exp (-b * (u:ℂ)^2) * V' u)) u
    convert h1 using 1 <;> try rfl
    field_simp [hb]
    ring
  have hint : IntervalIntegrable
      (fun u : ℝ => Complex.exp (-b * (u:ℂ)^2) * ((u:ℂ) * V u)
        - (1/(2*b)) * (Complex.exp (-b * (u:ℂ)^2) * V' u)) volume (-B) B := by
    apply Continuous.intervalIntegrable
    have hc : Continuous (fun u : ℝ => Complex.exp (-b * (u:ℂ)^2)) := continuous_cgauss b
    fun_prop
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hFd u) hint
  have hFB : F B = 0 := by
    simp [hF, hsupp B (by rw [abs_of_pos (by linarith)]; linarith)]
  have hFmB : F (-B) = 0 := by
    simp [hF, hsupp (-B) (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)]
  rw [hFB, hFmB, sub_zero] at key
  have hsplit : (∫ u in (-B)..B, Complex.exp (-b * (u:ℂ)^2) * ((u:ℂ) * V u))
      = (1/(2*b)) * ∫ u in (-B)..B, Complex.exp (-b * (u:ℂ)^2) * V' u := by
    have hc : Continuous (fun u : ℝ => Complex.exp (-b * (u:ℂ)^2)) := continuous_cgauss b
    have h1 : IntervalIntegrable (fun u : ℝ => Complex.exp (-b * (u:ℂ)^2) * ((u:ℂ) * V u))
        volume (-B) B := by apply Continuous.intervalIntegrable; fun_prop
    have h2 : IntervalIntegrable
        (fun u : ℝ => (1/(2*b)) * (Complex.exp (-b * (u:ℂ)^2) * V' u)) volume (-B) B := by
      apply Continuous.intervalIntegrable; fun_prop
    rw [intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul] at key
    linear_combination key
  have hc : Continuous (fun u : ℝ => Complex.exp (-b * (u:ℂ)^2)) := continuous_cgauss b
  have hhalf : A + 1/2 < B := by rw [hB]; linarith
  rw [integral_eq_of_supp hBA (g := fun u : ℝ => Complex.exp (-b * (u:ℂ)^2) * ((u:ℂ) * V u))
      (fun u hu => by simp [hsupp u hu]),
    integral_eq_of_supp hhalf (g := fun u : ℝ => Complex.exp (-b * (u:ℂ)^2) * V' u)
      (fun u hu => by
        have : A < |u| := by linarith
        simp [deriv_zero_far hV hsupp this])] at hsplit
  exact hsplit

/-! ### Van der Corput type bound -/

theorem hasDerivAt_ibpF (hb0 : b ≠ 0) {u : ℝ} (hu : u ≠ 0) {W W' : ℝ → ℂ}
    (hW : ∀ u, HasDerivAt W (W' u) u) :
    HasDerivAt (fun t : ℝ => Complex.exp (-b * (t:ℂ)^2) * W t * (-1/(2*b*(t:ℂ))))
      (Complex.exp (-b * (u:ℂ)^2) * W u
        + Complex.exp (-b * (u:ℂ)^2) * (-(W' u)/(2*b*(u:ℂ)) + W u/(2*b*(u:ℂ)^2))) u := by
  have hu' : ((u:ℂ)) ≠ 0 := by exact_mod_cast hu
  have hne : (2*b*(u:ℂ)) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hb0) hu'
  have h0 : HasDerivAt (fun t : ℝ => (t:ℂ)) 1 u := Complex.ofRealCLM.hasDerivAt
  have hG : HasDerivAt (fun t : ℝ => -1/(2*b*(t:ℂ))) (1/(2*b*(u:ℂ)^2)) u := by
    have h1 : HasDerivAt (fun t : ℝ => 2*b*(t:ℂ)) (2*b) u := by
      simpa using h0.const_mul (2*b)
    have h2 := (hasDerivAt_const u (-1:ℂ)).div h1 hne
    change HasDerivAt
      ((fun _ : ℝ ↦ (-1 : ℂ)) / fun t : ℝ ↦ 2*b*(t:ℂ))
      (1/(2*b*(u:ℂ)^2)) u
    convert h2 using 1 <;> try rfl
    field_simp [hb0, hu']
    ring
  have h := (((hasDerivAt_cgauss b u).mul (hW u)).mul hG)
  change HasDerivAt
    (((fun t : ℝ ↦ Complex.exp (-b*(t:ℂ)^2)) * W) *
      fun t : ℝ ↦ -1/(2*b*(t:ℂ)))
    (Complex.exp (-b * (u:ℂ)^2) * W u
      + Complex.exp (-b * (u:ℂ)^2) *
        (-(W' u)/(2*b*(u:ℂ)) + W u/(2*b*(u:ℂ)^2))) u
  convert h using 1 <;> try rfl
  field_simp [hb0, hu']
  simp only [Pi.mul_apply]
  ring

theorem integral_majorant {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) :
    (∫ u in c..d, (1/c + 1/u^2)) = (d-c)/c + (1/c - 1/d) := by
  have hd : d ≠ 0 := ne_of_gt (lt_of_lt_of_le hc hcd)
  have hmem : ∀ u ∈ Set.uIcc c d, 0 < u := by
    intro u hu
    rw [Set.uIcc_of_le hcd] at hu
    exact lt_of_lt_of_le hc hu.1
  have hH : ∀ u ∈ Set.uIcc c d, HasDerivAt (fun u : ℝ => u/c - 1/u) (1/c + 1/u^2) u := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (hmem u hu)
    have h1 : HasDerivAt (fun u : ℝ => u/c) (1/c) u := by
      simpa [div_eq_mul_inv] using (hasDerivAt_id u).mul_const (1/c)
    have h2 : HasDerivAt (fun u : ℝ => 1/u) (-(1/u^2)) u := by
      simpa only [one_div, inv_pow] using (hasDerivAt_inv hu0)
    have := h1.sub h2
    change HasDerivAt ((fun u : ℝ ↦ u/c) - fun u : ℝ ↦ 1/u) (1/c + 1/u^2) u
    convert this using 1 <;> try rfl
    ring
  have hint : IntervalIntegrable (fun u : ℝ => 1/c + 1/u^2) volume c d := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.add continuousOn_const
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro u hu
    have := hmem u hu
    positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hH hint]
  field_simp
  ring

/-- One-sided van der Corput bound: away from the stationary point `u = 0` an oscillatory
Gaussian integral is `O (1/‖b‖)`, with the constant degenerating as `c → 0`. -/
theorem gauss_vdC_right (hb : 0 ≤ b.re) (hb0 : b ≠ 0) {c d M : ℝ} (hc : 0 < c)
    (hcd : c ≤ d) {W W' : ℝ → ℂ} (hW : ∀ u, HasDerivAt W (W' u) u) (hW'c : Continuous W')
    (hWd : W d = 0) (hWb : ∀ u, ‖W u‖ ≤ M) (hW'b : ∀ u, ‖W' u‖ ≤ M) :
    ‖∫ u in c..d, Complex.exp (-b*(u:ℂ)^2) * W u‖
      ≤ M/(2*‖b‖*c) + (M/(2*‖b‖))*((d-c)/c + 1/c) := by
  have hWc : Continuous W := continuous_iff_continuousAt.2 fun x => (hW x).continuousAt
  have hM : 0 ≤ M := le_trans (norm_nonneg _) (hWb 0)
  have hbn : 0 < ‖b‖ := norm_pos_iff.2 hb0
  have hmem : ∀ u ∈ Set.uIcc c d, 0 < u := by
    intro u hu
    rw [Set.uIcc_of_le hcd] at hu
    exact lt_of_lt_of_le hc hu.1
  set E : ℝ → ℂ := fun u => Complex.exp (-b * (u:ℂ)^2) with hE
  set rest : ℝ → ℂ := fun u => -(W' u)/(2*b*(u:ℂ)) + W u/(2*b*(u:ℂ)^2) with hrest
  have hcont_rest : ContinuousOn (fun u : ℝ => E u * rest u) (Set.uIcc c d) := by
    apply ContinuousOn.mul (Continuous.continuousOn (by fun_prop))
    apply ContinuousOn.add
    · apply ContinuousOn.div (Continuous.continuousOn (by fun_prop))
        (Continuous.continuousOn (by fun_prop))
      intro u hu
      have h1 := hmem u hu
      have h2 : ((u:ℂ)) ≠ 0 := by exact_mod_cast ne_of_gt h1
      exact mul_ne_zero (mul_ne_zero two_ne_zero hb0) h2
    · apply ContinuousOn.div (Continuous.continuousOn (by fun_prop))
        (Continuous.continuousOn (by fun_prop))
      intro u hu
      have h1 := hmem u hu
      have h2 : ((u:ℂ)) ≠ 0 := by exact_mod_cast ne_of_gt h1
      exact mul_ne_zero (mul_ne_zero two_ne_zero hb0) (pow_ne_zero 2 h2)
  have hFTC : (∫ u in c..d, (E u * W u + E u * rest u))
      = (E d * W d * (-1/(2*b*(d:ℂ)))) - (E c * W c * (-1/(2*b*(c:ℂ)))) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro u hu
      exact hasDerivAt_ibpF hb0 (ne_of_gt (hmem u hu)) hW
    · apply ContinuousOn.intervalIntegrable
      exact ContinuousOn.add (Continuous.continuousOn (by fun_prop)) hcont_rest
  have hsplit : (∫ u in c..d, (E u * W u + E u * rest u))
      = (∫ u in c..d, E u * W u) + ∫ u in c..d, E u * rest u := by
    apply intervalIntegral.integral_add
    · exact Continuous.intervalIntegrable (by fun_prop) _ _
    · exact ContinuousOn.intervalIntegrable hcont_rest
  -- pointwise bound on the remainder integrand
  have hpt : ∀ u ∈ Set.uIcc c d, ‖E u * rest u‖ ≤ (M/(2*‖b‖))*(1/c + 1/u^2) := by
    intro u hu
    have hu0 : 0 < u := hmem u hu
    have huc : c ≤ u := by
      rw [Set.uIcc_of_le hcd] at hu; exact hu.1
    have h1 : ‖-(W' u)/(2*b*(u:ℂ))‖ = ‖W' u‖/(2*‖b‖*u) := by
      rw [norm_div, norm_neg]
      congr 1
      simp [abs_of_pos hu0]
    have h2 : ‖W u/(2*b*(u:ℂ)^2)‖ = ‖W u‖/(2*‖b‖*u^2) := by
      rw [norm_div]
      congr 1
      simp [abs_of_pos hu0]
    have hE1 : ‖E u‖ ≤ 1 := norm_cgauss_le_one hb u
    have hrb : ‖rest u‖ ≤ M/(2*‖b‖*u) + M/(2*‖b‖*u^2) := by
      calc ‖rest u‖ ≤ ‖-(W' u)/(2*b*(u:ℂ))‖ + ‖W u/(2*b*(u:ℂ)^2)‖ := norm_add_le _ _
        _ = ‖W' u‖/(2*‖b‖*u) + ‖W u‖/(2*‖b‖*u^2) := by rw [h1, h2]
        _ ≤ M/(2*‖b‖*u) + M/(2*‖b‖*u^2) := by gcongr <;> [exact hW'b u; exact hWb u]
    have hfin : M/(2*‖b‖*u) + M/(2*‖b‖*u^2) ≤ (M/(2*‖b‖))*(1/c + 1/u^2) := by
      have hle : M/(2*‖b‖*u) ≤ M/(2*‖b‖*c) := by
        apply div_le_div_of_nonneg_left hM (by positivity)
        nlinarith
      have : (M/(2*‖b‖))*(1/c + 1/u^2) = M/(2*‖b‖*c) + M/(2*‖b‖*u^2) := by
        field_simp
      rw [this]
      linarith
    calc ‖E u * rest u‖ = ‖E u‖ * ‖rest u‖ := norm_mul _ _
      _ ≤ 1 * (M/(2*‖b‖*u) + M/(2*‖b‖*u^2)) := by
          apply mul_le_mul hE1 hrb (norm_nonneg _) zero_le_one
      _ = M/(2*‖b‖*u) + M/(2*‖b‖*u^2) := one_mul _
      _ ≤ (M/(2*‖b‖))*(1/c + 1/u^2) := hfin
  have hintM : IntervalIntegrable (fun u : ℝ => (M/(2*‖b‖))*(1/c + 1/u^2)) volume c d := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.add continuousOn_const
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro u hu
    have := hmem u hu
    positivity
  have hbound2 : ‖∫ u in c..d, E u * rest u‖ ≤ (M/(2*‖b‖))*((d-c)/c + 1/c) := by
    have h1 : ‖∫ u in c..d, E u * rest u‖ ≤ ∫ u in c..d, ‖E u * rest u‖ :=
      intervalIntegral.norm_integral_le_integral_norm hcd
    have h2 : (∫ u in c..d, ‖E u * rest u‖) ≤ ∫ u in c..d, (M/(2*‖b‖))*(1/c + 1/u^2) := by
      apply intervalIntegral.integral_mono_on hcd
        (ContinuousOn.intervalIntegrable hcont_rest.norm) hintM
      intro u hu
      exact hpt u (by rw [Set.uIcc_of_le hcd]; exact hu)
    have h3 : (∫ u in c..d, (M/(2*‖b‖))*(1/c + 1/u^2))
        = (M/(2*‖b‖)) * ((d-c)/c + (1/c - 1/d)) := by
      rw [intervalIntegral.integral_const_mul, integral_majorant hc hcd]
    have h4 : (M/(2*‖b‖)) * ((d-c)/c + (1/c - 1/d)) ≤ (M/(2*‖b‖))*((d-c)/c + 1/c) := by
      have hd : 0 < d := lt_of_lt_of_le hc hcd
      have : (0:ℝ) ≤ M/(2*‖b‖) := by positivity
      nlinarith [this, le_of_lt (one_div_pos.2 hd)]
    linarith [h1, h2, h3 ▸ h2]
  have hbound1 : ‖E c * W c * (-1/(2*b*(c:ℂ)))‖ ≤ M/(2*‖b‖*c) := by
    have h1 : ‖(-1/(2*b*(c:ℂ)))‖ = 1/(2*‖b‖*c) := by
      rw [norm_div, norm_neg]
      simp [abs_of_pos hc]
    rw [norm_mul, norm_mul, h1]
    have hE1 : ‖E c‖ ≤ 1 := norm_cgauss_le_one hb c
    have : ‖E c‖ * ‖W c‖ ≤ 1 * M := by
      apply mul_le_mul hE1 (hWb c) (norm_nonneg _) zero_le_one
    calc ‖E c‖ * ‖W c‖ * (1/(2*‖b‖*c)) ≤ (1*M) * (1/(2*‖b‖*c)) := by
          apply mul_le_mul_of_nonneg_right this (by positivity)
      _ = M/(2*‖b‖*c) := by field_simp
  have hkey : (∫ u in c..d, E u * W u)
      = -(E c * W c * (-1/(2*b*(c:ℂ)))) - ∫ u in c..d, E u * rest u := by
    rw [hsplit] at hFTC
    rw [hWd] at hFTC
    simp only [mul_zero, zero_mul] at hFTC
    linear_combination hFTC
  rw [hkey]
  calc ‖-(E c * W c * (-1/(2*b*(c:ℂ)))) - ∫ u in c..d, E u * rest u‖
      ≤ ‖E c * W c * (-1/(2*b*(c:ℂ)))‖ + ‖∫ u in c..d, E u * rest u‖ := by
        rw [← norm_neg (E c * W c * (-1/(2*b*(c:ℂ))))]
        exact norm_sub_le _ _
    _ ≤ M/(2*‖b‖*c) + (M/(2*‖b‖))*((d-c)/c + 1/c) := add_le_add hbound1 hbound2

/-- Auxiliary form of the van der Corput bound with the scale `δ` (satisfying `‖b‖δ² = 1`)
given explicitly. -/
theorem gauss_vdC_aux (hb : 0 ≤ b.re) (hb0 : b ≠ 0) {A M δ : ℝ} (hA : 1 ≤ A)
    (hδpos : 0 < δ) (hδ1 : δ ≤ 1) (hbδ : ‖b‖ * δ * δ = 1)
    {W W' : ℝ → ℂ} (hW : ∀ u, HasDerivAt W (W' u) u) (hW'c : Continuous W')
    (hsupp : ∀ u : ℝ, A ≤ |u| → W u = 0) (hWb : ∀ u, ‖W u‖ ≤ M) (hW'b : ∀ u, ‖W' u‖ ≤ M) :
    ‖∫ u : ℝ, Complex.exp (-b*(u:ℂ)^2) * W u‖ ≤ M*(A+5)*δ := by
  have hWc : Continuous W := continuous_iff_continuousAt.2 fun x => (hW x).continuousAt
  have hM : 0 ≤ M := le_trans (norm_nonneg _) (hWb 0)
  have hbn : 0 < ‖b‖ := norm_pos_iff.2 hb0
  have hbd : ‖b‖ * δ = 1/δ := by
    rw [eq_div_iff (ne_of_gt hδpos)]; exact hbδ
  have hinv : 1/(‖b‖*δ) = δ := by rw [hbd, one_div_one_div]
  have hδB : δ ≤ A + 1 := by linarith
  have hcont : Continuous (fun u : ℝ => Complex.exp (-b*(u:ℂ)^2) * W u) := by
    have := continuous_cgauss b
    fun_prop
  have hkey : ∀ (V V' : ℝ → ℂ), (∀ u, HasDerivAt V (V' u) u) → Continuous V' →
      V (A+1) = 0 → (∀ u, ‖V u‖ ≤ M) → (∀ u, ‖V' u‖ ≤ M) →
      ‖∫ u in δ..(A+1), Complex.exp (-b*(u:ℂ)^2) * V u‖ ≤ (M*δ/2)*(A+3) := by
    intro V V' hV hV'c hVB hVb hV'b
    have h := gauss_vdC_right hb hb0 hδpos hδB hV hV'c hVB hVb hV'b
    refine le_trans h ?_
    have e1 : M/(2*‖b‖*δ) = M*δ/2 := by
      rw [show 2*‖b‖*δ = 2*(‖b‖*δ) by ring, hbd]
      field_simp
    have e2 : (M/(2*‖b‖))*(((A+1)-δ)/δ + 1/δ) = (M*δ/2)*((A+1)-δ+1) := by
      have h1 : ((A+1)-δ)/δ + 1/δ = ((A+1)-δ+1)/δ := by
        field_simp
      rw [h1]
      have h2 : (M/(2*‖b‖))*(((A+1)-δ+1)/δ) = (M*((A+1)-δ+1)/2) * (1/(‖b‖*δ)) := by
        field_simp
      rw [h2, hinv]
      ring
    rw [e1, e2]
    have h3 : (M*δ/2)*((A+1)-δ+1) ≤ (M*δ/2)*(A+2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    linarith
  have hii : ∀ x y : ℝ, IntervalIntegrable
      (fun u : ℝ => Complex.exp (-b*(u:ℂ)^2) * W u) volume x y :=
    fun x y => hcont.intervalIntegrable x y
  have hfull : (∫ u : ℝ, Complex.exp (-b*(u:ℂ)^2) * W u)
      = ∫ u in (-(A+1))..(A+1), Complex.exp (-b*(u:ℂ)^2) * W u := by
    exact (integral_eq_of_supp (show A < A+1 by linarith)
      (g := fun u : ℝ => Complex.exp (-b*(u:ℂ)^2) * W u) (fun u hu => by simp [hsupp u hu])).symm
  have hsplit : (∫ u in (-(A+1))..(A+1), Complex.exp (-b*(u:ℂ)^2) * W u)
      = ((∫ u in (-(A+1))..(-δ), Complex.exp (-b*(u:ℂ)^2) * W u)
        + (∫ u in (-δ)..δ, Complex.exp (-b*(u:ℂ)^2) * W u))
        + (∫ u in δ..(A+1), Complex.exp (-b*(u:ℂ)^2) * W u) := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals (hii (-(A+1)) (-δ)) (hii (-δ) δ)
    have h2 := intervalIntegral.integral_add_adjacent_intervals (hii (-(A+1)) δ) (hii δ (A+1))
    rw [h1, h2]
  have hWB : W (A+1) = 0 := hsupp (A+1) (by rw [abs_of_pos (by linarith)]; linarith)
  have hright := hkey W W' hW hW'c hWB hWb hW'b
  have hleft : ‖∫ u in (-(A+1))..(-δ), Complex.exp (-b*(u:ℂ)^2) * W u‖ ≤ (M*δ/2)*(A+3) := by
    have hrefl : (∫ u in (-(A+1))..(-δ), Complex.exp (-b*(u:ℂ)^2) * W u)
        = ∫ u in δ..(A+1), Complex.exp (-b*(u:ℂ)^2) * W (-u) := by
      have h := (intervalIntegral.integral_comp_neg
        (a := δ) (b := A+1) (fun u : ℝ => Complex.exp (-b*(u:ℂ)^2) * W u)).symm
      refine h.trans (intervalIntegral.integral_congr ?_)
      intro u _
      simp only
      congr 1
      push_cast
      ring_nf
    rw [hrefl]
    have hWneg : ∀ u : ℝ, HasDerivAt (fun t : ℝ => W (-t)) (-(W' (-u))) u := by
      intro u
      change HasDerivAt (W ∘ fun t : ℝ => -t) (-(W' (-u))) u
      simpa only [neg_smul, one_smul] using
        HasDerivAt.scomp u (hW (-u)) (hasDerivAt_neg' u)
    have hWmB : W (-(A+1)) = 0 :=
      hsupp (-(A+1)) (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
    exact hkey (fun t => W (-t)) (fun t => -(W' (-t))) hWneg (by fun_prop) hWmB
      (fun u => hWb (-u)) (fun u => by rw [norm_neg]; exact hW'b (-u))
  have hmid : ‖∫ u in (-δ)..δ, Complex.exp (-b*(u:ℂ)^2) * W u‖ ≤ M * (2*δ) := by
    have h : ‖∫ u in (-δ)..δ, Complex.exp (-b*(u:ℂ)^2) * W u‖ ≤ M * |δ - (-δ)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x _
      calc ‖Complex.exp (-b*(x:ℂ)^2) * W x‖ = ‖Complex.exp (-b*(x:ℂ)^2)‖ * ‖W x‖ := norm_mul _ _
        _ ≤ 1 * M := mul_le_mul (norm_cgauss_le_one hb x) (hWb x) (norm_nonneg _) zero_le_one
        _ = M := one_mul _
    rw [show δ - (-δ) = 2*δ by ring, abs_of_pos (by linarith)] at h
    exact h
  rw [hfull, hsplit]
  have hstep : ‖((∫ u in (-(A+1))..(-δ), Complex.exp (-b*(u:ℂ)^2) * W u)
        + (∫ u in (-δ)..δ, Complex.exp (-b*(u:ℂ)^2) * W u))
        + (∫ u in δ..(A+1), Complex.exp (-b*(u:ℂ)^2) * W u)‖
      ≤ ((M*δ/2)*(A+3) + M*(2*δ)) + (M*δ/2)*(A+3) := by
    refine le_trans (norm_add_le _ _) ?_
    refine add_le_add ?_ hright
    exact le_trans (norm_add_le _ _) (add_le_add hleft hmid)
  refine le_trans hstep (le_of_eq ?_)
  ring

/-- **Van der Corput / stationary phase bound.**  For a compactly supported `C¹` amplitude the
oscillatory Gaussian integral is `O (‖b‖^{-1/2})`, uniformly on the closed right half plane. -/
theorem gauss_vdC (hb : 0 ≤ b.re) (hb1 : 1 ≤ ‖b‖) {A M : ℝ} (hA : 1 ≤ A)
    {W W' : ℝ → ℂ} (hW : ∀ u, HasDerivAt W (W' u) u) (hW'c : Continuous W')
    (hsupp : ∀ u : ℝ, A ≤ |u| → W u = 0) (hWb : ∀ u, ‖W u‖ ≤ M) (hW'b : ∀ u, ‖W' u‖ ≤ M) :
    ‖∫ u : ℝ, Complex.exp (-b*(u:ℂ)^2) * W u‖ ≤ M*(A+5)/Real.sqrt ‖b‖ := by
  have hbn : 0 < ‖b‖ := lt_of_lt_of_le zero_lt_one hb1
  have hb0 : b ≠ 0 := norm_pos_iff.1 hbn
  have hsq : 0 < Real.sqrt ‖b‖ := Real.sqrt_pos.2 hbn
  have hsq1 : 1 ≤ Real.sqrt ‖b‖ := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hb1
  have hδpos : 0 < 1 / Real.sqrt ‖b‖ := by positivity
  have hδ1 : 1 / Real.sqrt ‖b‖ ≤ 1 := by rw [div_le_one hsq]; exact hsq1
  have hbδ : ‖b‖ * (1 / Real.sqrt ‖b‖) * (1 / Real.sqrt ‖b‖) = 1 := by
    calc ‖b‖ * (1 / Real.sqrt ‖b‖) * (1 / Real.sqrt ‖b‖)
        = ‖b‖ / (Real.sqrt ‖b‖ * Real.sqrt ‖b‖) := by ring
      _ = ‖b‖ / ‖b‖ := by rw [Real.mul_self_sqrt hbn.le]
      _ = 1 := div_self (ne_of_gt hbn)
  have h := gauss_vdC_aux hb hb0 hA hδpos hδ1 hbδ hW hW'c hsupp hWb hW'b
  calc ‖∫ u : ℝ, Complex.exp (-b*(u:ℂ)^2) * W u‖ ≤ M*(A+5)*(1 / Real.sqrt ‖b‖) := h
    _ = M*(A+5)/Real.sqrt ‖b‖ := by ring

end OscGauss

/-! ## A smooth cutoff and the explicit amplitude of the `m = 2` saddle -/

section Cutoff

/-- The bump function used as a cutoff: it is `1` on `[-1/2,1/2]` and vanishes off `(-1,1)`. -/
noncomputable def bumpHalf : ContDiffBump (0:ℝ) := ⟨1/2, 1, by norm_num, by norm_num⟩

/-- A smooth cutoff, equal to `1` on `[-1/2,1/2]` and supported in `[-1,1]`. -/
noncomputable def cutoff (u : ℝ) : ℝ := bumpHalf u

theorem cutoff_smooth : ContDiff ℝ (⊤ : ℕ∞) cutoff := bumpHalf.contDiff

theorem cutoff_one {u : ℝ} (h : |u| ≤ 1/2) : cutoff u = 1 := by
  apply bumpHalf.one_of_mem_closedBall
  simpa [Real.dist_eq, bumpHalf] using h

theorem cutoff_zero {u : ℝ} (h : 1 ≤ |u|) : cutoff u = 0 := by
  apply bumpHalf.zero_of_le_dist
  simpa [Real.dist_eq, bumpHalf] using h

theorem cutoff_nonneg (u : ℝ) : 0 ≤ cutoff u := bumpHalf.nonneg
theorem cutoff_le_one (u : ℝ) : cutoff u ≤ 1 := bumpHalf.le_one

theorem cutoff_continuous : Continuous cutoff := cutoff_smooth.continuous

/-- A continuous function vanishing outside a bounded set is bounded. -/
theorem bounded_of_supp {f : ℝ → ℂ} (hf : Continuous f) {A : ℝ}
    (h0 : ∀ u, A ≤ |u| → f u = 0) : ∃ M : ℝ, 0 ≤ M ∧ ∀ u, ‖f u‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -A) (b := A)).exists_bound_of_continuousOn
    (hf.continuousOn (s := Set.Icc (-A) A))
  refine ⟨max M 0, le_max_right _ _, fun u => ?_⟩
  by_cases h : |u| ≤ A
  · have hu : u ∈ Set.Icc (-A) A := by
      rw [Set.mem_Icc]
      exact ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩
    exact le_trans (hM u hu) (le_max_left _ _)
  · rw [h0 u (le_of_lt (not_le.1 h))]
    simpa using le_max_right M 0

/-- Multiplying by the cutoff makes a function that is smooth on `(-2,2)` globally smooth. -/
theorem contDiff_cutoff_mul {F : ℝ → ℝ} (hF : ∀ u : ℝ, |u| < 2 → ContDiffAt ℝ (⊤:ℕ∞) F u) :
    ContDiff ℝ (⊤ : ℕ∞) (fun u => cutoff u * F u) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases h : |u| < 2
  · exact (cutoff_smooth.contDiffAt).mul (hF u h)
  · have hev : (fun v => cutoff v * F v) =ᶠ[nhds u] fun _ => (0:ℝ) := by
      have hset : {v : ℝ | 1 < |v|} ∈ nhds u := by
        refine IsOpen.mem_nhds (isOpen_lt continuous_const continuous_abs) ?_
        simp only [Set.mem_setOf_eq]
        linarith [not_lt.1 h]
      filter_upwards [hset] with v hv
      simp [cutoff_zero hv.le]
    exact contDiffAt_const.congr_of_eventuallyEq hev

theorem cutoff_mul_supp {F : ℝ → ℝ} {u : ℝ} (h : 1 ≤ |u|) : cutoff u * F u = 0 := by
  simp [cutoff_zero h]

/-- `√(1 - u²/4)`, positive on `(-2,2)`. -/
noncomputable def sroot (u : ℝ) : ℝ := Real.sqrt (1 - u^2/4)

theorem sroot_pos {u : ℝ} (h : |u| < 2) : 0 < sroot u := by
  apply Real.sqrt_pos.2
  nlinarith [abs_nonneg u, sq_abs u, (abs_lt.1 h).1, (abs_lt.1 h).2]

theorem sroot_sq {u : ℝ} (h : |u| ≤ 2) : (sroot u)^2 = 1 - u^2/4 := by
  apply Real.sq_sqrt
  nlinarith [sq_abs u, abs_nonneg u]

theorem sroot_zero : sroot 0 = 1 := by simp [sroot]

theorem contDiffAt_sroot {u : ℝ} (h : |u| < 2) : ContDiffAt ℝ (⊤:ℕ∞) sroot u := by
  apply ContDiffAt.sqrt
  · exact (contDiff_const.sub ((contDiff_id.pow 2).div_const 4)).contDiffAt
  · have := sroot_pos h
    rw [sroot] at this
    intro hc
    rw [hc] at this
    simp at this

/-- The amplitude `(1 - u²/4)^{-1/2}` of the `m = 2` saddle point integral. -/
noncomputable def amp (u : ℝ) : ℝ := (sroot u)⁻¹

theorem amp_zero : amp 0 = 1 := by simp [amp, sroot_zero]

theorem contDiffAt_amp {u : ℝ} (h : |u| < 2) : ContDiffAt ℝ (⊤:ℕ∞) amp u :=
  (contDiffAt_sroot h).inv (ne_of_gt (sroot_pos h))

/-- The explicit smooth quotient `(amp u - 1)/u² = 1/(4√(1-u²/4) + 4 - u²)`. -/
noncomputable def Pfun (u : ℝ) : ℝ := (4 * sroot u + 4 - u^2)⁻¹

theorem Pfun_denom_pos {u : ℝ} (h : |u| < 2) : 0 < 4 * sroot u + 4 - u^2 := by
  have h1 : 0 < sroot u := sroot_pos h
  have h2 : (sroot u)^2 = 1 - u^2/4 := sroot_sq h.le
  nlinarith

theorem Pfun_zero : Pfun 0 = 1/8 := by norm_num [Pfun, sroot_zero]

theorem contDiffAt_Pfun {u : ℝ} (h : |u| < 2) : ContDiffAt ℝ (⊤:ℕ∞) Pfun u := by
  apply ContDiffAt.inv
  · exact ((contDiffAt_const.mul (contDiffAt_sroot h)).add contDiffAt_const).sub
      ((contDiff_id.pow 2).contDiffAt)
  · exact ne_of_gt (Pfun_denom_pos h)

/-- The key algebraic identity `amp u - 1 = u² · Pfun u`. -/
theorem amp_sub_one {u : ℝ} (h : |u| < 2) : amp u - 1 = u^2 * Pfun u := by
  have h1 : 0 < sroot u := sroot_pos h
  have h2 : (sroot u)^2 = 1 - u^2/4 := sroot_sq h.le
  have h3 : 0 < 4 * sroot u + 4 - u^2 := Pfun_denom_pos h
  have key : (amp u - 1) * (4 * sroot u + 4 - u^2) = u^2 := by
    rw [amp]
    field_simp
    nlinarith [h1, h2]
  have hP : u^2 * Pfun u = u^2 / (4 * sroot u + 4 - u^2) := by rw [Pfun]; ring
  rw [hP, eq_div_iff (ne_of_gt h3)]
  exact key

end Cutoff

end Q776
