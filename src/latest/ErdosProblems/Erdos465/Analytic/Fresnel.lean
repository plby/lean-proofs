/-
This analytic helper is adapted from the fully proved Q776 development at
https://github.com/l-pommeret/rms-math-proofs, revision
a5c24c8190191bc9491259035073a9230b9f6727, for Lean/Mathlib v4.33.0.
-/

import ErdosProblems.Erdos465.Analytic.StationaryPhase

/-!
# Q776 — the Fresnel integral of a smooth cutoff

The purpose of this file is the estimate

  `‖∫ u, exp (-b u²) * cutoff u - (π/b)^(1/2)‖ ≤ K / ‖b‖³`

valid for **all** `b` in the closed right half plane with `‖b‖ ≥ 1`, in particular on the
imaginary axis, where the Gaussian integral is not absolutely convergent.  Mathlib only
provides the Gaussian value `∫ exp (-b u²) = (π/b)^(1/2)` for `0 < re b`; the above is obtained
by three integrations by parts in the tail `1 - cutoff` (each gaining a factor `1/(2b)`) and a
limiting argument `re b ↓ 0`.
-/

open scoped Real
open Complex MeasureTheory

namespace Q776

/-! ## A hierarchy of tail functions -/

/-- `TailFun a k c h` says: `h` is smooth, vanishes on `|u| ≤ a` (with `a > 0`), and equals
`c / u ^ k` for `|u| > 1`. -/
structure TailFun (a : ℝ) (k : ℕ) (c : ℝ) (h : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) h
  apos : 0 < a
  zero_near : ∀ u, |u| ≤ a → h u = 0
  far : ∀ u, 1 < |u| → h u = c / u ^ k

theorem TailFun.bounded {a : ℝ} {k : ℕ} {c : ℝ} {h : ℝ → ℝ} (H : TailFun a k c h) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u, |h u| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-1:ℝ)) (b := 1)).exists_bound_of_continuousOn
    (H.smooth.continuous.continuousOn (s := Set.Icc (-1:ℝ) 1))
  refine ⟨max (max M 0) |c|, le_trans (le_max_right M 0) (le_max_left _ _), fun u => ?_⟩
  by_cases hu : |u| ≤ 1
  · have hmem : u ∈ Set.Icc (-1:ℝ) 1 := by
      rw [Set.mem_Icc]
      exact ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩
    have := hM u hmem
    simp only [Real.norm_eq_abs] at this
    exact le_trans this (le_trans (le_max_left M 0) (le_max_left _ _))
  · push Not at hu
    rw [H.far u hu]
    have h1 : (1:ℝ) ≤ |u| ^ k := one_le_pow₀ hu.le
    have : |c / u ^ k| = |c| / |u| ^ k := by
      rw [abs_div, abs_pow]
    rw [this]
    refine le_trans ?_ (le_max_right _ _)
    exact div_le_self (abs_nonneg c) h1

theorem TailFun.integrable {a : ℝ} {k : ℕ} {c : ℝ} {h : ℝ → ℝ} (H : TailFun a k c h)
    (hk : 2 ≤ k) : Integrable h := by
  obtain ⟨M, hM0, hM⟩ := H.bounded
  refine Integrable.mono' (g := fun u : ℝ => (2 * (M + |c|)) * (1 + u ^ 2)⁻¹)
    (integrable_inv_one_add_sq.const_mul _) H.smooth.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs]
  have hpos : (0:ℝ) < 1 + u ^ 2 := by positivity
  have hMc : (0:ℝ) ≤ 2 * (M + |c|) := by linarith [abs_nonneg c]
  by_cases hu : |u| ≤ 1
  · have hu2 : u ^ 2 ≤ 1 := by nlinarith [sq_abs u, abs_nonneg u]
    have h2 : (1:ℝ)/2 ≤ (1 + u^2)⁻¹ := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le hpos (by linarith)
    have hstep : 2 * (M + |c|) * (1/2 : ℝ) ≤ 2 * (M + |c|) * (1 + u^2)⁻¹ :=
      mul_le_mul_of_nonneg_left h2 hMc
    have := hM u
    linarith [abs_nonneg c]
  · push Not at hu
    have hupos : (0:ℝ) < |u| := by linarith
    have hu2 : (1:ℝ) ≤ u ^ 2 := by nlinarith [sq_abs u]
    have habs : |h u| = |c| / |u| ^ k := by rw [H.far u hu, abs_div, abs_pow]
    have hk2 : |u| ^ 2 ≤ |u| ^ k := pow_le_pow_right₀ hu.le hk
    have hposk : (0:ℝ) < |u| ^ k := pow_pos hupos k
    have hpos2 : (0:ℝ) < |u| ^ 2 := pow_pos hupos 2
    have hle : |c| / |u| ^ k ≤ |c| / |u| ^ 2 := by
      rw [div_le_div_iff₀ hposk hpos2]
      nlinarith [abs_nonneg c]
    rw [sq_abs] at hle
    have h4 : (1 : ℝ) / (2 * u^2) ≤ (1 + u^2)⁻¹ := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le hpos (by linarith)
    have hfin : |c| / u ^ 2 ≤ (2 * (M + |c|)) * (1 + u ^ 2)⁻¹ := by
      have e1 : |c| / u^2 = (2 * |c|) * (1/(2*u^2)) := by
        field_simp
      rw [e1]
      have e2 : (2 * |c|) * (1/(2*u^2)) ≤ (2 * |c|) * (1+u^2)⁻¹ :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
      refine le_trans e2 ?_
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      linarith [abs_nonneg c]
    rw [habs]
    linarith

/-- Division by the coordinate: preserves the tail hierarchy, raising the decay order. -/
noncomputable def tdiv (h : ℝ → ℝ) (u : ℝ) : ℝ := h u / u

theorem TailFun.tdiv {a : ℝ} {k : ℕ} {c : ℝ} {h : ℝ → ℝ} (H : TailFun a k c h) :
    TailFun a (k + 1) c (Q776.tdiv h) := by
  have hzero : ∀ u : ℝ, |u| ≤ a → Q776.tdiv h u = 0 := by
    intro u hu
    simp [Q776.tdiv, H.zero_near u hu]
  refine ⟨?_, H.apos, hzero, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro u
    by_cases hu : |u| < a
    · have hev : Q776.tdiv h =ᶠ[nhds u] fun _ => (0:ℝ) := by
        have hset : {v : ℝ | |v| < a} ∈ nhds u :=
          IsOpen.mem_nhds (isOpen_lt continuous_abs continuous_const) hu
        filter_upwards [hset] with v hv using hzero v hv.le
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · push Not at hu
      have hune : u ≠ 0 := by
        intro h0
        rw [h0] at hu
        simp at hu
        linarith [H.apos]
      exact H.smooth.contDiffAt.div contDiffAt_id hune
  · intro u hu
    have hune : u ≠ 0 := by
      intro h0; rw [h0] at hu; simp at hu; linarith
    have hdef : Q776.tdiv h u = h u / u := rfl
    rw [hdef, H.far u hu]
    field_simp
    ring

theorem TailFun.deriv_tail {a : ℝ} {k : ℕ} {c : ℝ} {h : ℝ → ℝ} (H : TailFun a k c h)
    (hk : 1 ≤ k) : TailFun (a/2) (k + 1) (-(k * c)) (deriv h) := by
  have hdiff : Differentiable ℝ h := (contDiff_infty_iff_deriv.1 H.smooth).1
  refine ⟨(contDiff_infty_iff_deriv.1 H.smooth).2, by linarith [H.apos], ?_, ?_⟩
  · intro u hu
    have hu' : |u| < a := by linarith [H.apos]
    have hev : h =ᶠ[nhds u] fun _ => (0:ℝ) := by
      have hset : {v : ℝ | |v| < a} ∈ nhds u :=
        IsOpen.mem_nhds (isOpen_lt continuous_abs continuous_const) hu'
      filter_upwards [hset] with v hv using H.zero_near v hv.le
    rw [Filter.EventuallyEq.deriv_eq hev]
    simp
  · intro u hu
    have hune : u ≠ 0 := by
      intro h0; rw [h0] at hu; simp at hu; linarith
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hev : h =ᶠ[nhds u] fun x : ℝ => c / x ^ (j+1) := by
      have hset : {v : ℝ | 1 < |v|} ∈ nhds u :=
        IsOpen.mem_nhds (isOpen_lt continuous_const continuous_abs) hu
      filter_upwards [hset] with v hv using H.far v hv
    rw [Filter.EventuallyEq.deriv_eq hev]
    have hp : HasDerivAt (fun x : ℝ => x ^ (j+1)) (((j:ℝ)+1) * u ^ j) u := by
      simpa using hasDerivAt_pow (j+1) u
    have hd : HasDerivAt (fun x : ℝ => c / x ^ (j+1))
        ((0 * u ^ (j+1) - c * (((j:ℝ)+1) * u ^ j)) / (u ^ (j+1))^2) u :=
      (hasDerivAt_const u c).div hp (pow_ne_zero _ hune)
    rw [hd.deriv]
    push_cast
    field_simp
    ring

/-! ## Integration by parts in the tail -/

theorem integrable_gauss_mul {b : ℂ} (hb : 0 < b.re) {g : ℝ → ℂ} (hg : Continuous g) {M : ℝ}
    (hM : ∀ u, ‖g u‖ ≤ M) :
    Integrable (fun u : ℝ => Complex.exp (-b * (u:ℂ)^2) * g u) := by
  have := (integrable_cexp_neg_mul_sq hb).bdd_mul (f := g) hg.aestronglyMeasurable
    (c := M) (Filter.Eventually.of_forall hM)
  simpa [mul_comm] using this

theorem integrable_gauss_mul_real {b : ℂ} (hb : 0 < b.re) {g : ℝ → ℝ}
    (hg : Continuous g) {M : ℝ} (hM : ∀ u, |g u| ≤ M) :
    Integrable (fun u : ℝ => Complex.exp (-b * (u:ℂ)^2) * (g u : ℂ)) := by
  refine integrable_gauss_mul hb (by fun_prop) (M := M) fun u => ?_
  simpa using hM u

theorem tail_ibp {b : ℂ} (hb : 0 < b.re) {a : ℝ} {k : ℕ} {c : ℝ} {h : ℝ → ℝ}
    (H : TailFun a k c h) :
    ∫ u : ℝ, Complex.exp (-b * (u:ℂ)^2) * (h u : ℂ)
      = (1/(2*b)) * ∫ u : ℝ, Complex.exp (-b * (u:ℂ)^2) * ((deriv (Q776.tdiv h) u : ℝ) : ℂ) := by
  have hbne : b ≠ 0 := by intro h0; rw [h0] at hb; simp at hb
  set v : ℝ → ℂ := fun u => ((Q776.tdiv h u : ℝ) : ℂ) with hv
  set v' : ℝ → ℂ := fun u => ((deriv (Q776.tdiv h) u : ℝ) : ℂ) with hv'
  set P : ℝ → ℂ := fun u => Complex.exp (-b * (u:ℂ)^2) with hP
  set P' : ℝ → ℂ := fun u => Complex.exp (-b * (u:ℂ)^2) * (-b * (2*u)) with hP'
  have hTd := H.tdiv
  have hTd' := hTd.deriv_tail (by omega)
  obtain ⟨M, hM0, hM⟩ := H.bounded
  obtain ⟨M1, hM10, hM1⟩ := hTd.bounded
  obtain ⟨M2, hM20, hM2⟩ := hTd'.bounded
  -- the three integrability hypotheses
  have hPv' : Integrable (P * v') := by
    have := integrable_gauss_mul_real hb (g := deriv (Q776.tdiv h))
      hTd'.smooth.continuous (M := M2) hM2
    simpa [Pi.mul_def, hP, hv'] using this
  have hPv : Integrable (P * v) := by
    have := integrable_gauss_mul_real hb (g := Q776.tdiv h) hTd.smooth.continuous (M := M1) hM1
    simpa [Pi.mul_def, hP, hv] using this
  have hxv : ∀ u : ℝ, (u:ℂ) * v u = (h u : ℂ) := by
    intro u
    rcases eq_or_ne u 0 with rfl | hu
    · simp [hv, Q776.tdiv, H.zero_near 0 (by simpa using H.apos.le)]
    · have hne : (u:ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hu
      have hdef : Q776.tdiv h u = h u / u := rfl
      change (u:ℂ) * ((Q776.tdiv h u : ℝ) : ℂ) = (h u : ℂ)
      rw [hdef]
      push_cast
      field_simp
  have hP'v : Integrable (P' * v) := by
    have hEq : (P' * v) = fun u : ℝ => (-b * 2) * (Complex.exp (-b * (u:ℂ)^2) * (h u : ℂ)) := by
      funext u
      simp only [hP', Pi.mul_apply]
      rw [← hxv u]
      ring
    rw [hEq]
    exact (integrable_gauss_mul_real hb H.smooth.continuous (M := M) hM).const_mul _
  have hdu : ∀ u : ℝ, HasDerivAt P (P' u) u := fun u => hasDerivAt_cgauss b u
  have hdv : ∀ u : ℝ, HasDerivAt v (v' u) u := by
    intro u
    have hd : HasDerivAt (Q776.tdiv h) (deriv (Q776.tdiv h) u) u :=
      ((contDiff_infty_iff_deriv.1 hTd.smooth).1 u).hasDerivAt
    exact hd.ofReal_comp
  have hIBP := MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun u _ ↦ hdu u) (fun u _ ↦ hdv u) hPv' hP'v hPv
  -- rewrite `∫ P' v` as `-2b ∫ P h`
  have hEq2 : ∫ u : ℝ, P' u * v u
      = (-b * 2) * ∫ u : ℝ, Complex.exp (-b * (u:ℂ)^2) * (h u : ℂ) := by
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    funext u
    simp only [hP']
    rw [← hxv u]
    ring
  rw [hEq2] at hIBP
  have hX : (∫ u : ℝ, P u * v' u)
      = ∫ u : ℝ, Complex.exp (-b * (u:ℂ)^2) * ((deriv (Q776.tdiv h) u : ℝ) : ℂ) := rfl
  rw [hX] at hIBP
  rw [hIBP]
  field_simp

/-! ## The concrete tail chain -/

/-- The tail `1 - cutoff`. -/
noncomputable def tail0 (u : ℝ) : ℝ := 1 - cutoff u

noncomputable def tw1 : ℝ → ℝ := Q776.tdiv tail0
noncomputable def tw2 : ℝ → ℝ := deriv tw1
noncomputable def tw3 : ℝ → ℝ := Q776.tdiv tw2
noncomputable def tw4 : ℝ → ℝ := deriv tw3
noncomputable def tw5 : ℝ → ℝ := Q776.tdiv tw4
noncomputable def tw6 : ℝ → ℝ := deriv tw5

theorem tailFun_tail0 : TailFun (1/2) 0 1 tail0 := by
  refine ⟨contDiff_const.sub cutoff_smooth, by norm_num, ?_, ?_⟩
  · intro u hu
    simp [tail0, cutoff_one hu]
  · intro u hu
    simp [tail0, cutoff_zero hu.le]

theorem tailFun_tw1 : TailFun (1/2) 1 1 tw1 := tailFun_tail0.tdiv

theorem tailFun_tw2 : TailFun (1/4) 2 (-1) tw2 := by
  have := tailFun_tw1.deriv_tail (by norm_num)
  norm_num at this
  exact this

theorem tailFun_tw3 : TailFun (1/4) 3 (-1) tw3 := tailFun_tw2.tdiv

theorem tailFun_tw4 : TailFun (1/8) 4 3 tw4 := by
  have := tailFun_tw3.deriv_tail (by norm_num)
  norm_num at this
  exact this

theorem tailFun_tw5 : TailFun (1/8) 5 3 tw5 := tailFun_tw4.tdiv

theorem tailFun_tw6 : TailFun (1/16) 6 (-15) tw6 := by
  have := tailFun_tw5.deriv_tail (by norm_num)
  norm_num at this
  exact this

/-- The universal constant in the tail estimate. -/
noncomputable def tailConst : ℝ := ∫ u : ℝ, |tw6 u|

theorem tailConst_nonneg : 0 ≤ tailConst :=
  MeasureTheory.integral_nonneg fun _ => abs_nonneg _

theorem norm_integral_tw6_le {b : ℂ} (hb : 0 < b.re) :
    ‖∫ u : ℝ, Complex.exp (-b * (u:ℂ)^2) * (tw6 u : ℂ)‖ ≤ tailConst := by
  obtain ⟨M, hM0, hM⟩ := tailFun_tw6.bounded
  have hint : Integrable (fun u : ℝ => Complex.exp (-b * (u:ℂ)^2) * (tw6 u : ℂ)) :=
    integrable_gauss_mul_real hb tailFun_tw6.smooth.continuous hM
  have h6 : Integrable tw6 := tailFun_tw6.integrable (by norm_num)
  refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
  refine MeasureTheory.integral_mono hint.norm h6.abs fun u => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 : ‖Complex.exp (-b * (u:ℂ)^2)‖ ≤ 1 := norm_cgauss_le_one hb.le u
  nlinarith [abs_nonneg (tw6 u)]

/-- Three integrations by parts: the tail integral is `O(‖b‖^{-3})`. -/
theorem norm_integral_tail0_le {b : ℂ} (hb : 0 < b.re) :
    ‖∫ u : ℝ, Complex.exp (-b * (u:ℂ)^2) * (tail0 u : ℂ)‖ ≤ tailConst / (8 * ‖b‖^3) := by
  have hbne : b ≠ 0 := by intro h0; rw [h0] at hb; simp at hb
  have e1 := tail_ibp hb tailFun_tail0
  have e2 := tail_ibp hb tailFun_tw2
  have e3 := tail_ibp hb tailFun_tw4
  have hd1 : deriv (Q776.tdiv tail0) = tw2 := rfl
  have hd2 : deriv (Q776.tdiv tw2) = tw4 := rfl
  have hd3 : deriv (Q776.tdiv tw4) = tw6 := rfl
  rw [hd1] at e1
  rw [hd2] at e2
  rw [hd3] at e3
  rw [e1, e2, e3]
  rw [norm_mul, norm_mul, norm_mul]
  have hb0 : (0:ℝ) < ‖b‖ := norm_pos_iff.2 hbne
  have hnorm : ‖1/(2*b)‖ = 1/(2*‖b‖) := by
    rw [norm_div, norm_mul]
    simp
  rw [hnorm]
  have hkey := norm_integral_tw6_le hb
  have hpos : (0:ℝ) < 2 * ‖b‖ := by linarith
  have : 1/(2*‖b‖) * (1/(2*‖b‖) * (1/(2*‖b‖) *
      ‖∫ u : ℝ, Complex.exp (-b * (u:ℂ)^2) * (tw6 u : ℂ)‖))
      ≤ 1/(2*‖b‖) * (1/(2*‖b‖) * (1/(2*‖b‖) * tailConst)) := by
    have h1 : (0:ℝ) ≤ 1/(2*‖b‖) := by positivity
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hkey h1) h1) h1
  refine le_trans this (le_of_eq ?_)
  field_simp
  ring

/-! ## The Fresnel estimate -/

/-- The cutoff Fresnel integral. -/
noncomputable def fresnelI (b : ℂ) : ℂ := ∫ u : ℝ, Complex.exp (-b * (u:ℂ)^2) * (cutoff u : ℂ)

theorem fresnel_pos {b : ℂ} (hb : 0 < b.re) :
    ‖fresnelI b - ((π:ℂ)/b)^(1/2:ℂ)‖ ≤ tailConst / (8 * ‖b‖^3) := by
  obtain ⟨M, hM0, hM⟩ := tailFun_tail0.bounded
  have hP : Integrable (fun u : ℝ => Complex.exp (-b * (u:ℂ)^2)) := integrable_cexp_neg_mul_sq hb
  have hPt : Integrable (fun u : ℝ => Complex.exp (-b * (u:ℂ)^2) * (tail0 u : ℂ)) :=
    integrable_gauss_mul_real hb tailFun_tail0.smooth.continuous hM
  have hsplit : fresnelI b
      = (∫ u : ℝ, Complex.exp (-b * (u:ℂ)^2))
        - ∫ u : ℝ, Complex.exp (-b * (u:ℂ)^2) * (tail0 u : ℂ) := by
    change (∫ u : ℝ, Complex.exp (-b * (u:ℂ)^2) * (cutoff u : ℂ)) = _
    rw [← MeasureTheory.integral_sub hP hPt]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have hc : (cutoff u : ℂ) = 1 - (tail0 u : ℂ) := by
      simp [tail0]
    simp only [hc]
    ring
  rw [hsplit, integral_gaussian_complex hb]
  have hcancel : ((π:ℂ)/b)^(1/2:ℂ) - (∫ u : ℝ, Complex.exp (-b*(u:ℂ)^2) * (tail0 u:ℂ))
      - ((π:ℂ)/b)^(1/2:ℂ) = -(∫ u : ℝ, Complex.exp (-b*(u:ℂ)^2) * (tail0 u:ℂ)) := by ring
  rw [hcancel, norm_neg]
  exact norm_integral_tail0_le hb

theorem continuous_fresnelI : Continuous fresnelI := by
  rw [continuous_iff_continuousAt]
  intro b₀
  set C : ℝ := Real.exp (‖b₀‖ + 1) with hC
  have hC0 : 0 < C := Real.exp_pos _
  refine MeasureTheory.continuousAt_of_dominated
    (bound := fun u : ℝ => 2 * C * (1 + u^2)⁻¹) ?_ ?_
    (integrable_inv_one_add_sq.const_mul _) ?_
  · exact Filter.Eventually.of_forall fun b =>
      ((continuous_cgauss b).mul
        (Complex.continuous_ofReal.comp cutoff_continuous)).aestronglyMeasurable
  · have hnb : ∀ᶠ b : ℂ in nhds b₀, ‖b‖ ≤ ‖b₀‖ + 1 := by
      have : ∀ᶠ b : ℂ in nhds b₀, ‖b - b₀‖ < 1 := by
        have := Metric.ball_mem_nhds b₀ (by norm_num : (0:ℝ) < 1)
        filter_upwards [this] with b hb
        simpa [dist_eq_norm] using hb
      filter_upwards [this] with b hb
      have := norm_add_le (b - b₀) b₀
      simp only [sub_add_cancel] at this
      linarith
    filter_upwards [hnb] with b hb
    refine Filter.Eventually.of_forall fun u => ?_
    have hpos : (0:ℝ) < 1 + u^2 := by positivity
    by_cases hu : |u| ≤ 1
    · have h2 : (1:ℝ)/2 ≤ (1 + u^2)⁻¹ := by
        have : u^2 ≤ 1 := by nlinarith [sq_abs u, abs_nonneg u]
        rw [inv_eq_one_div]
        exact one_div_le_one_div_of_le hpos (by linarith)
      have hgauss : ‖Complex.exp (-b * (u:ℂ)^2)‖ ≤ C := by
        rw [norm_cexp_neg_mul_sq, hC]
        apply Real.exp_le_exp.2
        have h1 : |b.re| ≤ ‖b‖ := Complex.abs_re_le_norm b
        have h2' : u^2 ≤ 1 := by nlinarith [sq_abs u, abs_nonneg u]
        nlinarith [abs_nonneg b.re, neg_abs_le b.re, le_abs_self b.re, sq_nonneg u,
          norm_nonneg b]
      have hcut : ‖(cutoff u : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg u)]
        exact cutoff_le_one u
      calc ‖Complex.exp (-b * (u:ℂ)^2) * (cutoff u : ℂ)‖
          ≤ C * 1 := by
            rw [norm_mul]
            exact mul_le_mul hgauss hcut (norm_nonneg _) hC0.le
        _ ≤ 2 * C * (1 + u^2)⁻¹ := by nlinarith
    · push Not at hu
      have : cutoff u = 0 := cutoff_zero hu.le
      rw [this]
      simp only [Complex.ofReal_zero, mul_zero, norm_zero]
      positivity
  · exact Filter.Eventually.of_forall fun u => by fun_prop

/-- **Fresnel estimate for a smooth cutoff.**  Valid on the whole closed right half plane,
in particular on the imaginary axis. -/
theorem fresnel_cutoff {b : ℂ} (hb : 0 ≤ b.re) (hbne : b ≠ 0) :
    ‖fresnelI b - ((π:ℂ)/b)^(1/2:ℂ)‖ ≤ tailConst / (8 * ‖b‖^3) := by
  rcases lt_or_eq_of_le hb with hpos | hzero
  · exact fresnel_pos hpos
  · -- `b` is purely imaginary; approximate from the right half plane
    have hre : b.re = 0 := hzero.symm
    have him : b.im ≠ 0 := by
      intro h0
      exact hbne (Complex.ext hre h0)
    set bn : ℕ → ℂ := fun n => b + (((((n:ℝ)+1)⁻¹ : ℝ)) : ℂ) with hbn
    have hbnre : ∀ n, 0 < (bn n).re := by
      intro n
      simp only [hbn, Complex.add_re, Complex.ofReal_re, hre, zero_add]
      positivity
    have htend : Filter.Tendsto bn Filter.atTop (nhds b) := by
      have h2 : Filter.Tendsto (fun n : ℕ => (((n:ℝ)+1)⁻¹ : ℝ)) Filter.atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.congr (fun n => by rw [one_div])
      have h0 : Filter.Tendsto (fun n : ℕ => ((((n:ℝ)+1)⁻¹ : ℝ) : ℂ)) Filter.atTop (nhds 0) := by
        have hco : Filter.Tendsto (fun x : ℝ => (x : ℂ)) (nhds 0) (nhds ((0:ℝ) : ℂ)) :=
          Complex.continuous_ofReal.tendsto 0
        simpa [Function.comp_def] using hco.comp h2
      have := h0.const_add b
      simpa [hbn] using this
    have hslit : ((π:ℂ)/b) ∈ Complex.slitPlane := by
      right
      rw [Complex.div_im]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div]
      have hns : Complex.normSq b ≠ 0 := by
        simpa [Complex.normSq_eq_zero] using hbne
      have : -(π * b.im / Complex.normSq b) ≠ 0 := by
        apply neg_ne_zero.2
        apply div_ne_zero _ hns
        exact mul_ne_zero (ne_of_gt Real.pi_pos) him
      simpa using this
    have hcont : ContinuousAt (fun z : ℂ => ‖fresnelI z - ((π:ℂ)/z)^(1/2:ℂ)‖) b := by
      refine (continuous_fresnelI.continuousAt.sub ?_).norm
      exact (continuousAt_cpow_const hslit).comp (continuousAt_const.div continuousAt_id hbne)
    have hcont2 : ContinuousAt (fun z : ℂ => tailConst / (8 * ‖z‖^3)) b := by
      refine ContinuousAt.div continuousAt_const (by fun_prop) ?_
      have : (0:ℝ) < ‖b‖ := norm_pos_iff.2 hbne
      positivity
    exact le_of_tendsto_of_tendsto' (hcont.tendsto.comp htend) (hcont2.tendsto.comp htend)
      (fun n => fresnel_pos (hbnre n))

end Q776
