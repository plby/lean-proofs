import Wikipedia.GreenTao.Sieve.SmoothCutoffFourier
import Wikipedia.GreenTao.Sieve.ZetaNearOne
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Fourier parameters for the zeta comparison

`SmoothCutoffFourier` fixes Mathlib's analyst normalization.  Its divisor
phase is

`exp (-x + 2 π i t x)`, where `x = log d / log R`.

Thus the exact complex shift occurring in the Euler and zeta factors is

`(1 - 2 π i t) / log R`.

This file records that conversion, its positivity and elementary norm
bounds, and the resulting access to the completed zeta estimates.  Keeping
this bridge explicit prevents a hidden `2π` or sign error when the
multivariate Fourier integral is assembled.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter
open scoped BigOperators Topology

/-- The exact zeta shift belonging to Mathlib's Fourier parameter `t`. -/
noncomputable def cutoffZetaShift
    (R : ℕ) (t : ℝ) : ℂ :=
  (((Real.log (R : ℝ))⁻¹ : ℝ) : ℂ) *
    ((1 : ℂ) -
      ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

theorem cutoffZetaShift_re
    (R : ℕ) (t : ℝ) :
    (cutoffZetaShift R t).re =
      1 / Real.log R := by
  change
    (Complex.ofReal ((Real.log (R : ℝ))⁻¹) *
      ((1 : ℂ) -
        Complex.ofReal (2 * Real.pi * t) *
          Complex.I)).re =
      1 / Real.log R
  simp only [Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.sub_re, Complex.one_re,
    Complex.I_re, Complex.I_im, zero_mul, mul_zero,
    sub_zero]
  rw [one_div]
  simp

theorem cutoffZetaShift_re_pos
    {R : ℕ} (hR : 1 < R) (t : ℝ) :
    0 < (cutoffZetaShift R t).re := by
  rw [cutoffZetaShift_re R]
  exact one_div_pos.mpr
    (Real.log_pos (by exact_mod_cast hR))

theorem cutoffZetaShift_ne_zero
    {R : ℕ} (hR : 1 < R) (t : ℝ) :
    cutoffZetaShift R t ≠ 0 := by
  intro hzero
  have hre := cutoffZetaShift_re_pos hR t
  rw [hzero] at hre
  norm_num at hre

theorem cutoffZetaShift_add_ne_zero
    {R : ℕ} (hR : 1 < R) (t u : ℝ) :
    cutoffZetaShift R t +
        cutoffZetaShift R u ≠ 0 := by
  intro hzero
  have hre :
      0 <
        (cutoffZetaShift R t +
          cutoffZetaShift R u).re := by
    rw [Complex.add_re]
    exact add_pos
      (cutoffZetaShift_re_pos hR t)
      (cutoffZetaShift_re_pos hR u)
  rw [hzero] at hre
  norm_num at hre

/-- Elementary norm bound for the exact Fourier shift. -/
theorem norm_cutoffZetaShift_le
    {R : ℕ} (hR : 1 < R) (t : ℝ) :
    ‖cutoffZetaShift R t‖ ≤
      (1 + |2 * Real.pi * t|) /
        Real.log R := by
  have hlog :
      0 < Real.log (R : ℝ) :=
    Real.log_pos (by exact_mod_cast hR)
  calc
    ‖cutoffZetaShift R t‖ =
        (Real.log (R : ℝ))⁻¹ *
          ‖(1 : ℂ) -
            ((2 * Real.pi * t : ℝ) : ℂ) *
              Complex.I‖ := by
      rw [cutoffZetaShift, norm_mul,
        Complex.norm_real,
        Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hlog)]
    _ ≤
        (Real.log (R : ℝ))⁻¹ *
          (1 + |2 * Real.pi * t|) := by
      apply mul_le_mul_of_nonneg_left
      · calc
          ‖(1 : ℂ) -
              ((2 * Real.pi * t : ℝ) : ℂ) *
                Complex.I‖ ≤
              ‖(1 : ℂ)‖ +
                ‖((2 * Real.pi * t : ℝ) : ℂ) *
                  Complex.I‖ :=
            norm_sub_le _ _
          _ = 1 + |2 * Real.pi * t| := by
            rw [norm_mul, Complex.norm_real,
              Real.norm_eq_abs,
              Complex.norm_I, mul_one, norm_one]
      · exact (inv_nonneg.mpr hlog.le)
    _ = (1 + |2 * Real.pi * t|) /
          Real.log R := by
      rw [div_eq_mul_inv]
      ring

/-- Uniform shift bound on a truncated Fourier interval. -/
theorem norm_cutoffZetaShift_le_of_abs_le
    {R : ℕ} (hR : 1 < R)
    {T t : ℝ} (ht : |t| ≤ T) :
    ‖cutoffZetaShift R t‖ ≤
      (1 + 2 * Real.pi * T) /
        Real.log R := by
  have hlog :
      0 ≤ Real.log (R : ℝ) :=
    (Real.log_pos (by exact_mod_cast hR)).le
  have hcoef :
      |2 * Real.pi * t| ≤
        2 * Real.pi * T := by
    calc
      |2 * Real.pi * t| =
          (2 * Real.pi) * |t| := by
        rw [abs_mul, abs_of_nonneg
          (mul_nonneg (by norm_num) Real.pi_pos.le)]
      _ ≤ (2 * Real.pi) * T :=
        mul_le_mul_of_nonneg_left ht
          (mul_nonneg (by norm_num) Real.pi_pos.le)
  have hnum :
      1 + |2 * Real.pi * t| ≤
        1 + 2 * Real.pi * T := by
    linarith
  exact (norm_cutoffZetaShift_le hR t).trans
    (div_le_div_of_nonneg_right
      hnum hlog)

/-- The divisor phase is exactly a negative complex power with the shift
above. -/
theorem divisorMultiplicativePhase_eq_cpow
    {R d : ℕ} (hR : 1 < R) (hd : 0 < d)
    (t : ℝ) :
    SmoothSieveCutoff.divisorMultiplicativePhase R d t =
      (d : ℂ) ^ (-cutoffZetaShift R t) := by
  have hd0 : (d : ℂ) ≠ 0 := by
    exact_mod_cast hd.ne'
  have hlog :
      Real.log (R : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hR)).ne'
  rw [SmoothSieveCutoff.divisorMultiplicativePhase,
    SmoothSieveCutoff.cutoffMultiplicativePhase,
    Complex.cpow_def_of_ne_zero hd0,
    ← Complex.natCast_log]
  congr 1
  rw [cutoffZetaShift]
  push_cast
  field_simp [hlog]
  ring

/-- Every shifted zeta argument lies in the classical half-plane of
absolute convergence. -/
theorem one_lt_one_add_cutoffZetaShift_re
    {R : ℕ} (hR : 1 < R) (t : ℝ) :
    1 < (1 + cutoffZetaShift R t).re := by
  rw [Complex.add_re, Complex.one_re]
  exact lt_add_of_pos_right 1
    (cutoffZetaShift_re_pos hR t)

/-- Zeta is nonzero at every Fourier shift, using its absolutely convergent
half-plane rather than a separate zero-free-region argument. -/
theorem riemannZeta_one_add_cutoffZetaShift_ne_zero
    {R : ℕ} (hR : 1 < R) (t : ℝ) :
    riemannZeta (1 + cutoffZetaShift R t) ≠ 0 :=
  riemannZeta_ne_zero_of_one_lt_re
    (one_lt_one_add_cutoffZetaShift_re hR t)

/-! ## Finite Fourier systems -/

/-- The completed zeta factor for a finite system of paired Fourier
parameters. -/
noncomputable def cutoffZetaSystemFactor
    {κ : Type*} [Fintype κ]
    (R : ℕ) (t u : κ → ℝ) : ℂ :=
  normalizedZetaSystemFactor
    (fun i => cutoffZetaShift R (t i))
    (fun i => cutoffZetaShift R (u i))

/-- Exact raw-zeta product for all paired Fourier parameters.  Positivity of
the real parts discharges every denominator nonvanishing condition. -/
theorem cutoffZetaSystemFactor_eq_prod
    {κ : Type*} [Fintype κ]
    {R : ℕ} (hR : 1 < R)
    (t u : κ → ℝ) :
    cutoffZetaSystemFactor R t u =
      ∏ i,
        (((cutoffZetaShift R (t i) +
              cutoffZetaShift R (u i)) /
            (cutoffZetaShift R (t i) *
              cutoffZetaShift R (u i))) *
          (riemannZeta
                (1 + cutoffZetaShift R (t i) +
                  cutoffZetaShift R (u i)) /
            (riemannZeta
                  (1 + cutoffZetaShift R (t i)) *
              riemannZeta
                  (1 + cutoffZetaShift R (u i))))) := by
  rw [cutoffZetaSystemFactor]
  exact normalizedZetaSystemFactor_eq_prod
    (fun i => cutoffZetaShift_ne_zero hR (t i))
    (fun i => cutoffZetaShift_ne_zero hR (u i))
    (fun i => cutoffZetaShift_add_ne_zero hR (t i) (u i))
    (fun i =>
      riemannZeta_one_add_cutoffZetaShift_ne_zero
        hR (t i))
    (fun i =>
      riemannZeta_one_add_cutoffZetaShift_ne_zero
        hR (u i))

/-- Uniform finite-system zeta comparison, stated directly for the exact
Fourier shifts. -/
theorem exists_norm_cutoffZetaSystemFactor_sub_one_lt
    {κ : Type*} [Fintype κ]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (R : ℕ) (t u : κ → ℝ),
        (∀ i, ‖cutoffZetaShift R (t i)‖ < δ) →
        (∀ i, ‖cutoffZetaShift R (u i)‖ < δ) →
        ‖cutoffZetaSystemFactor R t u - 1‖ < ε := by
  obtain ⟨δ, hδ, hclose⟩ :=
    exists_norm_normalizedZetaSystemFactor_sub_one_lt
      (κ := κ) hε
  refine ⟨δ, hδ, fun R t u ht hu => ?_⟩
  rw [cutoffZetaSystemFactor]
  apply hclose
  · exact (pi_norm_lt_iff hδ).2 ht
  · exact (pi_norm_lt_iff hδ).2 hu

/-- Ready-to-use zeta comparison on a common truncated Fourier box.  All
analytic smallness is reduced to the displayed scalar inequality. -/
theorem exists_cutoffZetaSystemFactor_close_on_box
    {κ : Type*} [Fintype κ]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {R : ℕ}, 1 < R →
      ∀ {T : ℝ} (t u : κ → ℝ),
        (1 + 2 * Real.pi * T) /
            Real.log R < δ →
        (∀ i, |t i| ≤ T) →
        (∀ i, |u i| ≤ T) →
        ‖cutoffZetaSystemFactor R t u - 1‖ < ε := by
  obtain ⟨δ, hδ, hclose⟩ :=
    exists_norm_cutoffZetaSystemFactor_sub_one_lt
      (κ := κ) hε
  refine ⟨δ, hδ, ?_⟩
  intro R hR T t u hsmall ht hu
  exact hclose R t u
    (fun i =>
      (norm_cutoffZetaShift_le_of_abs_le
        hR (ht i)).trans_lt hsmall)
    (fun i =>
      (norm_cutoffZetaShift_le_of_abs_le
        hR (hu i)).trans_lt hsmall)

/-! ## The standard growing truncation box -/

/-- The scalar radius controlling the box `|t| ≤ sqrt (log R)` tends to
zero. -/
theorem tendsto_fourierZetaBoxRadius_real :
    Tendsto
      (fun x : ℝ =>
        (1 + 2 * Real.pi * Real.sqrt x) / x)
      atTop (𝓝 0) := by
  have hinv :
      Tendsto (fun x : ℝ => x⁻¹)
        atTop (𝓝 0) :=
    tendsto_inv_atTop_zero
  have hsqrtInv :
      Tendsto (fun x : ℝ => (Real.sqrt x)⁻¹)
        atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      Real.tendsto_sqrt_atTop
  have hsum :
      Tendsto
        (fun x : ℝ =>
          x⁻¹ +
            (2 * Real.pi) *
              (Real.sqrt x)⁻¹)
        atTop (𝓝 0) := by
    simpa using hinv.add
      ((tendsto_const_nhds :
          Tendsto (fun _ : ℝ => 2 * Real.pi)
            atTop (𝓝 (2 * Real.pi))).mul
        hsqrtInv)
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hsqrt :
      0 < Real.sqrt x :=
    Real.sqrt_pos.2 hx
  have hsquare :
      (Real.sqrt x) ^ 2 = x :=
    Real.sq_sqrt hx.le
  have hsqrtDiv :
      Real.sqrt x / x =
        (Real.sqrt x)⁻¹ := by
    calc
      Real.sqrt x / x =
          Real.sqrt x / (Real.sqrt x) ^ 2 := by
        rw [hsquare]
      _ = (Real.sqrt x)⁻¹ := by
        field_simp [hsqrt.ne']
  rw [add_div, one_div, mul_div_assoc, hsqrtDiv]

theorem tendsto_fourierZetaBoxRadius_nat :
    Tendsto
      (fun R : ℕ =>
        (1 + 2 * Real.pi *
            Real.sqrt (Real.log R)) /
          Real.log R)
      atTop (𝓝 0) := by
  exact tendsto_fourierZetaBoxRadius_real.comp
    (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop)

/-- On the conventional truncation region
`|t_i|, |u_i| ≤ sqrt (log R)`, the completed finite zeta factor is uniformly
close to one for all sufficiently large `R`. -/
theorem exists_threshold_cutoffZetaSystemFactor_close
    {κ : Type*} [Fintype κ]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ : ℕ,
      ∀ R, R₀ ≤ R →
      ∀ (t u : κ → ℝ),
        (∀ i, |t i| ≤ Real.sqrt (Real.log R)) →
        (∀ i, |u i| ≤ Real.sqrt (Real.log R)) →
        ‖cutoffZetaSystemFactor R t u - 1‖ < ε := by
  obtain ⟨δ, hδ, hbox⟩ :=
    exists_cutoffZetaSystemFactor_close_on_box
      (κ := κ) hε
  have hlarge :
      ∀ᶠ R : ℕ in atTop, 1 < R :=
    eventually_gt_atTop 1
  have hdist :
      ∀ᶠ R : ℕ in atTop,
        dist
          ((1 + 2 * Real.pi *
              Real.sqrt (Real.log R)) /
            Real.log R)
          0 < δ :=
    Metric.tendsto_nhds.mp
      tendsto_fourierZetaBoxRadius_nat δ hδ
  have hsmall :
      ∀ᶠ R : ℕ in atTop,
        (1 + 2 * Real.pi *
            Real.sqrt (Real.log R)) /
          Real.log R < δ := by
    filter_upwards [hdist, hlarge] with R hdistR hR
    have hlog :
        0 < Real.log (R : ℝ) :=
      Real.log_pos (by exact_mod_cast hR)
    have hnum :
        0 ≤
          1 + 2 * Real.pi *
            Real.sqrt (Real.log R) := by
      positivity
    have hfrac :
        0 ≤
          (1 + 2 * Real.pi *
              Real.sqrt (Real.log R)) /
            Real.log R :=
      div_nonneg hnum hlog.le
    have habs :
        |(1 + 2 * Real.pi *
              Real.sqrt (Real.log R)) /
            Real.log R| < δ := by
      simpa only [Real.dist_eq, sub_zero] using hdistR
    rw [abs_of_nonneg hfrac] at habs
    exact habs
  rw [eventually_atTop] at hsmall hlarge
  obtain ⟨R₁, hR₁⟩ := hsmall
  obtain ⟨R₂, hR₂⟩ := hlarge
  refine ⟨max R₁ R₂, fun R hR t u ht hu => ?_⟩
  exact hbox (hR₂ R ((le_max_right R₁ R₂).trans hR))
    t u
    (hR₁ R ((le_max_left R₁ R₂).trans hR))
    ht hu

end Wikipedia.SzemeredisTheorem
