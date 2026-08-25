import ErdosProblems.Erdos67.MRLemma14
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.Inversion

/-!
# Compact logarithmic smoothing for a finite Halasz polynomial

This file gives a genuinely finite Mellin--Fourier smoothing device.  A
normalised smooth bump of radius `delta` is convolved with the indicator of
the log interval `[A + delta, B - delta]`.  The resulting window is smooth,
compactly supported, and exactly one on the smaller interval
`[A + 2 * delta, B - 2 * delta]`.  Its Fourier transform is a Schwartz
function, so in particular it is an honest integrable kernel.

The final identity applies Fourier inversion term by term to a finite
logarithmic Dirichlet polynomial.  There is no complete `LSeries`, no tail,
and no hidden convergence assertion.
-/

open scoped BigOperators Convolution FourierTransform ContDiff SchwartzMap
open Complex Finset MeasureTheory Set

namespace Erdos67.MRFiniteHalaszSmoothing

noncomputable section

/-- The complex-valued indicator of a closed real interval. -/
def logIntervalIndicator (A B x : ℝ) : ℂ :=
  Set.Icc A B |>.indicator (fun _ ↦ (1 : ℂ)) x

@[simp] theorem logIntervalIndicator_eq_one
    {A B x : ℝ} (hx : x ∈ Set.Icc A B) :
    logIntervalIndicator A B x = 1 := by
  simp [logIntervalIndicator, hx]

@[simp] theorem logIntervalIndicator_eq_zero
    {A B x : ℝ} (hx : x ∉ Set.Icc A B) :
    logIntervalIndicator A B x = 0 := by
  simp [logIntervalIndicator, hx]

theorem integrable_logIntervalIndicator (A B : ℝ) :
    Integrable (logIntervalIndicator A B) := by
  unfold logIntervalIndicator
  exact (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc

theorem locallyIntegrable_logIntervalIndicator (A B : ℝ) :
    LocallyIntegrable (logIntervalIndicator A B) :=
  (integrable_logIntervalIndicator A B).locallyIntegrable

theorem hasCompactSupport_logIntervalIndicator (A B : ℝ) :
    HasCompactSupport (logIntervalIndicator A B) := by
  apply (isCompact_Icc : IsCompact (Set.Icc A B)).of_isClosed_subset
    (isClosed_tsupport (logIntervalIndicator A B))
  apply closure_minimal
  · intro x hx
    by_contra hnot
    exact hx (logIntervalIndicator_eq_zero hnot)
  · exact isClosed_Icc

/-- A canonical smooth bump centred at zero, with inner radius `delta / 2`
and outer radius `delta`. -/
def logSmoothingBump (delta : ℝ) (hdelta : 0 < delta) :
    ContDiffBump (0 : ℝ) where
  rIn := delta / 2
  rOut := delta
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

@[simp] theorem logSmoothingBump_rOut
    (delta : ℝ) (hdelta : 0 < delta) :
    (logSmoothingBump delta hdelta).rOut = delta := rfl

/-- The compact logarithmic window.  It is a normalised bump of radius
`delta` convolved with the interval `[A + delta, B - delta]`. -/
def logTrapezoidWindow
    (delta A B : ℝ) (hdelta : 0 < delta) : ℝ → ℂ :=
  (logSmoothingBump delta hdelta).normed volume ⋆[
      ContinuousLinearMap.lsmul ℝ ℝ]
    logIntervalIndicator (A + delta) (B - delta)

theorem contDiff_logTrapezoidWindow
    (delta A B : ℝ) (hdelta : 0 < delta) :
    ContDiff ℝ ∞ (logTrapezoidWindow delta A B hdelta) := by
  unfold logTrapezoidWindow
  exact (logSmoothingBump delta hdelta).hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ)
    (ContDiffBump.contDiff_normed (logSmoothingBump delta hdelta))
    (locallyIntegrable_logIntervalIndicator (A + delta) (B - delta))

theorem continuous_logTrapezoidWindow
    (delta A B : ℝ) (hdelta : 0 < delta) :
    Continuous (logTrapezoidWindow delta A B hdelta) :=
  (contDiff_logTrapezoidWindow delta A B hdelta).continuous

theorem hasCompactSupport_logTrapezoidWindow
    (delta A B : ℝ) (hdelta : 0 < delta) :
    HasCompactSupport (logTrapezoidWindow delta A B hdelta) := by
  unfold logTrapezoidWindow
  exact (logSmoothingBump delta hdelta).hasCompactSupport_normed.convolution
    (ContinuousLinearMap.lsmul ℝ ℝ)
    (hasCompactSupport_logIntervalIndicator (A + delta) (B - delta))

theorem integrable_logTrapezoidWindow
    (delta A B : ℝ) (hdelta : 0 < delta) :
    Integrable (logTrapezoidWindow delta A B hdelta) := by
  unfold logTrapezoidWindow
  exact (logSmoothingBump delta hdelta).integrable_normed.integrable_convolution
    (ContinuousLinearMap.lsmul ℝ ℝ)
    (integrable_logIntervalIndicator (A + delta) (B - delta))

/-- The compact log window has no leakage outside `[A,B]`.  This is the
key finite-support feature: coefficients of a convolution beyond the
enlarged dyadic range never enter the smoothing identity. -/
theorem support_logTrapezoidWindow_subset
    (delta A B : ℝ) (hdelta : 0 < delta) :
    Function.support (logTrapezoidWindow delta A B hdelta) ⊆ Set.Icc A B := by
  intro v hv
  have hv' := MeasureTheory.support_convolution_subset
    (L := ContinuousLinearMap.lsmul ℝ ℝ) hv
  rcases hv' with ⟨x, hx, y, hy, rfl⟩
  have hxball : x ∈ Metric.ball (0 : ℝ) delta := by
    rw [(logSmoothingBump delta hdelta).support_normed_eq (μ := volume)] at hx
    simpa [logSmoothingBump_rOut] using hx
  have hxabs : |x| < delta := by
    simpa [Real.dist_eq] using hxball
  have hyI : y ∈ Set.Icc (A + delta) (B - delta) := by
    by_contra hnot
    exact hy (logIntervalIndicator_eq_zero hnot)
  rcases abs_lt.mp hxabs with ⟨hxlo, hxhi⟩
  exact ⟨by linarith [hyI.1], by linarith [hyI.2]⟩

@[simp] theorem logTrapezoidWindow_eq_zero_of_not_mem
    (delta A B : ℝ) (hdelta : 0 < delta) {v : ℝ}
    (hv : v ∉ Set.Icc A B) :
    logTrapezoidWindow delta A B hdelta v = 0 := by
  by_contra hne
  exact hv (support_logTrapezoidWindow_subset delta A B hdelta hne)

/-- The compact smoothing window is pointwise bounded by one. -/
theorem norm_logTrapezoidWindow_le_one
    (delta A B : ℝ) (hdelta : 0 < delta) (v : ℝ) :
    ‖logTrapezoidWindow delta A B hdelta v‖ ≤ 1 := by
  unfold logTrapezoidWindow MeasureTheory.convolution
  calc
    ‖∫ t : ℝ,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          ((logSmoothingBump delta hdelta).normed volume t)
          (logIntervalIndicator (A + delta) (B - delta) (v - t))‖ ≤
        ∫ t : ℝ, (logSmoothingBump delta hdelta).normed volume t := by
      apply norm_integral_le_of_norm_le
        (logSmoothingBump delta hdelta).integrable_normed
      filter_upwards with t
      rw [ContinuousLinearMap.lsmul_apply, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg ((logSmoothingBump delta hdelta).nonneg_normed t)]
      apply mul_le_of_le_one_right
      · exact (logSmoothingBump delta hdelta).nonneg_normed t
      · unfold logIntervalIndicator
        by_cases hmem : v - t ∈ Set.Icc (A + delta) (B - delta) <;>
          simp [hmem]
    _ = 1 := (logSmoothingBump delta hdelta).integral_normed

/-- The normalised bump sees a constant interval indicator at every point
whose distance from both ends is at least its outer radius.  Consequently
the smoothing window is exactly one on the full interior interval. -/
theorem logTrapezoidWindow_eq_one_of_mem_interior
    (delta A B : ℝ) (hdelta : 0 < delta) {v : ℝ}
    (hv : v ∈ Set.Icc (A + 2 * delta) (B - 2 * delta)) :
    logTrapezoidWindow delta A B hdelta v = 1 := by
  unfold logTrapezoidWindow
  rw [ContDiffBump.normed_convolution_eq_right]
  · exact logIntervalIndicator_eq_one ⟨by linarith [hv.1], by linarith [hv.2]⟩
  · intro x hx
    have hxabs : |x - v| < delta := by
      simpa [logSmoothingBump_rOut, Real.dist_eq, abs_sub_comm] using hx
    rcases abs_lt.mp hxabs with ⟨hxlo, hxhi⟩
    have hxI : x ∈ Set.Icc (A + delta) (B - delta) :=
      ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have hvI : v ∈ Set.Icc (A + delta) (B - delta) :=
      ⟨by linarith [hv.1], by linarith [hv.2]⟩
    rw [logIntervalIndicator_eq_one hxI, logIntervalIndicator_eq_one hvI]

/-- The window, packaged as a Schwartz function. -/
def logTrapezoidSchwartz
    (delta A B : ℝ) (hdelta : 0 < delta) : 𝓢(ℝ, ℂ) :=
  (hasCompactSupport_logTrapezoidWindow delta A B hdelta).toSchwartzMap
    (contDiff_logTrapezoidWindow delta A B hdelta)

@[simp] theorem logTrapezoidSchwartz_apply
    (delta A B : ℝ) (hdelta : 0 < delta) (x : ℝ) :
    logTrapezoidSchwartz delta A B hdelta x =
      logTrapezoidWindow delta A B hdelta x := rfl

/-- The rapidly decaying Fourier kernel associated to the compact log
window.  Mathlib's Fourier convention is `exp (-2*pi*i*x*xi)`. -/
def logTrapezoidKernel
    (delta A B : ℝ) (hdelta : 0 < delta) : ℝ → ℂ :=
  fun xi ↦ (𝓕 (logTrapezoidSchwartz delta A B hdelta)) xi

theorem integrable_logTrapezoidKernel
    (delta A B : ℝ) (hdelta : 0 < delta) :
    Integrable (logTrapezoidKernel delta A B hdelta) := by
  exact (𝓕 (logTrapezoidSchwartz delta A B hdelta)).integrable (μ := volume)

/-- The exact `L¹` mass of the explicit smoothing kernel. -/
def logTrapezoidKernelMass
    (delta A B : ℝ) (hdelta : 0 < delta) : ℝ :=
  ∫ xi : ℝ, ‖logTrapezoidKernel delta A B hdelta xi‖

theorem logTrapezoidKernelMass_nonneg
    (delta A B : ℝ) (hdelta : 0 < delta) :
    0 ≤ logTrapezoidKernelMass delta A B hdelta := by
  unfold logTrapezoidKernelMass
  exact integral_nonneg fun _ ↦ norm_nonneg _

theorem logTrapezoidKernelMass_lt_top
    (delta A B : ℝ) (hdelta : 0 < delta) :
    HasFiniteIntegral
      (fun xi ↦ ‖logTrapezoidKernel delta A B hdelta xi‖) :=
  (integrable_logTrapezoidKernel delta A B hdelta).norm.hasFiniteIntegral

/-- Fourier inversion for the concrete log window, in the exact convention
used by `logTrapezoidKernel`. -/
theorem integral_exp_mul_logTrapezoidKernel
    (delta A B : ℝ) (hdelta : 0 < delta) (v : ℝ) :
    (∫ xi : ℝ,
        Complex.exp (((2 * Real.pi * xi * v : ℝ) : ℂ) * Complex.I) *
          logTrapezoidKernel delta A B hdelta xi) =
      logTrapezoidWindow delta A B hdelta v := by
  let S : 𝓢(ℝ, ℂ) := logTrapezoidSchwartz delta A B hdelta
  have hInv : (𝓕⁻ (𝓕 S)) v = S v := by
    rw [FourierTransform.fourierInv_fourier_eq]
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq'] at hInv
  simp only [smul_eq_mul, RCLike.inner_apply, conj_trivial] at hInv
  change (∫ xi : ℝ,
      Complex.exp (((2 * Real.pi * xi * v : ℝ) : ℂ) * Complex.I) *
        (FourierTransform.fourier S) xi) = S v
  rw [show (fun xi : ℝ ↦
      Complex.exp (((2 * Real.pi * xi * v : ℝ) : ℂ) * Complex.I) *
        (FourierTransform.fourier S) xi) =
      fun xi : ℝ ↦
        Complex.exp (((2 * Real.pi * (v * xi) : ℝ) : ℂ) * Complex.I) *
          (FourierTransform.fourier S) xi by
    funext xi
    congr 2
    push_cast
    ring]
  exact hInv

/-! ## Exponentially tilted compact windows

The tilt below is the finite Mellin correction which changes a polynomial
on the line `Re s = 1 + rho` back to the line `Re s = 1`.  Compact support
is essential: multiplication by the exponential does not introduce any
new coefficients. -/

/-- The compact logarithmic window after the real exponential Mellin tilt. -/
def tiltedLogTrapezoidWindow
    (rho delta A B : ℝ) (hdelta : 0 < delta) : ℝ → ℂ :=
  fun v ↦ (Real.exp (rho * v) : ℂ) *
    logTrapezoidWindow delta A B hdelta v

theorem contDiff_tiltedLogTrapezoidWindow
    (rho delta A B : ℝ) (hdelta : 0 < delta) :
    ContDiff ℝ ∞ (tiltedLogTrapezoidWindow rho delta A B hdelta) := by
  unfold tiltedLogTrapezoidWindow
  have hexp : ContDiff ℝ ∞ (fun v : ℝ ↦ Real.exp (rho * v)) := by
    fun_prop
  have hexpC : ContDiff ℝ ∞
      (Complex.ofRealCLM ∘ fun v : ℝ ↦ Real.exp (rho * v)) :=
    Complex.ofRealCLM.contDiff.comp hexp
  simpa only [Function.comp_apply, Complex.ofRealCLM_apply] using
    hexpC.mul (contDiff_logTrapezoidWindow delta A B hdelta)

theorem continuous_tiltedLogTrapezoidWindow
    (rho delta A B : ℝ) (hdelta : 0 < delta) :
    Continuous (tiltedLogTrapezoidWindow rho delta A B hdelta) :=
  (contDiff_tiltedLogTrapezoidWindow rho delta A B hdelta).continuous

theorem hasCompactSupport_tiltedLogTrapezoidWindow
    (rho delta A B : ℝ) (hdelta : 0 < delta) :
    HasCompactSupport (tiltedLogTrapezoidWindow rho delta A B hdelta) := by
  unfold tiltedLogTrapezoidWindow
  exact (hasCompactSupport_logTrapezoidWindow delta A B hdelta).mul_left

theorem integrable_tiltedLogTrapezoidWindow
    (rho delta A B : ℝ) (hdelta : 0 < delta) :
    Integrable (tiltedLogTrapezoidWindow rho delta A B hdelta) :=
  (continuous_tiltedLogTrapezoidWindow rho delta A B hdelta).integrable_of_hasCompactSupport
    (hasCompactSupport_tiltedLogTrapezoidWindow rho delta A B hdelta)

/-- Tilting preserves the exact compact support `[A,B]`. -/
theorem support_tiltedLogTrapezoidWindow_subset
    (rho delta A B : ℝ) (hdelta : 0 < delta) :
    Function.support (tiltedLogTrapezoidWindow rho delta A B hdelta) ⊆ Set.Icc A B := by
  intro v hv
  apply support_logTrapezoidWindow_subset delta A B hdelta
  intro hzero
  exact hv (by simp [tiltedLogTrapezoidWindow, hzero])

@[simp] theorem tiltedLogTrapezoidWindow_eq_zero_of_not_mem
    (rho delta A B : ℝ) (hdelta : 0 < delta) {v : ℝ}
    (hv : v ∉ Set.Icc A B) :
    tiltedLogTrapezoidWindow rho delta A B hdelta v = 0 := by
  by_contra hne
  exact hv (support_tiltedLogTrapezoidWindow_subset rho delta A B hdelta hne)

/-- On the interior plateau the tilted window is exactly the exponential
factor required to undo a shift of the real part. -/
theorem tiltedLogTrapezoidWindow_eq_exp_of_mem_interior
    (rho delta A B : ℝ) (hdelta : 0 < delta) {v : ℝ}
    (hv : v ∈ Set.Icc (A + 2 * delta) (B - 2 * delta)) :
    tiltedLogTrapezoidWindow rho delta A B hdelta v =
      (Real.exp (rho * v) : ℂ) := by
  simp [tiltedLogTrapezoidWindow,
    logTrapezoidWindow_eq_one_of_mem_interior delta A B hdelta hv]

/-- The tilted compact window, packaged as a Schwartz function. -/
def tiltedLogTrapezoidSchwartz
    (rho delta A B : ℝ) (hdelta : 0 < delta) : 𝓢(ℝ, ℂ) :=
  (hasCompactSupport_tiltedLogTrapezoidWindow rho delta A B hdelta).toSchwartzMap
    (contDiff_tiltedLogTrapezoidWindow rho delta A B hdelta)

@[simp] theorem tiltedLogTrapezoidSchwartz_apply
    (rho delta A B : ℝ) (hdelta : 0 < delta) (v : ℝ) :
    tiltedLogTrapezoidSchwartz rho delta A B hdelta v =
      tiltedLogTrapezoidWindow rho delta A B hdelta v := rfl

/-- Fourier transform of the exponentially tilted compact window. -/
def tiltedLogTrapezoidKernel
    (rho delta A B : ℝ) (hdelta : 0 < delta) : ℝ → ℂ :=
  fun xi ↦ (𝓕 (tiltedLogTrapezoidSchwartz rho delta A B hdelta)) xi

theorem integrable_tiltedLogTrapezoidKernel
    (rho delta A B : ℝ) (hdelta : 0 < delta) :
    Integrable (tiltedLogTrapezoidKernel rho delta A B hdelta) := by
  exact (𝓕 (tiltedLogTrapezoidSchwartz rho delta A B hdelta)).integrable
    (μ := volume)

/-- Exact `L¹` mass of the tilted Fourier kernel. -/
def tiltedLogTrapezoidKernelMass
    (rho delta A B : ℝ) (hdelta : 0 < delta) : ℝ :=
  ∫ xi : ℝ, ‖tiltedLogTrapezoidKernel rho delta A B hdelta xi‖

theorem tiltedLogTrapezoidKernelMass_nonneg
    (rho delta A B : ℝ) (hdelta : 0 < delta) :
    0 ≤ tiltedLogTrapezoidKernelMass rho delta A B hdelta := by
  exact integral_nonneg fun _ ↦ norm_nonneg _

theorem tiltedLogTrapezoidKernelMass_lt_top
    (rho delta A B : ℝ) (hdelta : 0 < delta) :
    HasFiniteIntegral
      (fun xi ↦ ‖tiltedLogTrapezoidKernel rho delta A B hdelta xi‖) :=
  (integrable_tiltedLogTrapezoidKernel rho delta A B hdelta).norm.hasFiniteIntegral

/-- Any frequency-uniform bound may be pulled through the tilted smoothing
integral at the exact cost of the kernel's `L¹` mass. -/
theorem integral_norm_mul_tiltedLogTrapezoidKernel_le_mass_of_uniform
    (g : ℝ → ℂ) (hg : AEStronglyMeasurable g)
    (rho delta A B : ℝ) (hdelta : 0 < delta)
    {M : ℝ} (_hM : 0 ≤ M) (hgM : ∀ xi, ‖g xi‖ ≤ M) :
    (∫ xi : ℝ, ‖g xi‖ *
        ‖tiltedLogTrapezoidKernel rho delta A B hdelta xi‖) ≤
      M * tiltedLogTrapezoidKernelMass rho delta A B hdelta := by
  let q : ℝ → ℝ := fun xi ↦ ‖g xi‖ *
    ‖tiltedLogTrapezoidKernel rho delta A B hdelta xi‖
  let r : ℝ → ℝ := fun xi ↦ M *
    ‖tiltedLogTrapezoidKernel rho delta A B hdelta xi‖
  have hr : Integrable r :=
    (integrable_tiltedLogTrapezoidKernel rho delta A B hdelta).norm.const_mul M
  have hq : Integrable q := by
    refine hr.mono' ?_ ?_
    · exact hg.norm.mul
        (integrable_tiltedLogTrapezoidKernel rho delta A B hdelta).norm.aestronglyMeasurable
    · filter_upwards with xi
      change ‖q xi‖ ≤ r xi
      dsimp only [q, r]
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      exact mul_le_mul_of_nonneg_right (hgM xi) (norm_nonneg _)
  calc
    (∫ xi : ℝ, q xi) ≤ ∫ xi : ℝ, r xi := by
      apply integral_mono hq hr
      intro xi
      exact mul_le_mul_of_nonneg_right (hgM xi) (norm_nonneg _)
    _ = M * tiltedLogTrapezoidKernelMass rho delta A B hdelta := by
      rw [integral_const_mul]
      rfl

/-- A completely explicit seminorm upper bound for the Fourier `L¹` mass.
Unlike a pointwise Fourier estimate, this bound is uniform in frequency. -/
theorem tiltedLogTrapezoidKernelMass_le_schwartzSeminorm
    (rho delta A B : ℝ) (hdelta : 0 < delta) :
    tiltedLogTrapezoidKernelMass rho delta A B hdelta ≤
      2 ^ (volume : Measure ℝ).integrablePower *
        (∫ x : ℝ, (1 + ‖x‖) ^
          (-((volume : Measure ℝ).integrablePower : ℝ))) *
        (SchwartzMap.seminorm ℂ 0 0
            (𝓕 (tiltedLogTrapezoidSchwartz rho delta A B hdelta)) +
          SchwartzMap.seminorm ℂ (volume : Measure ℝ).integrablePower 0
            (𝓕 (tiltedLogTrapezoidSchwartz rho delta A B hdelta))) := by
  simpa [tiltedLogTrapezoidKernelMass, tiltedLogTrapezoidKernel,
    zero_add, one_mul] using
      SchwartzMap.integral_pow_mul_iteratedFDeriv_le ℂ volume
        (𝓕 (tiltedLogTrapezoidSchwartz rho delta A B hdelta)) 0 0

/-- The `L¹` mass of the tilted kernel beyond a symmetric frequency
cutoff. -/
def tiltedLogTrapezoidKernelTailMass
    (rho delta A B : ℝ) (hdelta : 0 < delta) (N : ℕ) : ℝ :=
  ∫ xi : ℝ in {xi | (N : ℝ) ≤ |xi|},
    ‖tiltedLogTrapezoidKernel rho delta A B hdelta xi‖

/-- The symmetric tails of the tilted Fourier kernel have mass tending to
zero.  Thus every later use of the inversion integral may be reduced to a
finite frequency window with an arbitrarily small, fully controlled error. -/
theorem tendsto_tiltedLogTrapezoidKernelTailMass_zero
    (rho delta A B : ℝ) (hdelta : 0 < delta) :
    Filter.Tendsto (tiltedLogTrapezoidKernelTailMass rho delta A B hdelta)
      Filter.atTop (nhds 0) := by
  let s : ℕ → Set ℝ := fun N ↦ {xi | (N : ℝ) ≤ |xi|}
  have hsmeas : ∀ N, MeasurableSet (s N) := by
    intro N
    exact measurableSet_le measurable_const continuous_abs.measurable
  have hsanti : Antitone s := by
    intro i j hij xi hxi
    have hijR : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    exact hijR.trans hxi
  have hsInter : ⋂ N, s N = (∅ : Set ℝ) := by
    apply Set.Subset.antisymm
    · intro xi hxi
      exfalso
      simp only [Set.mem_iInter, s, Set.mem_ofPred_eq] at hxi
      obtain ⟨N, hN⟩ := exists_nat_gt |xi|
      exact (not_le_of_gt hN) (hxi N)
    · exact Set.empty_subset _
  have hlim := hsanti.tendsto_setIntegral hsmeas
    ((integrable_tiltedLogTrapezoidKernel rho delta A B hdelta).norm.integrableOn)
  rw [hsInter, setIntegral_empty] at hlim
  exact hlim

/-- Exact Fourier inversion for the tilted window. -/
theorem integral_exp_mul_tiltedLogTrapezoidKernel
    (rho delta A B : ℝ) (hdelta : 0 < delta) (v : ℝ) :
    (∫ xi : ℝ,
        Complex.exp (((2 * Real.pi * xi * v : ℝ) : ℂ) * Complex.I) *
          tiltedLogTrapezoidKernel rho delta A B hdelta xi) =
      (Real.exp (rho * v) : ℂ) *
        logTrapezoidWindow delta A B hdelta v := by
  let S : 𝓢(ℝ, ℂ) := tiltedLogTrapezoidSchwartz rho delta A B hdelta
  have hInv : (𝓕⁻ (𝓕 S)) v = S v := by
    rw [FourierTransform.fourierInv_fourier_eq]
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq'] at hInv
  simp only [smul_eq_mul, RCLike.inner_apply, conj_trivial] at hInv
  change (∫ xi : ℝ,
      Complex.exp (((2 * Real.pi * xi * v : ℝ) : ℂ) * Complex.I) *
        (FourierTransform.fourier S) xi) = S v
  rw [show (fun xi : ℝ ↦
      Complex.exp (((2 * Real.pi * xi * v : ℝ) : ℂ) * Complex.I) *
        (FourierTransform.fourier S) xi) =
      fun xi : ℝ ↦
        Complex.exp (((2 * Real.pi * (v * xi) : ℝ) : ℂ) * Complex.I) *
          (FourierTransform.fourier S) xi by
    funext xi
    congr 2
    push_cast
    ring]
  exact hInv

/-- Exact finite smoothing identity with exponential Mellin tilt. -/
theorem integral_logarithmicDirichletPolynomial_mul_tiltedKernel
    (D : Finset ℕ) (a : ℕ → ℂ)
    (rho delta A B : ℝ) (hdelta : 0 < delta) (t0 : ℝ) :
    (∫ xi : ℝ,
        logarithmicDirichletPolynomial D a (-t0 + 2 * Real.pi * xi) *
          tiltedLogTrapezoidKernel rho delta A B hdelta xi) =
      ∑ n ∈ D, a n * logarithmicPhase n (-t0) *
        ((Real.exp (rho * Real.log n) : ℂ) *
          logTrapezoidWindow delta A B hdelta (Real.log n)) := by
  classical
  rw [show (fun xi : ℝ ↦
      logarithmicDirichletPolynomial D a (-t0 + 2 * Real.pi * xi) *
        tiltedLogTrapezoidKernel rho delta A B hdelta xi) =
      fun xi ↦ ∑ n ∈ D,
        (a n * logarithmicPhase n (-t0)) *
          (Complex.exp (((2 * Real.pi * xi * Real.log n : ℝ) : ℂ) * Complex.I) *
            tiltedLogTrapezoidKernel rho delta A B hdelta xi) by
    funext xi
    unfold logarithmicDirichletPolynomial logarithmicPhase
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n hn
    have hexp :
        Complex.exp ((((-t0 + 2 * Real.pi * xi) * Real.log n : ℝ) : ℂ) * Complex.I) =
          Complex.exp (((-t0 * Real.log n : ℝ) : ℂ) * Complex.I) *
            Complex.exp (((2 * Real.pi * xi * Real.log n : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    ring]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [integral_const_mul,
      integral_exp_mul_tiltedLogTrapezoidKernel rho delta A B hdelta (Real.log n)]
  · intro n hn
    have hphase : Integrable (fun xi : ℝ ↦
        Complex.exp (((2 * Real.pi * xi * Real.log n : ℝ) : ℂ) * Complex.I) *
          tiltedLogTrapezoidKernel rho delta A B hdelta xi) := by
      refine (integrable_tiltedLogTrapezoidKernel rho delta A B hdelta).norm.mono' ?_ ?_
      · exact (by fun_prop : Continuous (fun xi : ℝ ↦
          Complex.exp (((2 * Real.pi * xi * Real.log n : ℝ) : ℂ) * Complex.I))).aestronglyMeasurable.mul
            (integrable_tiltedLogTrapezoidKernel rho delta A B hdelta).aestronglyMeasurable
      filter_upwards with xi
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact hphase.const_mul (a n * logarithmicPhase n (-t0))

/-- Coefficients on the line `Re s = 1 + rho`, written relative to a
coefficient on `Re s = 1`. -/
def exponentiallyShiftedCoefficient
    (rho : ℝ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  (Real.exp (-rho * Real.log n) : ℂ) * a n

/-- The negative exponential in the shifted coefficient is cancelled
exactly by the positive exponential in the tilted window. -/
@[simp] theorem exponentiallyShiftedCoefficient_mul_exp
    (rho : ℝ) (a : ℕ → ℂ) (n : ℕ) :
    exponentiallyShiftedCoefficient rho a n *
      (Real.exp (rho * Real.log n) : ℂ) = a n := by
  have hExpR :
      Real.exp (-rho * Real.log n) * Real.exp (rho * Real.log n) = 1 := by
    calc
      Real.exp (-rho * Real.log n) * Real.exp (rho * Real.log n) =
          Real.exp (-rho * Real.log n + rho * Real.log n) := by rw [Real.exp_add]
      _ = Real.exp 0 := by congr 1; ring
      _ = 1 := Real.exp_zero
  have hExpC :
      (Real.exp (-rho * Real.log n) : ℂ) *
        (Real.exp (rho * Real.log n) : ℂ) = 1 := by
    exact_mod_cast hExpR
  unfold exponentiallyShiftedCoefficient
  calc
    (Real.exp (-rho * Real.log n) : ℂ) * a n *
        (Real.exp (rho * Real.log n) : ℂ) =
      ((Real.exp (-rho * Real.log n) : ℂ) *
        (Real.exp (rho * Real.log n) : ℂ)) * a n := by ring
    _ = a n := by rw [hExpC, one_mul]

/-- Finite tilted inversion with the Mellin factors already cancelled.
This is the form used to recover a `Re s = 1` logarithmic polynomial from
values of the shifted polynomial. -/
theorem integral_shiftedLogarithmicDirichletPolynomial_mul_tiltedKernel
    (D : Finset ℕ) (a : ℕ → ℂ)
    (rho delta A B : ℝ) (hdelta : 0 < delta) (t0 : ℝ) :
    (∫ xi : ℝ,
        logarithmicDirichletPolynomial D (exponentiallyShiftedCoefficient rho a)
            (-t0 + 2 * Real.pi * xi) *
          tiltedLogTrapezoidKernel rho delta A B hdelta xi) =
      ∑ n ∈ D, a n * logarithmicPhase n (-t0) *
        logTrapezoidWindow delta A B hdelta (Real.log n) := by
  rw [integral_logarithmicDirichletPolynomial_mul_tiltedKernel]
  apply Finset.sum_congr rfl
  intro n hn
  calc
    exponentiallyShiftedCoefficient rho a n * logarithmicPhase n (-t0) *
        ((Real.exp (rho * Real.log n) : ℂ) *
          logTrapezoidWindow delta A B hdelta (Real.log n)) =
      (exponentiallyShiftedCoefficient rho a n *
          (Real.exp (rho * Real.log n) : ℂ)) *
        logarithmicPhase n (-t0) *
          logTrapezoidWindow delta A B hdelta (Real.log n) := by ring
    _ = a n * logarithmicPhase n (-t0) *
        logTrapezoidWindow delta A B hdelta (Real.log n) := by rw [exponentiallyShiftedCoefficient_mul_exp]

/-- Exact finite smoothing identity for a logarithmic Dirichlet polynomial.
The polynomial is sampled at `-t0 + 2*pi*xi`, so after the usual
`F(1+i t)` sign convention this is a translate of the vertical polynomial.
-/
theorem integral_logarithmicDirichletPolynomial_mul_kernel
    (D : Finset ℕ) (a : ℕ → ℂ)
    (delta A B : ℝ) (hdelta : 0 < delta) (t0 : ℝ) :
    (∫ xi : ℝ,
        logarithmicDirichletPolynomial D a (-t0 + 2 * Real.pi * xi) *
          logTrapezoidKernel delta A B hdelta xi) =
      ∑ n ∈ D, a n * logarithmicPhase n (-t0) *
        logTrapezoidWindow delta A B hdelta (Real.log n) := by
  classical
  rw [show (fun xi : ℝ ↦
      logarithmicDirichletPolynomial D a (-t0 + 2 * Real.pi * xi) *
        logTrapezoidKernel delta A B hdelta xi) =
      fun xi ↦ ∑ n ∈ D,
        (a n * logarithmicPhase n (-t0)) *
          (Complex.exp (((2 * Real.pi * xi * Real.log n : ℝ) : ℂ) * Complex.I) *
            logTrapezoidKernel delta A B hdelta xi) by
    funext xi
    unfold logarithmicDirichletPolynomial logarithmicPhase
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n hn
    have hexp :
        Complex.exp ((((-t0 + 2 * Real.pi * xi) * Real.log n : ℝ) : ℂ) * Complex.I) =
          Complex.exp (((-t0 * Real.log n : ℝ) : ℂ) * Complex.I) *
            Complex.exp (((2 * Real.pi * xi * Real.log n : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    ring]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [integral_const_mul,
      integral_exp_mul_logTrapezoidKernel delta A B hdelta (Real.log n)]
  · intro n hn
    have hphase : Integrable (fun xi : ℝ ↦
        Complex.exp (((2 * Real.pi * xi * Real.log n : ℝ) : ℂ) * Complex.I) *
          logTrapezoidKernel delta A B hdelta xi) := by
      refine (integrable_logTrapezoidKernel delta A B hdelta).norm.mono' ?_ ?_
      · exact (by fun_prop : Continuous (fun xi : ℝ ↦
          Complex.exp (((2 * Real.pi * xi * Real.log n : ℝ) : ℂ) * Complex.I))).aestronglyMeasurable.mul
            (integrable_logTrapezoidKernel delta A B hdelta).aestronglyMeasurable
      filter_upwards with xi
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact hphase.const_mul (a n * logarithmicPhase n (-t0))

/-- The indices of `D` lying in the plateau of the compact log window. -/
def logSmoothingInterior
    (D : Finset ℕ) (delta A B : ℝ) : Finset ℕ :=
  D.filter fun n ↦ Real.log n ∈ Set.Icc (A + 2 * delta) (B - 2 * delta)

/-- The only remaining indices after removing the plateau: the two boundary
ramps inside `[A,B]`.  Indices outside `[A,B]` contribute exactly zero. -/
def logSmoothingBoundary
    (D : Finset ℕ) (delta A B : ℝ) : Finset ℕ :=
  D.filter fun n ↦
    Real.log n ∈ Set.Icc A B ∧
      Real.log n ∉ Set.Icc (A + 2 * delta) (B - 2 * delta)

/-- The smoothed finite sum is exactly the sharp plateau sum plus the two
finite boundary ramps. -/
theorem sum_mul_logTrapezoidWindow_eq_interior_add_boundary
    (D : Finset ℕ) (c : ℕ → ℂ)
    (delta A B : ℝ) (hdelta : 0 < delta) :
    (∑ n ∈ D, c n * logTrapezoidWindow delta A B hdelta (Real.log n)) =
      (∑ n ∈ logSmoothingInterior D delta A B, c n) +
        ∑ n ∈ logSmoothingBoundary D delta A B,
          c n * logTrapezoidWindow delta A B hdelta (Real.log n) := by
  classical
  simp only [logSmoothingInterior, logSmoothingBoundary, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hi : Real.log n ∈ Set.Icc (A + 2 * delta) (B - 2 * delta)
  · rw [logTrapezoidWindow_eq_one_of_mem_interior delta A B hdelta hi]
    simp [hi]
  · by_cases hs : Real.log n ∈ Set.Icc A B
    · simp [hi, hs]
    · rw [logTrapezoidWindow_eq_zero_of_not_mem delta A B hdelta hs]
      simp [hi, hs]

/-- Exact tilted finite smoothing with the recovered sharp interior and
the two boundary ramps displayed separately. -/
theorem integral_shiftedLogarithmicDirichletPolynomial_mul_tiltedKernel_eq_interior_add_boundary
    (D : Finset ℕ) (a : ℕ → ℂ)
    (rho delta A B : ℝ) (hdelta : 0 < delta) (t0 : ℝ) :
    (∫ xi : ℝ,
        logarithmicDirichletPolynomial D (exponentiallyShiftedCoefficient rho a)
            (-t0 + 2 * Real.pi * xi) *
          tiltedLogTrapezoidKernel rho delta A B hdelta xi) =
      (∑ n ∈ logSmoothingInterior D delta A B,
        a n * logarithmicPhase n (-t0)) +
      ∑ n ∈ logSmoothingBoundary D delta A B,
        a n * logarithmicPhase n (-t0) *
          logTrapezoidWindow delta A B hdelta (Real.log n) := by
  rw [integral_shiftedLogarithmicDirichletPolynomial_mul_tiltedKernel]
  exact sum_mul_logTrapezoidWindow_eq_interior_add_boundary D
    (fun n ↦ a n * logarithmicPhase n (-t0)) delta A B hdelta

/-- Exact finite Fourier smoothing with the sharp interior and the boundary
ramps displayed separately. -/
theorem integral_logarithmicDirichletPolynomial_mul_kernel_eq_interior_add_boundary
    (D : Finset ℕ) (a : ℕ → ℂ)
    (delta A B : ℝ) (hdelta : 0 < delta) (t0 : ℝ) :
    (∫ xi : ℝ,
        logarithmicDirichletPolynomial D a (-t0 + 2 * Real.pi * xi) *
          logTrapezoidKernel delta A B hdelta xi) =
      (∑ n ∈ logSmoothingInterior D delta A B,
        a n * logarithmicPhase n (-t0)) +
      ∑ n ∈ logSmoothingBoundary D delta A B,
        a n * logarithmicPhase n (-t0) *
          logTrapezoidWindow delta A B hdelta (Real.log n) := by
  rw [integral_logarithmicDirichletPolynomial_mul_kernel]
  exact sum_mul_logTrapezoidWindow_eq_interior_add_boundary D
    (fun n ↦ a n * logarithmicPhase n (-t0)) delta A B hdelta

/-- Norm form consumed by the finite Halasz argument.  The main term is a
weighted vertical integral against an integrable Schwartz kernel; every
other coefficient is confined to the two explicit finite boundary ramps. -/
theorem norm_sum_logSmoothingInterior_le_vertical_add_boundary
    (D : Finset ℕ) (a : ℕ → ℂ)
    (delta A B : ℝ) (hdelta : 0 < delta) (t0 : ℝ) :
    ‖∑ n ∈ logSmoothingInterior D delta A B,
        a n * logarithmicPhase n (-t0)‖ ≤
      (∫ xi : ℝ,
        ‖logarithmicDirichletPolynomial D a (-t0 + 2 * Real.pi * xi)‖ *
          ‖logTrapezoidKernel delta A B hdelta xi‖) +
      ∑ n ∈ logSmoothingBoundary D delta A B,
        ‖a n‖ * ‖logTrapezoidWindow delta A B hdelta (Real.log n)‖ := by
  let I : ℂ := ∫ xi : ℝ,
    logarithmicDirichletPolynomial D a (-t0 + 2 * Real.pi * xi) *
      logTrapezoidKernel delta A B hdelta xi
  let M : ℂ := ∑ n ∈ logSmoothingInterior D delta A B,
    a n * logarithmicPhase n (-t0)
  let E : ℂ := ∑ n ∈ logSmoothingBoundary D delta A B,
    a n * logarithmicPhase n (-t0) *
      logTrapezoidWindow delta A B hdelta (Real.log n)
  have hIME : I = M + E := by
    exact integral_logarithmicDirichletPolynomial_mul_kernel_eq_interior_add_boundary
      D a delta A B hdelta t0
  have hM : M = I - E := by
    rw [hIME]
    ring
  change ‖M‖ ≤ _
  rw [hM]
  calc
    ‖I - E‖ ≤ ‖I‖ + ‖E‖ := norm_sub_le _ _
    _ ≤ (∫ xi : ℝ,
          ‖logarithmicDirichletPolynomial D a (-t0 + 2 * Real.pi * xi)‖ *
            ‖logTrapezoidKernel delta A B hdelta xi‖) +
        ∑ n ∈ logSmoothingBoundary D delta A B,
          ‖a n‖ * ‖logTrapezoidWindow delta A B hdelta (Real.log n)‖ := by
      apply add_le_add
      · dsimp [I]
        refine (norm_integral_le_integral_norm _).trans_eq ?_
        apply integral_congr_ae
        filter_upwards with xi
        rw [norm_mul]
      · dsimp [E]
        refine (norm_sum_le _ _).trans ?_
        apply Finset.sum_le_sum
        intro n hn
        rw [norm_mul, norm_mul, norm_logarithmicPhase, mul_one]

/-- Dyadic-Halász specialization.  The main integral now contains the
repository's actual vertical Dirichlet polynomial, translated by `2*pi*xi`.
The left side is precisely that harmonic polynomial restricted to the
plateau; the only loss is the explicit finite boundary support. -/
theorem norm_dyadicSmoothingInterior_le_vertical_add_boundary
    (S : Finset ℕ) (f : ℕ → ℂ) (X : ℕ)
    (delta A B : ℝ) (hdelta : 0 < delta) (t0 : ℝ) :
    ‖∑ n ∈ logSmoothingInterior (dyadicRestrictedSupport S X) delta A B,
        (f n / (n : ℂ)) * logarithmicPhase n (-t0)‖ ≤
      (∫ xi : ℝ,
        ‖dyadicVerticalDirichletPolynomial S f X (t0 - 2 * Real.pi * xi)‖ *
          ‖logTrapezoidKernel delta A B hdelta xi‖) +
      ∑ n ∈ logSmoothingBoundary (dyadicRestrictedSupport S X) delta A B,
        ‖f n / (n : ℂ)‖ *
          ‖logTrapezoidWindow delta A B hdelta (Real.log n)‖ := by
  unfold dyadicVerticalDirichletPolynomial
  convert norm_sum_logSmoothingInterior_le_vertical_add_boundary
      (dyadicRestrictedSupport S X) (fun n ↦ f n / (n : ℂ))
      delta A B hdelta t0 using 1 with xi
  congr 3
  ring_nf

/-- A uniform vertical bound costs exactly the `L¹` mass of the concrete
Schwartz kernel.  This is the form used after one Euler band supplies the
pointwise Halasz saving. -/
theorem integral_norm_dyadicVertical_mul_kernel_le_mass_of_uniform
    (S : Finset ℕ) (f : ℕ → ℂ) (X : ℕ)
    (delta A B : ℝ) (hdelta : 0 < delta) (t0 : ℝ)
    {M : ℝ} (_hM : 0 ≤ M)
    (hvertical : ∀ xi : ℝ,
      ‖dyadicVerticalDirichletPolynomial S f X (t0 - 2 * Real.pi * xi)‖ ≤ M) :
    (∫ xi : ℝ,
        ‖dyadicVerticalDirichletPolynomial S f X (t0 - 2 * Real.pi * xi)‖ *
          ‖logTrapezoidKernel delta A B hdelta xi‖) ≤
      M * logTrapezoidKernelMass delta A B hdelta := by
  let q : ℝ → ℝ := fun xi ↦
    ‖dyadicVerticalDirichletPolynomial S f X (t0 - 2 * Real.pi * xi)‖ *
      ‖logTrapezoidKernel delta A B hdelta xi‖
  let r : ℝ → ℝ := fun xi ↦ M * ‖logTrapezoidKernel delta A B hdelta xi‖
  have hr : Integrable r :=
    (integrable_logTrapezoidKernel delta A B hdelta).norm.const_mul M
  have hq : Integrable q := by
    refine hr.mono' ?_ ?_
    · exact ((continuous_dyadicVerticalDirichletPolynomial S f X).comp
          (by fun_prop : Continuous (fun xi : ℝ ↦ t0 - 2 * Real.pi * xi))).norm.aestronglyMeasurable.mul
        (integrable_logTrapezoidKernel delta A B hdelta).norm.aestronglyMeasurable
    · filter_upwards with xi
      change ‖q xi‖ ≤ r xi
      dsimp only [q, r]
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      exact mul_le_mul_of_nonneg_right (hvertical xi) (norm_nonneg _)
  calc
    (∫ xi : ℝ, q xi) ≤ ∫ xi : ℝ, r xi := by
      apply integral_mono hq hr
      intro xi
      exact mul_le_mul_of_nonneg_right (hvertical xi) (norm_nonneg _)
    _ = M * logTrapezoidKernelMass delta A B hdelta := by
      rw [integral_const_mul]
      rfl

/-- Fully packaged uniform form: sharp interior harmonic polynomial bounded
by kernel mass times the vertical saving, plus only the finite boundary
ramps. -/
theorem norm_dyadicSmoothingInterior_le_mass_mul_uniform_add_boundary
    (S : Finset ℕ) (f : ℕ → ℂ) (X : ℕ)
    (delta A B : ℝ) (hdelta : 0 < delta) (t0 : ℝ)
    {M : ℝ} (hM : 0 ≤ M)
    (hvertical : ∀ xi : ℝ,
      ‖dyadicVerticalDirichletPolynomial S f X (t0 - 2 * Real.pi * xi)‖ ≤ M) :
    ‖∑ n ∈ logSmoothingInterior (dyadicRestrictedSupport S X) delta A B,
        (f n / (n : ℂ)) * logarithmicPhase n (-t0)‖ ≤
      M * logTrapezoidKernelMass delta A B hdelta +
      ∑ n ∈ logSmoothingBoundary (dyadicRestrictedSupport S X) delta A B,
        ‖f n / (n : ℂ)‖ *
          ‖logTrapezoidWindow delta A B hdelta (Real.log n)‖ := by
  exact (norm_dyadicSmoothingInterior_le_vertical_add_boundary
    S f X delta A B hdelta t0).trans
      (add_le_add
        (integral_norm_dyadicVertical_mul_kernel_le_mass_of_uniform
          S f X delta A B hdelta t0 hM hvertical) le_rfl)


end

end Erdos67.MRFiniteHalaszSmoothing
