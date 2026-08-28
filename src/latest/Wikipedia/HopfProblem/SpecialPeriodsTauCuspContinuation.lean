import Wikipedia.HopfProblem.SpecialPeriodsTauCuspLift
import Wikipedia.HopfProblem.SpecialPeriodsTauCuspWidth

/-!
# Continuing a chosen logarithmic cusp germ

The identity theorem propagates equality with a chosen logarithmic lift
throughout the connected source cusp half-plane. For a native holomorphic
map of the upper half-plane, analyticity of its ambient representative is
proved from the actual manifold maps. No target cusp-height bound is
needed after the local germ has been fixed.
-/

open Filter Set Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.TauCusp

open CuspUniformization

/-- Equality with the chosen corrected logarithm near one point propagates
throughout the actual connected logarithmic cusp domain. -/
theorem eqOn_correctedLogarithm_of_eventuallyEq {r : ℝ} (hr : 0 < r)
    {h τ : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (Metric.ball 0 r))
    (hτ : AnalyticOnNhd ℂ τ (CuspFamily.logBase r))
    {a : ℂ} (ha : a ∈ CuspFamily.logBase r)
    (heq : τ =ᶠ[𝓝 a] correctedLogarithm h) :
    Set.EqOn τ (correctedLogarithm h) (CuspFamily.logBase r) :=
  hτ.eqOn_of_preconnected_of_eventuallyEq (correctedLogarithm_analyticOnNhd hh)
    (logBase_convex r hr).isPreconnected ha heq

/-- The ambient representative of a native holomorphic upper-half-plane
map is analytic at every actual upper-half-plane point. -/
theorem upperHalfPlane_ambient_analyticAt {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω τ) {s : ℂ} (hs : 0 < s.im) :
    AnalyticAt ℂ (fun z : ℂ => (τ (ofComplex z) : ℂ)) s := by
  have hc : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun z : ℂ => (τ (ofComplex z) : ℂ)) s :=
    ((UpperHalfPlane.contMDiff_coe.comp hτ) (ofComplex s)).comp s
      (UpperHalfPlane.contMDiffAt_ofComplex hs)
  exact hc.contDiffAt.analyticAt

/-- A source cusp disc of radius less than one lies in the upper half-plane,
so the native map has an analytic ambient representative on its logarithmic preimage. -/
theorem upperHalfPlane_ambient_analyticOnNhd_logBase {r : ℝ} (hr1 : r < 1)
    {τ : ℍ → ℍ} (hτ : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω τ) :
    AnalyticOnNhd ℂ (fun z : ℂ => (τ (ofComplex z) : ℂ)) (CuspFamily.logBase r) := by
  intro s hs
  exact upperHalfPlane_ambient_analyticAt hτ
    (upperHalfPlane_of_exponential_norm_lt_one
      (((CuspFamily.mem_logBase r s).mp hs).trans hr1))

/-- A prescribed native cusp germ determines the native map on the whole
connected source cusp domain, without assuming a target cusp-height bound. -/
theorem native_eqOn_correctedLogarithm_of_eventuallyEq {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (Metric.ball 0 r)) {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω τ)
    {a : ℂ} (ha : a ∈ CuspFamily.logBase r)
    (heq : (fun z : ℂ => (τ (ofComplex z) : ℂ)) =ᶠ[𝓝 a] correctedLogarithm h) :
    Set.EqOn (fun z : ℂ => (τ (ofComplex z) : ℂ))
      (correctedLogarithm h) (CuspFamily.logBase r) :=
  eqOn_correctedLogarithm_of_eventuallyEq hr hh
    (upperHalfPlane_ambient_analyticOnNhd_logBase hr1 hτ) ha heq

/-- The difference between the native lift and the logarithmic source
coordinate is exactly the prescribed analytic function of the disc parameter. -/
theorem native_sub_eq_correction_of_eventuallyEq {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (Metric.ball 0 r)) {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω τ)
    {a : ℂ} (ha : a ∈ CuspFamily.logBase r)
    (heq : (fun z : ℂ => (τ (ofComplex z) : ℂ)) =ᶠ[𝓝 a] correctedLogarithm h)
    {s : ℂ} (hs : s ∈ CuspFamily.logBase r) :
    (τ (ofComplex s) : ℂ) - s = h (exponential s) := by
  have hglobal := native_eqOn_correctedLogarithm_of_eventuallyEq hr hr1 hh hτ ha heq
  have hsEq : (τ (ofComplex s) : ℂ) = correctedLogarithm h s := hglobal hs
  rw [hsEq, correctedLogarithm, add_sub_cancel_left]

/-- Clockwise integer covariance follows from the propagated exact cusp
formula, not from an additional equivariance or high-image assumption. -/
theorem native_sub_int_of_eventuallyEq {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (Metric.ball 0 r)) {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω τ)
    {a : ℂ} (ha : a ∈ CuspFamily.logBase r)
    (heq : (fun z : ℂ => (τ (ofComplex z) : ℂ)) =ᶠ[𝓝 a] correctedLogarithm h)
    {s : ℂ} (hs : s ∈ CuspFamily.logBase r) (k : ℤ) :
    (τ (ofComplex (s - (k : ℂ))) : ℂ) = (τ (ofComplex s) : ℂ) - k := by
  have hglobal := native_eqOn_correctedLogarithm_of_eventuallyEq hr hr1 hh hτ ha heq
  have hsk : s - (k : ℂ) ∈ CuspFamily.logBase r := by
    rw [CuspFamily.mem_logBase, CuspFamily.exponential_sub_int]
    exact (CuspFamily.mem_logBase r s).mp hs
  have hsEq : (τ (ofComplex s) : ℂ) = correctedLogarithm h s := hglobal hs
  have hskEq : (τ (ofComplex (s - (k : ℂ))) : ℂ) =
      correctedLogarithm h (s - (k : ℂ)) := hglobal hsk
  rw [hskEq, hsEq, correctedLogarithm_sub_int]

/-- The actual width-q cusp region is convex, being the real-linear
preimage of the width-one logarithmic half-plane. -/
theorem widthLogBase_convex (w : ℝ) {r : ℝ} (hr : 0 < r) :
    Convex ℝ {s : ℂ | ‖Function.Periodic.qParam w s‖ < r} := by
  have hset : {s : ℂ | ‖Function.Periodic.qParam w s‖ < r} =
      (LinearMap.mulRight ℝ (w : ℂ)⁻¹) ⁻¹' (CuspFamily.logBase r : Set ℂ) := by
    ext s
    change ‖Function.Periodic.qParam w s‖ < r ↔
      s * (w : ℂ)⁻¹ ∈ CuspFamily.logBase r
    rw [CuspFamily.mem_logBase, qParam_eq_exponential_div, div_eq_mul_inv]
  rw [hset]
  exact (logBase_convex r hr).linear_preimage (LinearMap.mulRight ℝ (w : ℂ)⁻¹)

/-- At positive width the actual width-q unit disc comes from source
points in the upper half-plane. -/
theorem upperHalfPlane_of_qParam_norm_lt_one (w : ℝ) (hw : 0 < w) {s : ℂ}
    (hs : ‖Function.Periodic.qParam w s‖ < 1) : 0 < s.im := by
  have hsd : 0 < (s / (w : ℂ)).im := upperHalfPlane_of_exponential_norm_lt_one
    (by simpa only [qParam_eq_exponential_div] using hs)
  rw [Complex.div_ofReal_im] at hsd
  exact (div_pos_iff_of_pos_right hw).mp hsd

/-- The identity theorem propagates a prescribed logarithmic germ on the
actual width-q cusp region. -/
theorem eqOn_correctedLogarithmWidth_of_eventuallyEq (w : ℝ) {r : ℝ} (hr : 0 < r)
    {h τ : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (Metric.ball 0 r))
    (hτ : AnalyticOnNhd ℂ τ {s : ℂ | ‖Function.Periodic.qParam w s‖ < r})
    {a : ℂ} (ha : ‖Function.Periodic.qParam w a‖ < r)
    (heq : τ =ᶠ[𝓝 a] correctedLogarithmWidth w h) :
    Set.EqOn τ (correctedLogarithmWidth w h)
      {s : ℂ | ‖Function.Periodic.qParam w s‖ < r} :=
  hτ.eqOn_of_preconnected_of_eventuallyEq (correctedLogarithmWidth_analyticOnNhd w hh)
    (widthLogBase_convex w hr).isPreconnected ha heq

/-- For any positive source width, a prescribed germ fixes a native
holomorphic upper-half-plane map throughout the actual width-q cusp region. -/
theorem native_eqOn_correctedLogarithmWidth_of_eventuallyEq (w : ℝ) (hw : 0 < w)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (Metric.ball 0 r)) {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω τ)
    {a : ℂ} (ha : ‖Function.Periodic.qParam w a‖ < r)
    (heq : (fun z : ℂ => (τ (ofComplex z) : ℂ)) =ᶠ[𝓝 a]
      correctedLogarithmWidth w h) :
    Set.EqOn (fun z : ℂ => (τ (ofComplex z) : ℂ)) (correctedLogarithmWidth w h)
      {s : ℂ | ‖Function.Periodic.qParam w s‖ < r} := by
  apply eqOn_correctedLogarithmWidth_of_eventuallyEq w hr hh ?_ ha heq
  intro s hs
  exact upperHalfPlane_ambient_analyticAt hτ
    (upperHalfPlane_of_qParam_norm_lt_one w hw (lt_trans hs hr1))

/-- The native lift minus the width-normalized source coordinate is the
prescribed analytic disc function on the whole source cusp region. -/
theorem native_sub_div_eq_correctionWidth_of_eventuallyEq (w : ℝ) (hw : 0 < w)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (Metric.ball 0 r)) {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω τ)
    {a : ℂ} (ha : ‖Function.Periodic.qParam w a‖ < r)
    (heq : (fun z : ℂ => (τ (ofComplex z) : ℂ)) =ᶠ[𝓝 a]
      correctedLogarithmWidth w h)
    {s : ℂ} (hs : ‖Function.Periodic.qParam w s‖ < r) :
    (τ (ofComplex s) : ℂ) - s / w = h (Function.Periodic.qParam w s) := by
  have hglobal := native_eqOn_correctedLogarithmWidth_of_eventuallyEq w hw hr hr1 hh hτ ha heq
  have hsEq : (τ (ofComplex s) : ℂ) = correctedLogarithmWidth w h s := hglobal hs
  rw [hsEq, correctedLogarithmWidth, add_sub_cancel_left]

/-- Clockwise translation by an integer number of source widths changes
the continued native modular lift by exactly that integer. -/
theorem native_sub_int_mul_width_of_eventuallyEq (w : ℝ) (hw : 0 < w)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (Metric.ball 0 r)) {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω τ)
    {a : ℂ} (ha : ‖Function.Periodic.qParam w a‖ < r)
    (heq : (fun z : ℂ => (τ (ofComplex z) : ℂ)) =ᶠ[𝓝 a]
      correctedLogarithmWidth w h)
    {s : ℂ} (hs : ‖Function.Periodic.qParam w s‖ < r) (k : ℤ) :
    (τ (ofComplex (s - (k : ℂ) * w)) : ℂ) = (τ (ofComplex s) : ℂ) - k := by
  have hglobal := native_eqOn_correctedLogarithmWidth_of_eventuallyEq w hw hr hr1 hh hτ ha heq
  have hsk : ‖Function.Periodic.qParam w (s - (k : ℂ) * w)‖ < r := by
    rw [qParam_sub_int_mul_width w hw.ne']
    exact hs
  have hsEq : (τ (ofComplex s) : ℂ) = correctedLogarithmWidth w h s := hglobal hs
  have hskEq : (τ (ofComplex (s - (k : ℂ) * w)) : ℂ) =
      correctedLogarithmWidth w h (s - (k : ℂ) * w) := hglobal hsk
  rw [hskEq, hsEq, correctedLogarithmWidth_sub_int_mul_width w hw.ne']

end Wikipedia.HopfProblem.SpecialPeriods.TauCusp
