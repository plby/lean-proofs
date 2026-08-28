import Mathlib.Analysis.Analytic.Order
import Wikipedia.HopfProblem.RiemannBoundaryDirections
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Tactic

/-!
# Noncriticality at a straight analytic boundary

A holomorphic germ taking the upper side of a real boundary point into the
upper half-plane, and taking the boundary point to zero, has a simple zero.
The proof uses its actual first nonzero Taylor term: a term of degree at
least two has a direction in the upper half-plane with negative imaginary
part, which contradicts the one-sided mapping property.
-/

noncomputable section

open Set Filter Topology

namespace Wikipedia.HopfProblem.RiemannMapping

/-- Every positive ray based at `a` tends to `a`. -/
theorem tendsto_boundaryRay (a v : ℂ) :
    Tendsto (fun t : ℝ => a + (t : ℂ) * v) (𝓝[>] 0) (𝓝 a) := by
  have hc : Continuous (fun t : ℝ => a + (t : ℂ) * v) := by fun_prop
  simpa using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds

/-- A positive ray in an upper direction stays above a real base point. -/
theorem boundaryRay_im_pos {a v : ℂ} (ha : a.im = 0) (hv : 0 < v.im)
    {t : ℝ} (ht : 0 < t) : 0 < (a + (t : ℂ) * v).im := by
  simpa only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, ha, zero_mul, mul_zero, add_zero, zero_add] using mul_pos ht hv

/-- The strict one-sided mapping property rules out an identically zero germ. -/
theorem analyticOrderAt_ne_top_of_upper_halfPlane
    {f : ℂ → ℂ} {a : ℂ} (ha : a.im = 0)
    (hupper : ∀ᶠ z in 𝓝 a, 0 < z.im → 0 < (f z).im) :
    analyticOrderAt f a ≠ ⊤ := by
  intro htop
  have hz := (tendsto_boundaryRay a Complex.I).eventually
    (analyticOrderAt_eq_top.mp htop)
  have hp := (tendsto_boundaryRay a Complex.I).eventually hupper
  have hfalse : ∀ᶠ t : ℝ in 𝓝[>] 0, False := by
    filter_upwards [self_mem_nhdsWithin, hz, hp] with t ht hzero hpos
    have hi := hpos (boundaryRay_im_pos ha (by simp) ht)
    simp only [hzero, Complex.zero_im, lt_self_iff_false] at hi
  obtain ⟨t, ht⟩ := hfalse.exists
  exact ht

/-- Every upper direction gives a nonnegative imaginary part for the leading
Taylor coefficient after multiplying by the corresponding direction power. -/
theorem nonneg_im_leading_of_upper_halfPlane
    {f u : ℂ → ℂ} {a : ℂ} {m : ℕ} (ha : a.im = 0)
    (hu : ContinuousAt u a)
    (hfactor : ∀ᶠ z in 𝓝 a, f z = (z - a) ^ m * u z)
    (hupper : ∀ᶠ z in 𝓝 a, 0 < z.im → 0 < (f z).im)
    {v : ℂ} (hv : 0 < v.im) : 0 ≤ (v ^ m * u a).im := by
  have hray := tendsto_boundaryRay a v
  have hlimC : Tendsto (fun t : ℝ => v ^ m * u (a + (t : ℂ) * v))
      (𝓝[>] 0) (𝓝 (v ^ m * u a)) :=
    tendsto_const_nhds.mul (hu.tendsto.comp hray)
  have hlim : Tendsto (fun t : ℝ => (v ^ m * u (a + (t : ℂ) * v)).im)
      (𝓝[>] 0) (𝓝 (v ^ m * u a).im) :=
    Complex.continuous_im.continuousAt.tendsto.comp hlimC
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin, hray.eventually hfactor,
    hray.eventually hupper] with t ht hft hpos
  have hft' : (f (a + (t : ℂ) * v)).im =
      t ^ m * (v ^ m * u (a + (t : ℂ) * v)).im := by
    rw [hft, add_sub_cancel_left, mul_pow, mul_assoc]
    simp only [← Complex.ofReal_pow, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
  have hp : 0 < t ^ m * (v ^ m * u (a + (t : ℂ) * v)).im := by
    rw [← hft']
    exact hpos (boundaryRay_im_pos ha hv ht)
  exact ((mul_pos_iff_of_pos_left (pow_pos ht m)).mp hp).le

/-- An analytic germ which vanishes at a real boundary point and maps the
upper side into the upper half-plane has analytic order exactly one. -/
theorem analyticOrderAt_eq_one_of_upper_halfPlane
    {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) (ha : a.im = 0)
    (hfa : f a = 0)
    (hupper : ∀ᶠ z in 𝓝 a, 0 < z.im → 0 < (f z).im) :
    analyticOrderAt f a = 1 := by
  have hfin := analyticOrderAt_ne_top_of_upper_halfPlane ha hupper
  let m := analyticOrderNatAt f a
  have horder : (m : ℕ∞) = analyticOrderAt f a := Nat.cast_analyticOrderNatAt hfin
  have hm0 : m ≠ 0 := by
    intro hm
    have hf0 : analyticOrderAt f a = 0 := by simpa [hm] using horder.symm
    exact (hf.analyticOrderAt_ne_zero.mpr hfa) hf0
  obtain ⟨u, hu, hua, hfactor⟩ := hf.analyticOrderAt_eq_natCast.mp horder.symm
  have hm2 : ¬2 ≤ m := by
    intro hm
    obtain ⟨v, hv, hneg⟩ := exists_upperHalf_power_direction hua hm
    have hnonneg : 0 ≤ (v ^ m * u a).im :=
      nonneg_im_leading_of_upper_halfPlane ha hu.continuousAt
        (by simpa only [smul_eq_mul] using hfactor) hupper hv
    rw [mul_comm] at hneg
    exact hneg.not_ge hnonneg
  have hm : m = 1 := by omega
  rw [← horder, hm]
  rfl

/-- The derivative at a straight boundary point is nonzero for an analytic
germ mapping the upper side into the upper half-plane and vanishing there. -/
theorem deriv_ne_zero_of_upper_halfPlane
    {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) (ha : a.im = 0)
    (hfa : f a = 0)
    (hupper : ∀ᶠ z in 𝓝 a, 0 < z.im → 0 < (f z).im) :
    deriv f a ≠ 0 := by
  have ho := analyticOrderAt_eq_one_of_upper_halfPlane hf ha hfa hupper
  have hd := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hf).mp ho
  simpa only [iteratedDeriv_one] using hd.2

/-- A normalized logarithm turns the unit-disc side of a boundary point
into the upper half-plane side of zero. -/
def boundaryLog (f : ℂ → ℂ) (a z : ℂ) : ℂ :=
  -Complex.I * Complex.log (f z / f a)

@[simp] theorem boundaryLog_self {f : ℂ → ℂ} {a : ℂ} (hfa : f a ≠ 0) :
    boundaryLog f a a = 0 := by
  simp [boundaryLog, hfa]

/-- The normalized logarithm is analytic at the boundary point because its
logarithm argument there is one, independently of the argument of `f a`. -/
theorem analyticAt_boundaryLog {f : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) (hfa : f a ≠ 0) :
    AnalyticAt ℂ (boundaryLog f a) a := by
  have hratio : AnalyticAt ℂ (fun z => f z / f a) a := hf.div_const
  have hslit : f a / f a ∈ Complex.slitPlane := by simp [hfa]
  exact analyticAt_const.mul (hratio.clog hslit)

/-- The derivative of the normalized logarithm at its center. -/
theorem hasDerivAt_boundaryLog {f : ℂ → ℂ} {a d : ℂ}
    (hf : HasDerivAt f d a) (hfa : f a ≠ 0) :
    HasDerivAt (boundaryLog f a) (-Complex.I * (d / f a)) a := by
  have hslit : f a / f a ∈ Complex.slitPlane := by simp [hfa]
  have hlog := (hf.div_const (f a)).clog hslit
  change HasDerivAt (fun z => -Complex.I * Complex.log (f z / f a))
    (-Complex.I * (d / f a)) a
  simpa only [div_self hfa, div_one] using hlog.const_mul (-Complex.I)

/-- At points inside the unit disc where `f` does not vanish, the
normalized logarithm has strictly positive imaginary part. -/
theorem im_boundaryLog_pos {f : ℂ → ℂ} {a z : ℂ}
    (hfa : ‖f a‖ = 1) (hfz : f z ≠ 0) (hz : ‖f z‖ < 1) :
    0 < (boundaryLog f a z).im := by
  have hfa0 : f a ≠ 0 := by
    intro hzero
    simp [hzero] at hfa
  have hratio0 : 0 < ‖f z / f a‖ := norm_pos_iff.mpr (div_ne_zero hfz hfa0)
  have hratio1 : ‖f z / f a‖ < 1 := by simpa only [norm_div, hfa, div_one] using hz
  have hlog := Real.log_neg hratio0 hratio1
  simpa [boundaryLog, Complex.mul_im, Complex.log_re] using neg_pos.mpr hlog

/-- A holomorphic germ taking one side of a straight boundary into the
unit disc, with its boundary value on the unit circle, is noncritical at
that boundary point. No boundary derivative or inverse is assumed. -/
theorem deriv_ne_zero_of_upper_halfPlane_to_unitDisc
    {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) (ha : a.im = 0)
    (hfa : ‖f a‖ = 1)
    (hupper : ∀ᶠ z in 𝓝 a, 0 < z.im → ‖f z‖ < 1) :
    deriv f a ≠ 0 := by
  have hfa0 : f a ≠ 0 := by
    intro hzero
    simp [hzero] at hfa
  have hnz : ∀ᶠ z in 𝓝 a, f z ≠ 0 := hf.continuousAt.eventually_ne hfa0
  have hlogUpper : ∀ᶠ z in 𝓝 a,
      0 < z.im → 0 < (boundaryLog f a z).im := by
    filter_upwards [hupper, hnz] with z hz hzne hzim
    exact im_boundaryLog_pos hfa hzne (hz hzim)
  have hlogDeriv := deriv_ne_zero_of_upper_halfPlane
    (analyticAt_boundaryLog hf hfa0) ha (boundaryLog_self hfa0) hlogUpper
  intro hderiv
  apply hlogDeriv
  simpa [hderiv] using (hasDerivAt_boundaryLog hf.differentiableAt.hasDerivAt hfa0).deriv

end Wikipedia.HopfProblem.RiemannMapping
