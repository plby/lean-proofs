import Wikipedia.NoExoticSixSphere.SphereCurveAngle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The energy lower bound for antipodal sphere curves

The regularized-angle derivative estimate is integrated, then the
regularization parameter tends to one by continuity. Every smooth unit
curve from a vector to its antipode on the unit time interval has energy
at least `π²`; no geodesic or stationarity assumption is made.
-/

open scoped ContDiff
open Set

namespace NoExoticSixSphere.SphereCurveAngle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {γ : ℝ → E}

theorem regularized_energy_bound_on {x : E} (hx : ‖x‖ = 1)
    (hγ : ContDiff ℝ ∞ γ) (hn : ∀ t, ‖γ t‖ = 1)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) {l u : ℝ} (hlu : l ≤ u) (c : ℝ) :
    2 * c * (angle x γ r u - angle x γ r l) ≤
      (∫ t : ℝ in l..u, ‖deriv γ t‖ ^ 2) + (u - l) * c ^ 2 := by
  let f := angle x γ r
  have hf : ContDiff ℝ ∞ f := contDiff_angle hx hn hr hr1 hγ
  have hf' : Continuous (deriv f) := (ContDiff.deriv' (n := ∞) hf).continuous
  have hg' : Continuous (fun t ↦ ‖deriv γ t‖ ^ 2) :=
    (ContDiff.deriv' (n := ∞) hγ).continuous.norm.pow 2
  have hpoint (t : ℝ) : 2 * c * deriv f t ≤ ‖deriv γ t‖ ^ 2 + c ^ 2 := by
    have hd := hasDerivAt_angle hx (hn t) hr hr1
      (((hγ.differentiable (by simp)) t).hasDerivAt)
    have hb := angleDerivative_sq_le hx hn hr hr1
      (((hγ.differentiable (by simp)) t).hasDerivAt)
    change HasDerivAt f _ t at hd
    rw [← hd.deriv] at hb
    nlinarith [sq_nonneg (deriv f t - c)]
  have hi := intervalIntegral.integral_mono (μ := MeasureTheory.volume)
    hlu ((continuous_const.mul hf').intervalIntegrable l u)
    ((hg'.add continuous_const).intervalIntegrable l u) hpoint
  simp only [Pi.mul_apply, Pi.add_apply] at hi
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ ↦ ((hf.differentiable (by simp)) t).hasDerivAt)
      (hf'.intervalIntegrable l u),
    intervalIntegral.integral_add (hg'.intervalIntegrable l u)
      (continuous_const.intervalIntegrable l u),
    intervalIntegral.integral_const] at hi
  simpa only [sub_zero, smul_eq_mul, one_mul] using hi

theorem regularized_energy_bound (hγ : ContDiff ℝ ∞ γ) (hn : ∀ t, ‖γ t‖ = 1)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (c : ℝ) :
    2 * c * (angle (γ 0) γ r 1 - angle (γ 0) γ r 0) ≤
      (∫ t : ℝ in 0..1, ‖deriv γ t‖ ^ 2) + c ^ 2 := by
  simpa only [sub_zero, one_mul] using
    regularized_energy_bound_on (hn 0) hγ hn hr hr1 zero_le_one c

theorem antipodal_energy_ge (hγ : ContDiff ℝ ∞ γ) (hn : ∀ t, ‖γ t‖ = 1)
    (hend : γ 1 = -γ 0) :
    Real.pi ^ 2 ≤ ∫ t : ℝ in 0..1, ‖deriv γ t‖ ^ 2 := by
  let Eγ := ∫ t : ℝ in 0..1, ‖deriv γ t‖ ^ 2
  let f : ℝ → ℝ := fun r ↦ 2 * Real.pi * (Real.arccos (-r) - Real.arccos r)
  have hf : Continuous f :=
    continuous_const.mul ((Real.continuous_arccos.comp continuous_neg).sub Real.continuous_arccos)
  have hc : IsClosed {r : ℝ | f r ≤ Eγ + Real.pi ^ 2} :=
    isClosed_le hf continuous_const
  have hsub : Ioo (0 : ℝ) 1 ⊆ {r : ℝ | f r ≤ Eγ + Real.pi ^ 2} := by
    intro r hr
    change f r ≤ Eγ + Real.pi ^ 2
    have h := regularized_energy_bound hγ hn hr.1.le hr.2 Real.pi
    simpa only [angle, hend, inner_neg_right, real_inner_self_eq_norm_sq, hn 0,
      one_pow, mul_one, mul_neg, f, Eγ] using h
  have hone : (1 : ℝ) ∈ closure (Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨zero_le_one, le_rfl⟩
  have hlim := (closure_minimal hsub hc) hone
  change f 1 ≤ Eγ + Real.pi ^ 2 at hlim
  simp only [f, Real.arccos_neg_one, Real.arccos_one, sub_zero] at hlim
  change Real.pi ^ 2 ≤ Eγ
  nlinarith

end NoExoticSixSphere.SphereCurveAngle
