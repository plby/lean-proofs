import Wikipedia.HopfProblem.SpecialPeriodsTauCuspQ
import Wikipedia.HopfProblem.SpecialPeriodsTauCuspDomain
import Wikipedia.HopfProblem.SpecialPeriodsTauCuspComparison

/-!
# Constructing the logarithmic modular lift of a simple pole

The actual inverse modular cusp coordinate and an actual logarithm of its
unit produce a holomorphic lift on an entire logarithmic half-plane.
Its upper-half-plane image follows from the q-norm bound. Clockwise
translation covariance is an exact identity of the constructed function.
-/

noncomputable section

open Filter Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.TauCusp

open CuspUniformization

/-- A holomorphic correction in the punctured-disc parameter, pulled back
to its actual logarithmic covering. -/
def correctedLogarithm (h : ℂ → ℂ) (s : ℂ) : ℂ := s + h (exponential s)

theorem correctedLogarithm_exponential (h : ℂ → ℂ) (s : ℂ) :
    exponential (correctedLogarithm h s) =
      exponential s * exponential (h (exponential s)) := exponential_add _ _

/-- The clockwise covariance does not require selecting pointwise sheets. -/
theorem correctedLogarithm_sub_int (h : ℂ → ℂ) (s : ℂ) (k : ℤ) :
    correctedLogarithm h (s - k) = correctedLogarithm h s - k := by
  simp only [correctedLogarithm, CuspFamily.exponential_sub_int]
  abel

theorem correctedLogarithm_analyticAt {r : ℝ} {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (Metric.ball 0 r)) {s : ℂ}
    (hs : s ∈ CuspFamily.logBase r) : AnalyticAt ℂ (correctedLogarithm h) s :=
  analyticAt_id.add ((hh (exponential s) hs).comp
    exponential_holomorphic.contDiffAt.analyticAt)

theorem correctedLogarithm_analyticOnNhd {r : ℝ} {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (Metric.ball 0 r)) :
    AnalyticOnNhd ℂ (correctedLogarithm h) (CuspFamily.logBase r) :=
  fun _ hs => correctedLogarithm_analyticAt hh hs

theorem correctedLogarithm_holomorphic {r : ℝ} {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (Metric.ball 0 r)) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun s : CuspFamily.LogBase r => correctedLogarithm h s) := by
  intro s
  exact (correctedLogarithm_analyticAt hh s.2).contDiffAt.contMDiffAt.comp s
    (contMDiff_subtype_val s)

theorem correctedLogarithm_upperHalfPlane_holomorphic {r : ℝ} {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (Metric.ball 0 r))
    (hpos : ∀ s ∈ CuspFamily.logBase r, 0 < (correctedLogarithm h s).im) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun s : CuspFamily.LogBase r =>
      UpperHalfPlane.ofComplex (correctedLogarithm h s)) := by
  intro s
  exact (UpperHalfPlane.contMDiffAt_ofComplex (hpos s s.2)).comp s
    (correctedLogarithm_holomorphic hh s)

/-- An actual logarithmic lift of `a(t)/t`, normalized at the cusp.
Both the source radius and target q-radius can be prescribed in advance.
The correction is derived from the actual inverse j-chart and logarithm. -/
theorem exists_simplePole_logarithmic_lift {a : ℂ → ℂ}
    (ha : AnalyticAt ℂ a 0) (ha0 : a 0 ≠ 0)
    {R r₀ : ℝ} (hR : 0 < R) (hr₀ : 0 < r₀) :
    ∃ r > 0, r < r₀ ∧ r < 1 ∧ ∃ h : ℂ → ℂ,
      AnalyticOnNhd ℂ h (Metric.ball 0 r) ∧
      h 0 = logarithm (1 / a 0) ∧
      (∀ t ∈ Metric.ball 0 r, exponential (h t) = simplePoleUnit a t) ∧
      ∀ s ∈ CuspFamily.logBase r,
        exponential (correctedLogarithm h s) = simplePoleQ a (exponential s) ∧
        0 < (correctedLogarithm h s).im ∧
        ‖exponential (correctedLogarithm h s)‖ < R ∧
        modularJ (UpperHalfPlane.ofComplex (correctedLogarithm h s)) =
          a (exponential s) / exponential s := by
  obtain ⟨rq, hrq, _, _, hq⟩ :=
    exists_simplePoleQ_coordinate ha ha0 (lt_min hR zero_lt_one)
  obtain ⟨rh, hrh, h, hh, hh0, he⟩ := analytic_unit_normalized_logarithm
    (simplePoleUnit_analyticAt ha ha0) (by simpa using one_div_ne_zero ha0)
  obtain ⟨r, hr, hrr⟩ := exists_between
    (show 0 < min rq (min rh (min r₀ 1)) from
      lt_min hrq (lt_min hrh (lt_min hr₀ zero_lt_one)))
  have hparts : r < rq ∧ r < rh ∧ r < r₀ ∧ r < 1 := by
    simpa only [lt_min_iff] using hrr
  have hh' : AnalyticOnNhd ℂ h (Metric.ball 0 r) :=
    hh.mono (Metric.ball_subset_ball hparts.2.1.le)
  refine ⟨r, hr, hparts.2.2.1, hparts.2.2.2, h, hh', ?_, ?_, ?_⟩
  · simpa only [simplePoleUnit_zero] using hh0
  · intro t ht
    exact he t (Metric.ball_subset_ball hparts.2.1.le ht)
  · intro s hs
    have hst : exponential s ∈ Metric.ball (0 : ℂ) r := hs
    have hsq := hq (exponential s) (Metric.ball_subset_ball hparts.1.le hst)
    have hse := he (exponential s) (Metric.ball_subset_ball hparts.2.1.le hst)
    have hτq : exponential (correctedLogarithm h s) = simplePoleQ a (exponential s) := by
      rw [correctedLogarithm_exponential, hse, simplePoleQ_eq_mul_unit]
    have hτpos : 0 < (correctedLogarithm h s).im :=
      upperHalfPlane_of_exponential_norm_lt_one
        (by rw [hτq]; exact lt_of_lt_of_le hsq.2.2.1 (min_le_right R 1))
    refine ⟨hτq, hτpos, ?_, ?_⟩
    · rw [hτq]
      exact lt_of_lt_of_le hsq.2.2.1 (min_le_left R 1)
    · rw [← modularJInQ_exponential hτpos, hτq]
      exact hsq.2.2.2 (exponential_ne_zero s)

end Wikipedia.HopfProblem.SpecialPeriods.TauCusp
