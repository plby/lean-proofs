import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscApproximationKernel
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Quantitative polynomial approximation on smaller closed bidiscs

The original analytic function is its actual double Cauchy integral.  The
finite polynomial is the same bounded functional applied to the finite
kernel.  The geometric error bound therefore gives uniform convergence,
and hence a finite polynomial for every positive tolerance.
-/

noncomputable section

open Set Metric Filter Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscApproximation

open CuspNormalization.Germs.NormalIntegral
open PeriodTorusLineBundleClassificationPolydiscAnalytic

/-- The actual Cauchy representation for a function analytic near the
closed outer bidisc; the slice hypotheses are derived here. -/
theorem analytic_eq_boundaryKernel_functional {f : ℂ × ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R ×ˢ closedBall 0 R))
    {z : ℂ × ℂ} (hz : z ∈ ball 0 R ×ˢ ball 0 R) :
    f z = normalizedDoubleCircleIntegralCLM R hR R hR
      (boundaryKernel R R (boundaryValues hf.continuousOn) z) := by
  apply eq_boundaryKernel_functional hR hR hf.continuousOn
  · intro w hw
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball (0 : ℂ) hR.ne']
    intro v hv
    exact ((hf (v, w) ⟨hv, hw⟩).comp₂ analyticAt_id analyticAt_const).differentiableAt
      |>.differentiableWithinAt
  · intro v hv
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball (0 : ℂ) hR.ne']
    intro w hw
    exact ((hf (v, w) ⟨hv, hw⟩).comp₂ analyticAt_const analyticAt_id).differentiableAt
      |>.differentiableWithinAt
  · exact hz

/-- One explicit uniform error bound, depending only on the two radii,
the actual boundary norm, and the norm of the actual integration operator. -/
def approximationError (r R : ℝ) (hR : 0 < R)
    (u : C(BoundaryTorus R R, ℂ)) (N : ℕ) : ℝ :=
  ‖normalizedDoubleCircleIntegralCLM R hR R hR‖ *
    ((3 * (r / R) ^ N / (R - r) ^ 2) * ‖u‖)

theorem approximationError_tendsto {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hR : 0 < R) (u : C(BoundaryTorus R R, ℂ)) :
    Tendsto (approximationError r R hR u) atTop (𝓝 0) := by
  have hq₀ : 0 ≤ r / R := div_nonneg hr hR.le
  have hq₁ : r / R < 1 := (div_lt_one hR).mpr hrR
  have h := (((tendsto_pow_atTop_nhds_zero_of_lt_one hq₀ hq₁).const_mul 3).div_const
    ((R - r) ^ 2)).mul_const ‖u‖
  have h' := h.const_mul ‖normalizedDoubleCircleIntegralCLM R hR R hR‖
  change Tendsto (fun N => ‖normalizedDoubleCircleIntegralCLM R hR R hR‖ *
    ((3 * (r / R) ^ N / (R - r) ^ 2) * ‖u‖)) atTop (𝓝 0)
  simpa only [mul_zero, zero_div, zero_mul] using h'

/-- Every point of the inner closed bidisc satisfies the same explicit
finite-polynomial error estimate. -/
theorem cauchyPolynomial_error_norm_le {f : ℂ × ℂ → ℂ} {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R ×ˢ closedBall 0 R))
    (N : ℕ) {z : ℂ × ℂ} (hz : z ∈ closedBall 0 r ×ˢ closedBall 0 r) :
    ‖cauchyPolynomial R hR (boundaryValues hf.continuousOn) N z - f z‖ ≤
      approximationError r R hR (boundaryValues hf.continuousOn) N := by
  rw [cauchyPolynomial_eq_functional,
    analytic_eq_boundaryKernel_functional hR hf (closedBidisc_subset_openBidisc hrR hz),
    ← map_sub]
  exact ((normalizedDoubleCircleIntegralCLM R hR R hR).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left
      (partialBoundaryKernel_error_norm_le hr hrR (boundaryValues hf.continuousOn) N hz)
      (norm_nonneg _))

/-- A genuinely finite Cauchy polynomial approximates the function uniformly
on the smaller closed bidisc, to any specified positive tolerance. -/
theorem exists_cauchyPolynomial_approximation {f : ℂ × ℂ → ℂ} {r R ε : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hε : 0 < ε)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R ×ˢ closedBall 0 R)) :
    ∃ N : ℕ, ∀ z ∈ closedBall (0 : ℂ) r ×ˢ closedBall 0 r,
      ‖cauchyPolynomial R (lt_of_le_of_lt hr hrR) (boundaryValues hf.continuousOn) N z - f z‖
        < ε := by
  have hR : 0 < R := lt_of_le_of_lt hr hrR
  obtain ⟨N, hN⟩ := ((approximationError_tendsto hr hrR hR
    (boundaryValues hf.continuousOn)).eventually_lt_const hε).exists
  exact ⟨N, fun z hz => (cauchyPolynomial_error_norm_le hr hrR hR hf N hz).trans_lt hN⟩

/-- The approximant is explicitly a finite double sum of monomials and
is entire `C^ω`, in addition to satisfying the uniform error requirement. -/
theorem exists_entire_polynomial_approximation {f : ℂ × ℂ → ℂ} {r R ε : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hε : 0 < ε)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R ×ˢ closedBall 0 R)) :
    ∃ (N : ℕ) (a : ℕ → ℕ → ℂ) (P : ℂ × ℂ → ℂ),
      (∀ z, P z = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, a i j * z.1 ^ i * z.2 ^ j) ∧
      ContDiff ℂ ω P ∧ ∀ z ∈ closedBall (0 : ℂ) r ×ˢ closedBall 0 r, ‖P z - f z‖ < ε := by
  obtain ⟨N, hN⟩ := exists_cauchyPolynomial_approximation hr hrR hε hf
  let hR : 0 < R := lt_of_le_of_lt hr hrR
  let u := boundaryValues hf.continuousOn
  exact ⟨N, cauchyCoefficient R hR u, cauchyPolynomial R hR u N,
    fun _ => rfl, cauchyPolynomial_contDiff R hR u N, hN⟩

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscApproximation
