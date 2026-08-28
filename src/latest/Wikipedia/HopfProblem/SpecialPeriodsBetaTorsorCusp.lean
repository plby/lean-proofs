import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorCuspCoordinates

/-!
# The actual cusp extension and bound for beta plus tau

The reciprocal finite quotient coordinate is an analytic function of the
genuine source cusp parameter.  Composing an analytic finite-coordinate
extension with this function gives an actual analytic `q`-extension.  The
proved escape of the finite projection also gives the limit and a uniform
bound as the imaginary part tends to infinity.  No growth condition or
cusp descent is assumed in these conclusions.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.BetaTorsor

open MuTorsor.CuspCoordinates

attribute [local instance] triangleCompactifiedChartedSpace

variable (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
  TriangleCompactifiedOrbitSpace RiemannSphere ω)

/-- The actual extension in the source cusp coordinate, obtained by
composing with the genuine reciprocal coordinate change. -/
def qExtension (B : ℂ → ℂ) (q : ℂ) : ℂ := B (t π q)

variable (hπ : π triangleCuspPoint = (∞ : RiemannSphere))

include hπ

theorem qExtension_zero (B : ℂ → ℂ) : qExtension π B 0 = B 0 := by
  rw [qExtension, t_zero π hπ]

theorem qExtension_analyticAt_zero {B : ℂ → ℂ} (hB : AnalyticAt ℂ B 0) :
    AnalyticAt ℂ (qExtension π B) 0 := by
  have ht : AnalyticAt ℂ B (t π 0) := by
    rw [t_zero π hπ]
    exact hB
  exact ht.comp (t_analyticAt_zero π hπ)

/-- The finite-coordinate cusp formula holds in the true source parameter
throughout a sufficiently high cusp region. -/
theorem cusp_formula_eventually_q {β : ℍ → ℂ} {τ : ℍ → ℍ} {B : ℂ → ℂ} {R : ℝ}
    (hformula : ∀ z ∈ Triangle.horodisc Triangle.width,
      R < ‖finiteProjection π z‖ → β z + (τ z : ℂ) = B (finiteProjection π z)⁻¹) :
    ∀ᶠ z in atImInfty, β z + (τ z : ℂ) = qExtension π B (Triangle.cuspQ z) := by
  filter_upwards [eventually_mem_horodisc Triangle.width,
    eventually_lt_norm_finiteProjection π hπ R,
    t_cuspQ_eq_inv_finiteProjection π hπ] with z hz hRz ht
  rw [hformula z hz hRz]
  change B (finiteProjection π z)⁻¹ = B (t π (Triangle.cuspQ z))
  rw [ht]

/-- **Actual analytic cusp extension.** An analytic formula in the
reciprocal finite quotient coordinate produces an analytic function of the
original exponential cusp parameter, with the same value at the cusp. -/
theorem analytic_cusp_formula_to_q_extension
    {β : ℍ → ℂ} {τ : ℍ → ℍ} {B : ℂ → ℂ} {R : ℝ}
    (hB : AnalyticAt ℂ B 0)
    (hformula : ∀ z ∈ Triangle.horodisc Triangle.width,
      R < ‖finiteProjection π z‖ → β z + (τ z : ℂ) = B (finiteProjection π z)⁻¹) :
    ∃ C : ℂ → ℂ, AnalyticAt ℂ C 0 ∧ C 0 = B 0 ∧
      ∃ Y : ℝ, ∀ z : ℍ, Y < z.im → β z + (τ z : ℂ) = C (Triangle.cuspQ z) := by
  refine ⟨qExtension π B, qExtension_analyticAt_zero π hπ hB,
    qExtension_zero π hπ B, ?_⟩
  obtain ⟨Y, hY⟩ := (UpperHalfPlane.atImInfty_mem _).mp
    (cusp_formula_eventually_q π hπ hformula)
  exact ⟨Y, fun z hz => hY z hz.le⟩

/-- The actual finite-coordinate escape makes beta plus tau converge to
the analytic extension's value at the added cusp. -/
theorem tendsto_of_analytic_cusp_formula
    {β : ℍ → ℂ} {τ : ℍ → ℍ} {B : ℂ → ℂ} {R : ℝ}
    (hB : AnalyticAt ℂ B 0)
    (hformula : ∀ z ∈ Triangle.horodisc Triangle.width,
      R < ‖finiteProjection π z‖ → β z + (τ z : ℂ) = B (finiteProjection π z)⁻¹) :
    Tendsto (fun z : ℍ => β z + (τ z : ℂ)) atImInfty (𝓝 (B 0)) := by
  have hlim : Tendsto (fun z : ℍ => B (finiteProjection π z)⁻¹)
      atImInfty (𝓝 (B 0)) :=
    hB.continuousAt.tendsto.comp
      ((finiteProjection_inv_tendsto_zero π hπ).mono_right nhdsWithin_le_nhds)
  apply hlim.congr'
  filter_upwards [eventually_mem_horodisc Triangle.width,
    eventually_lt_norm_finiteProjection π hπ R] with z hz hRz
  exact (hformula z hz hRz).symm

/-- **The required high-cusp bound.** It follows from the analytic cusp
formula and the actual finite projection's escape, uniformly in the real
part of the upper-half-plane coordinate. -/
theorem bounded_of_analytic_cusp_formula
    {β : ℍ → ℂ} {τ : ℍ → ℍ} {B : ℂ → ℂ} {R : ℝ}
    (hB : AnalyticAt ℂ B 0)
    (hformula : ∀ z ∈ Triangle.horodisc Triangle.width,
      R < ‖finiteProjection π z‖ → β z + (τ z : ℂ) = B (finiteProjection π z)⁻¹) :
    ∃ Y M : ℝ, ∀ z : ℍ, Y < z.im → ‖β z + (τ z : ℂ)‖ ≤ M := by
  have hlim := (tendsto_of_analytic_cusp_formula π hπ hB hformula).norm
  have hbound : ∀ᶠ z in atImInfty, ‖β z + (τ z : ℂ)‖ < ‖B 0‖ + 1 :=
    hlim.eventually (Iio_mem_nhds (lt_add_one ‖B 0‖))
  obtain ⟨Y, hY⟩ := (UpperHalfPlane.atImInfty_mem _).mp hbound
  exact ⟨Y, ‖B 0‖ + 1, fun z hz => (hY z hz.le).le⟩

end Wikipedia.HopfProblem.SpecialPeriods.BetaTorsor
