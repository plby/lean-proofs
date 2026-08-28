import Wikipedia.HopfProblem.SpecialPeriodsTriangleSourceTau
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsor
import Wikipedia.HopfProblem.SpecialPeriodsBetaTorsor

/-!
# Constructing all three global special period functions

The only geometric input is a genuine biholomorphism from the constructed
compact triangle quotient to the Riemann sphere, with its three prescribed
marked values.  The modular lifting construction produces tau; the actual
affine Cousin constructions then produce mu and beta.  Each cusp expression
comes with an analytic germ in the actual exponential cusp coordinate.

The discriminant is not assumed negative here.  A subsequent construction
proves its global upper bound and makes one constant imaginary beta shift.
-/

noncomputable section

open Filter Set UpperHalfPlane
open scoped Topology ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Construction

attribute [local instance] triangleCompactifiedChartedSpace

/-- Genuine global functions and their analytic cusp germs, before the
constant shift needed for admissibility.  Existence is proved below from
the supplied normalized quotient biholomorphism. -/
structure PeriodFunctions where
  data : BetaTorsor.Data
  beta : ℍ → ℂ
  beta_holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω beta
  beta_generators : data.GeneratorLaws beta
  tau_cusp : ∃ h : ℂ → ℂ, AnalyticAt ℂ h 0 ∧
    ∀ᶠ z in atImInfty,
      (data.tau z : ℂ) = (z : ℂ) / Triangle.width + h (Triangle.cuspQ z)
  mu_cusp : MuTorsor.CuspRegular data.mu
  beta_cusp : MuTorsor.CuspRegular (fun z => beta z + (data.tau z : ℂ))

private theorem eventually_norm_cuspQ_lt {r : ℝ} (hr : 0 < r) :
    ∀ᶠ z in atImInfty, ‖Triangle.cuspQ z‖ < r := by
  have ht := Triangle.cuspQ_tendsto_atImInfty.mono_right nhdsWithin_le_nhds
  simpa only [Metric.mem_ball, dist_zero_right] using
    ht.eventually (Metric.ball_mem_nhds (0 : ℂ) hr)

variable (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
  TriangleCompactifiedOrbitSpace RiemannSphere ω)
  (hπ : π triangleCuspPoint = (∞ : RiemannSphere))
  (h₀ : π (triangleOpenInclusion triangleOrbitCenterOne) = ((0 : ℂ) : RiemannSphere))
  (h₁ : π (triangleOpenInclusion triangleOrbitCenterTwo) = ((1 : ℂ) : RiemannSphere))

/-- All three holomorphic period functions and their genuine cusp germs
are constructed from the actual normalized sphere equivalence.  No period
function, local torsor section, overlap cocycle, or vanishing theorem is
assumed as additional input. -/
theorem exists_periodFunctions_of_sphere :
    ∃ F : PeriodFunctions, F.data.tau = TriangleSource.tauOfSphere π hπ h₀ h₁ := by
  let τ := TriangleSource.tauOfSphere π hπ h₀ h₁
  have hτa := TriangleSource.tauOfSphere_holomorphic π hπ h₀ h₁
  have hτc := TriangleSource.tauOfSphere_covariant π hπ h₀ h₁
  have hJ := TriangleSource.tauOfSphere_modular π hπ h₀ h₁
  obtain ⟨r, hr, _, h, hh, hτformula⟩ :=
    TriangleSource.tauOfSphere_cusp π hπ h₀ h₁
  have hh0 : AnalyticAt ℂ h 0 := hh 0 (Metric.mem_ball_self hr)
  have hτformula' : ∀ᶠ z in atImInfty,
      (τ z : ℂ) = (z : ℂ) / Triangle.width + h (Triangle.cuspQ z) := by
    filter_upwards [eventually_norm_cuspQ_lt hr] with z hz
    exact hτformula z hz
  obtain ⟨ru, hru, u, hu, hu0, hqu⟩ :=
    TriangleSource.tauOfSphere_cusp_unit π hπ h₀ h₁
  have hu0a : AnalyticAt ℂ u 0 := hu 0 (Metric.mem_ball_self hru)
  have hqu' : ∀ᶠ z in atImInfty,
      Function.Periodic.qParam 1 (τ z) = Triangle.cuspQ z * u (Triangle.cuspQ z) := by
    filter_upwards [eventually_norm_cuspQ_lt hru] with z hz
    exact hqu z hz
  obtain ⟨μ, hμ, _⟩ := MuTorsor.exists_unique_solution π hπ h₀ h₁
    hτc hτa hJ hu0a hu0 hqu'
  let D : BetaTorsor.Data := {
    tau := τ
    mu := μ
    tau_holomorphic := hτa
    mu_holomorphic := hμ.holomorphic
    tau_covariant := hτc
    mu_one := hμ.generatorOne
    mu_two := hμ.generatorTwo }
  obtain ⟨β, b, hβ, hb, _, Y, hβformula⟩ := D.exists_solution_with_cusp_extension π hπ
  have hβformula' : ∀ᶠ z in atImInfty,
      β z + (D.tau z : ℂ) = b (Triangle.cuspQ z) := by
    apply (UpperHalfPlane.atImInfty_mem _).mpr
    exact ⟨Y + 1, fun z hz => hβformula z (by linarith)⟩
  exact ⟨{
    data := D
    beta := β
    beta_holomorphic := hβ.holomorphic
    beta_generators := hβ.generators
    tau_cusp := ⟨h, hh0, hτformula'⟩
    mu_cusp := hμ.cuspRegular
    beta_cusp := ⟨b, hb, hβformula'⟩ }, rfl⟩

/-- A choice of the three constructed genuine global period functions. -/
def periodFunctionsOfSphere : PeriodFunctions :=
  (exists_periodFunctions_of_sphere π hπ h₀ h₁).choose

theorem periodFunctionsOfSphere_tau :
    (periodFunctionsOfSphere π hπ h₀ h₁).data.tau =
      TriangleSource.tauOfSphere π hπ h₀ h₁ :=
  (exists_periodFunctions_of_sphere π hπ h₀ h₁).choose_spec

end Wikipedia.HopfProblem.SpecialPeriods.Construction
