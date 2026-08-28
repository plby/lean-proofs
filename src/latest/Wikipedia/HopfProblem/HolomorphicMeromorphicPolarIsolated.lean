import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Basic

/-!
# Isolated common zeros from an actual analytic Bézout relation

An actual relation `A*p + C*q = z₁^n*u`, with `u(0) ≠ 0`, forces every
nearby common zero of `p,q` onto the first-coordinate-zero axis. A nonzero
analytic germ of `q` on that axis then forces the second coordinate to be
zero. No coherence or meromorphic-sheaf conclusion is assumed.
-/

open Set Filter Topology

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarIsolated

/-- A nonzero one-variable analytic germ has no nearby zero except possibly
the center itself. -/
theorem eventually_zero_imp_eq_zero {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hf₀ : ¬f =ᶠ[𝓝 (0 : ℂ)] 0) :
    ∀ᶠ w in 𝓝 (0 : ℂ), f w = 0 → w = 0 := by
  have hne := hf.eventually_eq_zero_or_eventually_ne_zero.resolve_left hf₀
  rw [eventually_nhdsWithin_iff] at hne
  filter_upwards [hne] with w hw
  intro hwzero
  by_contra hw₀
  exact hw hw₀ hwzero

/-- An actual coordinate-power Bézout relation and a nonzero axis germ
isolate the common zeros at the origin. Only `q,u` need analyticity for
this implication. The zero-exponent case is included. -/
theorem eventually_common_zero_eq_zero {p q A C u : ℂ × ℂ → ℂ} {n : ℕ}
    (hq : AnalyticAt ℂ q 0) (hu : AnalyticAt ℂ u 0) (hu₀ : u 0 ≠ 0)
    (hrel : (fun z ↦ A z * p z + C z * q z) =ᶠ[𝓝 (0 : ℂ × ℂ)]
      (fun z ↦ z.1 ^ n * u z))
    (hqaxis : ¬(fun w : ℂ ↦ q (0, w)) =ᶠ[𝓝 (0 : ℂ)] 0) :
    ∀ᶠ z in 𝓝 (0 : ℂ × ℂ), p z = 0 → q z = 0 → z = 0 := by
  have haxis_analytic : AnalyticAt ℂ (fun w : ℂ ↦ q (0, w)) 0 :=
    hq.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  have haxis := eventually_zero_imp_eq_zero haxis_analytic hqaxis
  have haxis_near := (continuous_snd.tendsto (0 : ℂ × ℂ)).eventually haxis
  filter_upwards [hrel, hu.continuousAt.eventually_ne hu₀, haxis_near]
    with z hrelz huz haxisz
  intro hpz hqz
  have hprod : z.1 ^ n * u z = 0 := by
    simpa only [hpz, hqz, mul_zero, add_zero] using hrelz.symm
  have hx : z.1 = 0 :=
    eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hprod).resolve_right huz)
  have hzpair : z = (0, z.2) := Prod.ext hx rfl
  have hqaxiszero : q (0, z.2) = 0 := by
    rw [← hzpair]
    exact hqz
  exact Prod.ext hx (haxisz hqaxiszero)

/-- In a punctured neighborhood at least one of the two actual functions
is nonzero. -/
theorem eventually_no_common_zero {p q A C u : ℂ × ℂ → ℂ} {n : ℕ}
    (hq : AnalyticAt ℂ q 0) (hu : AnalyticAt ℂ u 0) (hu₀ : u 0 ≠ 0)
    (hrel : (fun z ↦ A z * p z + C z * q z) =ᶠ[𝓝 (0 : ℂ × ℂ)]
      (fun z ↦ z.1 ^ n * u z))
    (hqaxis : ¬(fun w : ℂ ↦ q (0, w)) =ᶠ[𝓝 (0 : ℂ)] 0) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ × ℂ), p z ≠ 0 ∨ q z ≠ 0 := by
  have h : ∀ᶠ z in 𝓝[≠] (0 : ℂ × ℂ), p z = 0 → q z = 0 → z = 0 :=
    (eventually_common_zero_eq_zero hq hu hu₀ hrel hqaxis).filter_mono nhdsWithin_le_nhds
  filter_upwards [h, self_mem_nhdsWithin] with z hz hz₀
  by_cases hpz : p z = 0
  · exact Or.inr (fun hqz ↦ hz₀ (hz hpz hqz))
  · exact Or.inl hpz

/-- The common-zero isolation holds on one actual positive-radius ball,
uniformly for all points in that ball. -/
theorem exists_ball_common_zero_eq_zero {p q A C u : ℂ × ℂ → ℂ} {n : ℕ}
    (hq : AnalyticAt ℂ q 0) (hu : AnalyticAt ℂ u 0) (hu₀ : u 0 ≠ 0)
    (hrel : (fun z ↦ A z * p z + C z * q z) =ᶠ[𝓝 (0 : ℂ × ℂ)]
      (fun z ↦ z.1 ^ n * u z))
    (hqaxis : ¬(fun w : ℂ ↦ q (0, w)) =ᶠ[𝓝 (0 : ℂ)] 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ Metric.ball (0 : ℂ × ℂ) ε,
      p z = 0 → q z = 0 → z = 0 :=
  Metric.eventually_nhds_iff_ball.mp
    (eventually_common_zero_eq_zero hq hu hu₀ hrel hqaxis)

end Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarIsolated
