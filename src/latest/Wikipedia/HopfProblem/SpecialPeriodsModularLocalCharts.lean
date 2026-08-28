import Wikipedia.HopfProblem.SpecialPeriodsModularLocalChartsRoots
import Wikipedia.HopfProblem.SpecialPeriodsModularLocalChartsInverse

/-!
# Genuine analytic power charts

For a complex analytic function with a zero of finite positive order `m`,
we construct an open partial homeomorphism with analytic forward and inverse
maps on their full domains, centered at the zero, in which the function is
exactly the `m`th power.  The chart can be chosen inside any prescribed
neighborhood of the original point.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace Wikipedia.HopfProblem.SpecialPeriods

/-- The local analytic normal form at a zero of order `m`, on an actual
open chart inside any prescribed neighborhood. -/
theorem exists_analytic_power_chart_in {F : ℂ → ℂ} {a : ℂ} {m : ℕ} {U : Set ℂ}
    (hF : AnalyticAt ℂ F a) (horder : analyticOrderAt F a = m) (hm : 0 < m)
    (hU : U ∈ 𝓝 a) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      a ∈ e.source ∧ e a = 0 ∧ e.source ⊆ U ∧
      AnalyticOnNhd ℂ e e.source ∧ AnalyticOnNhd ℂ e.symm e.target ∧
      ∀ w ∈ e.source, F w = e w ^ m := by
  obtain ⟨h, hh, hha, hdh, hpower⟩ := exists_analytic_power_coordinate hF horder hm
  obtain ⟨e₀, hae₀, he₀, hea, hei⟩ := exists_analytic_openPartialHomeomorph hh hdh
  have hboth : ∀ᶠ w in 𝓝 a, F w = h w ^ m ∧ w ∈ U := hpower.and hU
  obtain ⟨V, hV, hVo, haV⟩ := eventually_nhds_iff.mp hboth
  let e : OpenPartialHomeomorph ℂ ℂ := e₀.restrOpen V hVo
  refine ⟨e, ⟨hae₀, haV⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact (he₀ a).trans hha
  · intro w hw
    exact (hV w hw.2).2
  · intro w hw
    exact hea w hw.1
  · intro w hw
    exact hei w hw.1
  · intro w hw
    exact (hV w hw.2).1.trans (congrArg (· ^ m) (he₀ w).symm)

/-- A zero of order `m` admits a biholomorphic coordinate in which the
function is exactly the `m`th power. -/
theorem exists_analytic_power_chart {F : ℂ → ℂ} {a : ℂ} {m : ℕ}
    (hF : AnalyticAt ℂ F a) (horder : analyticOrderAt F a = m) (hm : 0 < m) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      a ∈ e.source ∧ e a = 0 ∧
      AnalyticOnNhd ℂ e e.source ∧ AnalyticOnNhd ℂ e.symm e.target ∧
      ∀ w ∈ e.source, F w = e w ^ m := by
  obtain ⟨e, ha, he, _, hf, hi, hp⟩ :=
    exists_analytic_power_chart_in hF horder hm (Filter.univ_mem : Set.univ ∈ 𝓝 a)
  exact ⟨e, ha, he, hf, hi, hp⟩

/-- The inverse side of a power chart has the same exact normal form. -/
theorem power_chart_inverse_identity (e : OpenPartialHomeomorph ℂ ℂ)
    {F : ℂ → ℂ} {m : ℕ} (hp : ∀ w ∈ e.source, F w = e w ^ m) :
    ∀ w ∈ e.target, F (e.symm w) = w ^ m := by
  intro w hw
  rw [hp _ (e.map_target hw), e.right_inv hw]

end Wikipedia.HopfProblem.SpecialPeriods
