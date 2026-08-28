import Wikipedia.HopfProblem.SpecialPeriodsExistence
import Wikipedia.HopfProblem.SpecialPeriodsGlobalTauUniqueness

/-!
# Unconditional uniqueness of the special modular period

The already constructed normalized sphere equivalence supplies a genuine
upper-half-plane-valued modular lift. It is exactly the first coordinate
of the actual admissible period map. Its modular equation and the two
original generator laws determine it uniquely.
-/

noncomputable section

open Filter Function Metric Set UpperHalfPlane
open scoped Topology ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods

open Triangle

attribute [local instance] triangleCompactifiedChartedSpace

/-- The actual first period as a map to the genuine upper half-plane. -/
def specialTauHalfPlane : ℍ → ℍ :=
  TriangleSource.tauOfSphere triangleSphereUniformization triangleSphereUniformization_cusp
    triangleSphereUniformization_centerOne triangleSphereUniformization_centerTwo

@[simp] theorem specialTauHalfPlane_coe (z : ℍ) :
    (specialTauHalfPlane z : ℂ) = specialTau z :=
  (Construction.periodMapOfSphere_tau triangleSphereUniformization
    triangleSphereUniformization_cusp triangleSphereUniformization_centerOne
    triangleSphereUniformization_centerTwo z).symm

theorem specialTauHalfPlane_holomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω specialTauHalfPlane :=
  TriangleSource.tauOfSphere_holomorphic triangleSphereUniformization
    triangleSphereUniformization_cusp triangleSphereUniformization_centerOne
    triangleSphereUniformization_centerTwo

theorem specialTauHalfPlane_covariant : TauCovariant specialTauHalfPlane :=
  TriangleSource.tauOfSphere_covariant triangleSphereUniformization
    triangleSphereUniformization_cusp triangleSphereUniformization_centerOne
    triangleSphereUniformization_centerTwo

theorem specialTauHalfPlane_modular (z : ℍ) :
    modularJ (specialTauHalfPlane z) = 1728 * specialSourceCoordinate z :=
  TriangleSource.tauOfSphere_modular triangleSphereUniformization
    triangleSphereUniformization_cusp triangleSphereUniformization_centerOne
    triangleSphereUniformization_centerTwo z

@[simp] theorem specialTauHalfPlane_centerOne : specialTauHalfPlane centerOne = rhoPoint :=
  TriangleSource.tauOfSphere_centerOne triangleSphereUniformization
    triangleSphereUniformization_cusp triangleSphereUniformization_centerOne
    triangleSphereUniformization_centerTwo

@[simp] theorem specialTauHalfPlane_centerTwo :
    specialTauHalfPlane centerTwo = UpperHalfPlane.I :=
  TriangleSource.tauOfSphere_centerTwo triangleSphereUniformization
    triangleSphereUniformization_cusp triangleSphereUniformization_centerOne
    triangleSphereUniformization_centerTwo

/-- The actual modular cusp parameter is the original source parameter
times an analytic nonvanishing unit; no cusp germ is an input. -/
theorem specialTauHalfPlane_cusp_unit :
    ∃ u : ℂ → ℂ, AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
      ∀ᶠ z in atImInfty,
        Periodic.qParam 1 (specialTauHalfPlane z : ℂ) = cuspQ z * u (cuspQ z) := by
  obtain ⟨r, hr, u, hu, hu0, hq⟩ := TriangleSource.tauOfSphere_cusp_unit
    triangleSphereUniformization triangleSphereUniformization_cusp
    triangleSphereUniformization_centerOne triangleSphereUniformization_centerTwo
  have ht := cuspQ_tendsto_atImInfty.mono_right nhdsWithin_le_nhds
  have he : ∀ᶠ z in atImInfty, ‖cuspQ z‖ < r := by
    simpa only [mem_ball, dist_zero_right] using ht.eventually (ball_mem_nhds (0 : ℂ) hr)
  refine ⟨u, hu 0 (mem_ball_self hr), hu0, ?_⟩
  filter_upwards [he] with z hz
  exact hq z hz

/-- Uniqueness for the actual source coordinate. Only the properties of
the competing map occur as hypotheses. -/
theorem specialTauHalfPlane_unique {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ)
    (hJ : ∀ z : ℍ, modularJ (τ z) = 1728 * specialSourceCoordinate z)
    (hcov : TauCovariant τ) : τ = specialTauHalfPlane := by
  exact global_tau_unique hτ specialTauHalfPlane_holomorphic
    (fun z => (hJ z).trans (specialTauHalfPlane_modular z).symm)
    hcov specialTauHalfPlane_covariant

/-- The actual modular period exists uniquely with the original two
generator equations and actual modular source equation. -/
theorem exists_unique_specialTauHalfPlane :
    ∃! τ : ℍ → ℍ,
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ ∧ TauCovariant τ ∧
      ∀ z : ℍ, modularJ (τ z) = 1728 * specialSourceCoordinate z := by
  exact ⟨specialTauHalfPlane, ⟨specialTauHalfPlane_holomorphic,
    specialTauHalfPlane_covariant, specialTauHalfPlane_modular⟩,
    fun τ hτ => specialTauHalfPlane_unique hτ.1 hτ.2.2 hτ.2.1⟩

/-- The scalar formulation has the same uniqueness assertion: positivity
is used to form the genuine holomorphic competing upper-half-plane map. -/
theorem specialTau_unique {τ : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hpos : ∀ z : ℍ, 0 < (τ z).im)
    (hJ : ∀ z : ℍ, modularJ (ofComplex (τ z)) = 1728 * specialSourceCoordinate z)
    (h₁ : ∀ z : ℍ, τ (generatorOneSL • z) = (τ z - 1) / τ z)
    (h₂ : ∀ z : ℍ, τ (generatorTwoSL • z) = -1 / τ z) : τ = specialTau := by
  let τH : ℍ → ℍ := fun z => ofComplex (τ z)
  have hcoe (z : ℍ) : (τH z : ℂ) = τ z := by
    exact congrArg UpperHalfPlane.coe (ofComplex_apply_of_im_pos (hpos z))
  have hτH : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τH := by
    intro z
    exact (contMDiffAt_ofComplex (hpos z)).comp z (hτ z)
  have hcov : TauCovariant τH := by
    constructor
    · intro z
      simpa only [hcoe] using h₁ z
    · intro z
      simpa only [hcoe] using h₂ z
  have he : τH = specialTauHalfPlane := specialTauHalfPlane_unique hτH hJ hcov
  funext z
  rw [← hcoe, he, specialTauHalfPlane_coe]

end Wikipedia.HopfProblem.SpecialPeriods
