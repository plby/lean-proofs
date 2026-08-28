import Wikipedia.HopfProblem.SpecialPeriodsBetaTorsorOverlaps
import Wikipedia.HopfProblem.SpecialPeriodsBetaTorsorGluing

/-!
# Global beta from the actual local sections

The regular zero seeds, elliptic finite averages, and cusp seed minus tau
have already been extended to the actual saturated quotient patches.  Their
holomorphic differences have already been descended to the finite sphere
coordinate.  Applying the proved additive Cousin solver now constructs a
global holomorphic beta with the two required generator laws and an actual
normalized holomorphic extension of beta plus tau at the distinguished cusp.

Only actual tau and mu data and a supplied normalized sphere uniformization
are inputs.  Local beta sections, overlap cocycles, and cohomology vanishing
are not hypotheses of the existence theorem.
-/

noncomputable section

open Set Metric Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.BetaTorsor.Data

open MuTorsor

attribute [local instance] triangleOrbitChartedSpace triangleCompactifiedChartedSpace

variable (D : Data)

/-- The two actual inhomogeneous beta equations from Definition 3.1. -/
def GeneratorLaws (β : ℍ → ℂ) : Prop :=
  (∀ z : ℍ, β (Triangle.generatorOneSL • z) = β z + phiOne D.tau D.mu z) ∧
  (∀ z : ℍ, β (Triangle.generatorTwoSL • z) = β z + phiTwo D.tau D.mu z)

/-- The generator equations propagate to every actual triangle word using
the constructed cocycle, rather than an assumed consistency condition. -/
theorem GeneratorLaws.all_words {β : ℍ → ℂ} (hβ : D.GeneratorLaws β) :
    ∀ g : TriangleGroup, ∀ z : ℍ,
      β (triangleGeometricRepresentation g z) = β z + D.shift g z :=
  triangleAdditiveShift_covariance_of_generators
    (phiOne D.tau D.mu) (phiTwo D.tau D.mu)
    (phiOne_sum_range D.tau_covariant D.mu_one)
    (phiTwo_sum_range D.tau_covariant D.mu_two) β hβ.1 hβ.2

theorem generatorLaws_of_all_words {β : ℍ → ℂ}
    (hβ : ∀ g : TriangleGroup, ∀ z : ℍ,
      β (triangleGeometricRepresentation g z) = β z + D.shift g z) : D.GeneratorLaws β := by
  constructor
  · intro z
    simpa only [triangleGeometricRepresentation_generator₁_apply, D.shift_generator₁] using
      hβ triangleGenerator₁ z
  · intro z
    simpa only [triangleGeometricRepresentation_generator₂_apply, D.shift_generator₂] using
      hβ triangleGenerator₂ z

theorem GeneratorLaws.sub_invariant {β γ : ℍ → ℂ}
    (hβ : D.GeneratorLaws β) (hγ : D.GeneratorLaws γ) (g : TriangleGroup) (z : ℍ) :
    β (triangleGeometricRepresentation g z) - γ (triangleGeometricRepresentation g z) =
      β z - γ z := by
  rw [hβ.all_words D g z, hγ.all_words D g z]
  ring

theorem GeneratorLaws.add_const {β : ℍ → ℂ} (hβ : D.GeneratorLaws β) (c : ℂ) :
    D.GeneratorLaws (fun z => β z + c) := by
  constructor
  · intro z
    dsimp only
    rw [hβ.1 z]
    ring
  · intro z
    dsimp only
    rw [hβ.2 z]
    ring

variable (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
  TriangleCompactifiedOrbitSpace RiemannSphere ω)
  (hπ : π triangleCuspPoint = (∞ : RiemannSphere))

include hπ in
/-- **Global beta existence.** The actual local sections and their actual
descended differences give a global holomorphic function.  Its cusp extension
is normalized to zero at the added point; other constants are handled below. -/
theorem exists_global_beta :
    ∃ R : ℝ, 0 < R ∧ ∃ (β : ℍ → ℂ) (B : ℂ → ℂ),
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω β ∧ D.GeneratorLaws β ∧
      AnalyticOnNhd ℂ B (ball 0 R⁻¹) ∧ B 0 = 0 ∧
      ∀ z ∈ Triangle.horodisc Triangle.width, R < ‖finiteProjection π z‖ →
        β z + (D.tau z : ℂ) = B (finiteProjection π z)⁻¹ := by
  obtain ⟨R, hR, hRU⟩ := Cover.finitePatch_cusp_contains_exterior π hπ
  obtain ⟨β, B, hβ, hB, hB0, hwords, hcusp⟩ :=
    BetaTorsorGluing.exists_glued_beta_with_cusp
      (finiteProjection_holomorphic π hπ) (finiteProjection_surjective π hπ)
      (fun i => (Cover.finitePatch π i).isOpen) (Cover.exists_finitePatch π)
      (D.localSection_holomorphic_finite π hπ)
      (D.overlapCocycle_analytic π hπ) (D.localSection_difference π hπ)
      Cover.cuspIndex hR hRU
      (fun g z => triangleGeometricRepresentation g z) D.shift (finiteProjection_invariant π)
      (D.localSection_additive_finite π hπ)
      (fun z => (D.tau z : ℂ)) (Triangle.horodisc Triangle.width) D.localSection_cusp
  exact ⟨R, hR, β, B, hβ, D.generatorLaws_of_all_words hwords, hB, hB0, hcusp⟩

end Wikipedia.HopfProblem.SpecialPeriods.BetaTorsor.Data
