import Wikipedia.HopfProblem.SpecialPeriodsUniquenessTau
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsor

/-!
# Unconditional uniqueness of the bounded special middle period

The actual normalized sphere map, the actual modular period, and its
constructed analytic cusp unit discharge every existence input of the
global affine torsor theorem. The conclusion uses the original scalar
generator equations and boundedness at imaginary infinity.
-/

noncomputable section

open UpperHalfPlane
open scoped Topology ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods

open Triangle

attribute [local instance] triangleCompactifiedChartedSpace

theorem specialMu_bounded : IsBoundedAtImInfty specialMu :=
  specialMu_cusp.bounded

/-- The middle coordinate of the actual admissible period map solves
the genuine affine torsor for the actual upper-half-plane period. -/
theorem specialMu_isSolution : MuTorsor.IsSolution specialTauHalfPlane specialMu := by
  refine ⟨specialMu_holomorphic, ?_, ?_, specialMu_cusp⟩
  · intro z
    simpa only [specialTauHalfPlane_coe] using (specialPeriods_generator₁ z).2.1
  · intro z
    simpa only [specialTauHalfPlane_coe] using (specialPeriods_generator₂ z).2.1

theorem specialMu_bounded_solution :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω specialMu ∧
      (∀ z : ℍ, specialMu (generatorOneSL • z) = (1 - specialMu z) / specialTau z) ∧
      (∀ z : ℍ, specialMu (generatorTwoSL • z) = 1 + specialMu z / specialTau z) ∧
      IsBoundedAtImInfty specialMu :=
  ⟨specialMu_holomorphic, fun z => (specialPeriods_generator₁ z).2.1,
    fun z => (specialPeriods_generator₂ z).2.1, specialMu_bounded⟩

/-- The literal bounded scalar affine problem has a unique solution;
no uniformization, modular lift, or cusp unit is supplied as an input. -/
theorem exists_unique_specialMu :
    ∃! μ : ℍ → ℂ,
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω μ ∧
      (∀ z : ℍ, μ (generatorOneSL • z) = (1 - μ z) / specialTau z) ∧
      (∀ z : ℍ, μ (generatorTwoSL • z) = 1 + μ z / specialTau z) ∧
      IsBoundedAtImInfty μ := by
  obtain ⟨u, hu, hu0, hq⟩ := specialTauHalfPlane_cusp_unit
  have h := MuTorsor.exists_unique_bounded_solution triangleSphereUniformization
    triangleSphereUniformization_cusp triangleSphereUniformization_centerOne
    triangleSphereUniformization_centerTwo specialTauHalfPlane_covariant
    specialTauHalfPlane_holomorphic specialTauHalfPlane_modular hu hu0 hq
  simpa only [specialTauHalfPlane_coe] using h

/-- Every bounded holomorphic middle period satisfying the original
two affine laws is the actual middle coordinate of `specialPeriodMap`. -/
theorem specialMu_unique {μ : ℍ → ℂ}
    (hμ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω μ)
    (h₁ : ∀ z : ℍ, μ (generatorOneSL • z) = (1 - μ z) / specialTau z)
    (h₂ : ∀ z : ℍ, μ (generatorTwoSL • z) = 1 + μ z / specialTau z)
    (hb : IsBoundedAtImInfty μ) : μ = specialMu :=
  exists_unique_specialMu.unique ⟨hμ, h₁, h₂, hb⟩ specialMu_bounded_solution

theorem specialMu_solution_iff (μ : ℍ → ℂ) :
    (ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω μ ∧
      (∀ z : ℍ, μ (generatorOneSL • z) = (1 - μ z) / specialTau z) ∧
      (∀ z : ℍ, μ (generatorTwoSL • z) = 1 + μ z / specialTau z) ∧
      IsBoundedAtImInfty μ) ↔ μ = specialMu := by
  constructor
  · rintro ⟨hμ, h₁, h₂, hb⟩
    exact specialMu_unique hμ h₁ h₂ hb
  · rintro rfl
    exact specialMu_bounded_solution

end Wikipedia.HopfProblem.SpecialPeriods
