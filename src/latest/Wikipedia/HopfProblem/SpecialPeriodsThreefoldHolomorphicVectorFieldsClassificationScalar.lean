import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalGeneratorCusp
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorUniqueness

/-!
# Scalar consequences for holomorphic vector fields on the special threefold

The actual special period and its constructed homogeneous generator give
vanishing of cusp-regular homogeneous coefficients.  The generator has
the proved elliptic orders two and one and a simple pole at the cusp.
An invariant cusp-regular holomorphic coefficient is constant, by
subtracting the value of its analytic cusp germ and applying compact
triangle-quotient vanishing.
-/

noncomputable section

open Filter UpperHalfPlane
open scoped Topology ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicVectorFields.Classification

/-- A homogeneous coefficient for the actual special period vanishes
if it is holomorphic on the upper half-plane and regular at the cusp. -/
theorem homogeneous_eq_zero_of_cuspRegular {ν : ℍ → ℂ}
    (hν : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ν)
    (hcov : MuGenerator.Homogeneous specialTauHalfPlane ν)
    (hc : MuTorsor.CuspRegular ν) : ν = 0 := by
  exact MuTorsor.homogeneous_eq_zero_of_cuspRegular
    specialTauHalfPlane_holomorphic specialTauHalfPlane_covariant hν hcov.1 hcov.2 hc
    Canonical.GlobalGenerator.generator_holomorphic
    Canonical.GlobalGenerator.generator_homogeneous.1
    Canonical.GlobalGenerator.generator_homogeneous.2
    Canonical.GlobalGenerator.generator_eq_zero_iff_orbits
    Canonical.GlobalGenerator.generator_order_centerOne
    Canonical.GlobalGenerator.generator_order_centerTwo
    ⟨Canonical.GlobalGenerator.cuspUnit,
      Canonical.GlobalGenerator.cuspUnit_analyticAt,
      Canonical.GlobalGenerator.cuspUnit_zero_ne_zero,
      Canonical.GlobalGenerator.generator_cusp_eventually⟩

/-- The same vanishing statement with the literal scalar equations for
the two source generators. -/
theorem homogeneous_eq_zero_of_generator_laws {ν : ℍ → ℂ}
    (hν : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ν)
    (h₁ : ∀ z : ℍ, ν (Triangle.generatorOneSL • z) = -ν z / specialTau z)
    (h₂ : ∀ z : ℍ, ν (Triangle.generatorTwoSL • z) = ν z / specialTau z)
    (hc : MuTorsor.CuspRegular ν) : ν = 0 := by
  apply homogeneous_eq_zero_of_cuspRegular hν ?_ hc
  constructor
  · intro z
    simpa only [specialTauHalfPlane_coe] using h₁ z
  · intro z
    simpa only [specialTauHalfPlane_coe] using h₂ z

/-- Every holomorphic function invariant under the full actual triangle
group and regular at its cusp is constant. -/
theorem invariant_eq_const_of_cuspRegular {h : ℍ → ℂ}
    (hh : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω h)
    (hinv : ∀ g : TriangleGroup, ∀ z : ℍ,
      h (triangleGeometricRepresentation g z) = h z)
    (hc : MuTorsor.CuspRegular h) : ∃ c : ℂ, ∀ z : ℍ, h z = c := by
  obtain ⟨g, hg, he⟩ := hc
  have hzero : (fun z : ℍ => h z - g 0) = 0 := by
    apply MuTorsor.invariant_eq_zero_of_eventually_cusp
      (g := fun q : ℂ => g q - g 0) (hh.sub contMDiff_const)
    · intro γ z
      rw [hinv γ z]
    · exact hg.sub analyticAt_const
    · exact sub_self _
    · filter_upwards [he] with z hz
      rw [hz]
  refine ⟨g 0, fun z => ?_⟩
  exact sub_eq_zero.mp (congrFun hzero z)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicVectorFields.Classification
