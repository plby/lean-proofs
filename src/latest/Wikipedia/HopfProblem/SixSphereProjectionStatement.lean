import Wikipedia.HopfProblem.SixSphereProjection

/-!
# An independent statement of the holomorphic sphere-projection result

The same map is surjective, complex analytic, and null-homotopic. Its source
atlas has the standard complex three-dimensional coordinate model and retains
the six-sphere's original real smooth structure. The proof uses the actual
transported threefold projection; the statement does not expose its construction.
-/

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SixSphereProjection

/-- There are complex atlases on the standard spheres and a single surjective
holomorphic null-homotopic map between them. The source atlas is compatible
with the original smooth structure. -/
theorem holomorphic_nullhomotopic_surjection :
    ∃ c₆ : ChartedSpace (EuclideanSpace ℂ (Fin 3)) SixSphere,
      ∃ c₂ : ChartedSpace ℂ TwoSphere,
        letI := c₆
        letI := c₂
        IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin 3)) ω SixSphere ∧
          IsManifold 𝓘(ℂ) ω TwoSphere ∧
          ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin 3)) (𝓡 6) ∞ (id : SixSphere → SixSphere) ∧
          ContMDiff (𝓡 6) 𝓘(ℝ, EuclideanSpace ℂ (Fin 3)) ∞ (id : SixSphere → SixSphere) ∧
          ∃ p : C(SixSphere, TwoSphere),
            Function.Surjective p ∧
              ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin 3)) 𝓘(ℂ) ω p ∧ p.Nullhomotopic := by
  let := complexChartedSpace
  let := complex_isManifold
  let := baseComplexChartedSpace
  let e := SixSphereComplexAtlas.modelEquiv
  let c := SpecialPeriods.Threefold.ModelChange.chartedSpace e SixSphere
  have hC := SpecialPeriods.Threefold.ModelChange.isManifold e SixSphere ω
  have hR := original_smooth_structure_agrees
  let D := SpecialPeriods.Threefold.ModelChange.diffeomorph e SixSphere ∞
  have hD : (D : SixSphere → SixSphere) = id := rfl
  have hDs : (D.symm : SixSphere → SixSphere) = id := rfl
  refine ⟨c, baseComplexChartedSpace, hC, base_complex_isManifold, ?_, ?_,
    sphereProjection, sphere_projection_surjective, ?_, sphere_projection_nullhomotopic⟩
  · have hf := complexContMDiff_restrict_real D.symm.contMDiff
    rw [hDs] at hf
    exact hR.1.comp hf
  · exact (hD ▸ complexContMDiff_restrict_real D.contMDiff).comp hR.2
  · let := c
    exact sphere_projection_holomorphic.comp
      (SpecialPeriods.Threefold.ModelChange.diffeomorph e SixSphere ω).symm.contMDiff

end Wikipedia.HopfProblem.SixSphereProjection
