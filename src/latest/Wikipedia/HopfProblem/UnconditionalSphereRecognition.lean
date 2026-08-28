import Wikipedia.SmoothSixDPoincare.Diffeomorphism
import Wikipedia.HopfProblem.DegreeCollapseHomotopyEquivalence
import Wikipedia.HopfProblem.SixSphereComplexAtlas
import Wikipedia.HopfProblem.ComplexRealMaps

/-!
# Unconditional complex structures on the standard smooth six-sphere

The constructed threefold is a smooth homotopy six-sphere. Smooth Poincaré
recognition supplies a diffeomorphism for its original real atlas. Transport
then gives a complex analytic atlas on the literal standard six-sphere whose
underlying real smooth structure agrees with its stereographic structure.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem

namespace UnconditionalSphereRecognition

open SpecialPeriods

local notation "Model" => ℂ × ComplexPlane₂

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold
  Threefold.space_isSmoothRealManifold Threefold.space_compact
  Threefold.space_t2Space Threefold.space_secondCountable

/-- The original smooth threefold is diffeomorphic to the standard smooth sphere. -/
theorem smoothIdentification_nonempty : Nonempty SixSphereComplexTransport.SmoothIdentification :=
  Wikipedia.SmoothSixDPoincare.diffeomorphic_sixSphere_of_homotopySixSphere
    Model Threefold.Space Threefold.real_dimension DegreeCollapse.threefoldHomotopyEquiv

def smoothIdentification : SixSphereComplexTransport.SmoothIdentification :=
  Classical.choice smoothIdentification_nonempty

/-- The original threefold is biholomorphic to the transported complex sphere. -/
def biholomorph :
    letI := SixSphereComplexTransport.complexChartedSpace smoothIdentification
    Threefold.Space ≃ₘ^ω⟮𝓘(ℂ, Model), 𝓘(ℂ, Model)⟯ SixSphere :=
  SixSphereComplexTransport.biholomorph smoothIdentification

/-- The complex atlas can use the standard complex three-dimensional coordinate model,
while retaining the sphere's original topology and real smooth structure. -/
theorem exists_compatible_complex_atlas :
    ∃ c : ChartedSpace (EuclideanSpace ℂ (Fin 3)) SixSphere,
      letI := c
      IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin 3)) ω SixSphere ∧
        ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin 3)) (𝓡 6) ∞ (id : SixSphere → SixSphere) ∧
        ContMDiff (𝓡 6) 𝓘(ℝ, EuclideanSpace ℂ (Fin 3)) ∞ (id : SixSphere → SixSphere) := by
  let d := smoothIdentification
  let := SixSphereComplexTransport.complexChartedSpace d
  let := SixSphereComplexTransport.complex_isManifold d
  let e := SixSphereComplexAtlas.modelEquiv
  let atlas := Threefold.ModelChange.chartedSpace e SixSphere
  have hC := Threefold.ModelChange.isManifold e SixSphere ω
  have hR := SixSphereComplexTransport.original_smooth_structure_agrees d
  let D := Threefold.ModelChange.diffeomorph e SixSphere ∞
  have hD : (D : SixSphere → SixSphere) = id := rfl
  have hDs : (D.symm : SixSphere → SixSphere) = id := rfl
  refine ⟨atlas, ?_⟩
  refine ⟨hC, ?_, ?_⟩
  · have hf := complexContMDiff_restrict_real D.symm.contMDiff
    rw [hDs] at hf
    exact hR.1.comp hf
  · exact (hD ▸ complexContMDiff_restrict_real D.contMDiff).comp hR.2

end UnconditionalSphereRecognition

/-- The topological six-sphere admits a complex analytic structure of complex dimension three. -/
theorem hopf_problem :
    ∃ c : ChartedSpace (EuclideanSpace ℂ (Fin 3)) SixSphere,
      letI := c
      IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin 3)) ω SixSphere :=
  SixSphereComplexAtlas.exists_complex_analytic_atlas

/-- The same existence statement at complex differentiability class `C¹`. -/
theorem hopf_problem_c1 :
    ∃ c : ChartedSpace (EuclideanSpace ℂ (Fin 3)) SixSphere,
      letI := c
      IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin 3)) 1 SixSphere :=
  SixSphereComplexAtlas.exists_complex_atlas

/-- The standard smooth six-sphere admits a compatible complex analytic structure. -/
theorem hopf_problem_smooth :
    ∃ c : ChartedSpace (EuclideanSpace ℂ (Fin 3)) SixSphere,
      letI := c
      IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin 3)) ω SixSphere ∧
        ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin 3)) (𝓡 6) ∞ (id : SixSphere → SixSphere) ∧
        ContMDiff (𝓡 6) 𝓘(ℝ, EuclideanSpace ℂ (Fin 3)) ∞ (id : SixSphere → SixSphere) :=
  UnconditionalSphereRecognition.exists_compatible_complex_atlas

end Wikipedia.HopfProblem
