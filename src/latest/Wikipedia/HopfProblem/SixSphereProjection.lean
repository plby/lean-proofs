import Wikipedia.HopfProblem.UnconditionalSphereRecognition
import Wikipedia.HopfProblem.ThreefoldProjectionNullhomotopy
import Mathlib.Topology.Compactification.OnePoint.Sphere

/-!
# The unconditional holomorphic, null-homotopic projection from S⁶ to S²

The map is the original threefold projection transported through its proved
smooth identification with the standard six-sphere. It is holomorphic for
the transported complex atlas, whose underlying real smooth structure agrees
with the sphere's original stereographic atlas. It is surjective and
null-homotopic. No sphere-recognition or homotopy-group hypothesis remains.

The primary target is the standard Riemann sphere. The final declarations
also express the map between literal Euclidean unit spheres, transporting
the Riemann sphere's complex atlas through its standard sphere homeomorphism.
-/

noncomputable section

open scoped ContDiff Manifold ContinuousMap

namespace Wikipedia.HopfProblem.SixSphereProjection

open SpecialPeriods

local notation "Model" => ℂ × ComplexPlane₂
local notation "IC" => 𝓘(ℂ, Model)
local notation "IR" => 𝓘(ℝ, Model)

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

/-- The complex atlas from the proved smooth identification, with no additional input. -/
@[instance_reducible] def complexChartedSpace : ChartedSpace Model SixSphere :=
  SixSphereComplexTransport.complexChartedSpace
    UnconditionalSphereRecognition.smoothIdentification

theorem complex_isManifold :
    letI := complexChartedSpace
    IsManifold IC ω SixSphere :=
  SixSphereComplexTransport.complex_isManifold
    UnconditionalSphereRecognition.smoothIdentification

/-- This atlas retains the sphere's original smooth structure. -/
theorem original_smooth_structure_agrees :
    letI := complexChartedSpace
    ContMDiff IR (𝓡 6) ∞ (id : SixSphere → SixSphere) ∧
      ContMDiff (𝓡 6) IR ∞ (id : SixSphere → SixSphere) :=
  SixSphereComplexTransport.original_smooth_structure_agrees
    UnconditionalSphereRecognition.smoothIdentification

/-- The original projection, using the proved diffeomorphism to identify its source. -/
def projection : C(SixSphere, RiemannSphere) :=
  Threefold.ProjectionHomotopy.projectionMap.comp
    (UnconditionalSphereRecognition.smoothIdentification.symm.toHomeomorph :
      C(SixSphere, Threefold.Space))

/-- The map to the standard Riemann sphere is complex analytic. -/
theorem projection_holomorphic :
    letI := complexChartedSpace
    ContMDiff IC 𝓘(ℂ) ω projection := by
  let := complexChartedSpace
  exact Threefold.projectionSphere_holomorphic.comp
    UnconditionalSphereRecognition.biholomorph.symm.contMDiff

theorem projection_surjective : Function.Surjective projection :=
  Threefold.projectionSphere_surjective.comp
    UnconditionalSphereRecognition.smoothIdentification.symm.surjective

theorem projection_nullhomotopic : projection.Nullhomotopic :=
  Threefold.ProjectionHomotopy.projection_nullhomotopic.comp_left _

/-- The literal unit two-sphere in real Euclidean three-space. -/
abbrev TwoSphere := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- The usual identification of the Riemann sphere with the Euclidean two-sphere. -/
def baseHomeomorph : RiemannSphere ≃ₜ TwoSphere :=
  onePointEquivSphereOfFinrankEq (by simp)

@[instance_reducible] def baseComplexChartedSpace : ChartedSpace ℂ TwoSphere :=
  ManifoldAtlasTransport.chartedSpace (H := ℂ) baseHomeomorph

theorem base_complex_isManifold :
    letI := baseComplexChartedSpace
    IsManifold 𝓘(ℂ) ω TwoSphere :=
  ManifoldAtlasTransport.isManifold 𝓘(ℂ) ω baseHomeomorph

def baseBiholomorph :
    letI := baseComplexChartedSpace
    RiemannSphere ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ TwoSphere :=
  ManifoldAtlasTransport.diffeomorph 𝓘(ℂ) ω baseHomeomorph

/-- The same projection, now between the literal Euclidean spheres. -/
def sphereProjection : C(SixSphere, TwoSphere) :=
  (baseHomeomorph : C(RiemannSphere, TwoSphere)).comp projection

/-- Unconditionally, the constructed map S⁶ → S² is complex analytic. -/
theorem sphere_projection_holomorphic :
    letI := complexChartedSpace
    letI := baseComplexChartedSpace
    ContMDiff IC 𝓘(ℂ) ω sphereProjection := by
  let := complexChartedSpace
  let := baseComplexChartedSpace
  exact baseBiholomorph.contMDiff.comp projection_holomorphic

theorem sphere_projection_surjective : Function.Surjective sphereProjection :=
  baseHomeomorph.surjective.comp projection_surjective

theorem sphere_projection_nullhomotopic : sphereProjection.Nullhomotopic :=
  projection_nullhomotopic.comp_right (baseHomeomorph : C(RiemannSphere, TwoSphere))

end Wikipedia.HopfProblem.SixSphereProjection
