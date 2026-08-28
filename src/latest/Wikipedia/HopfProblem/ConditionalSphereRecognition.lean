import Wikipedia.HopfProblem.SphereRecognitionHypotheses
import Wikipedia.HopfProblem.ThreefoldHomologySphere
import Wikipedia.HopfProblem.SixSphereComplexTransport

/-!
# Route I: the sphere conclusion from one explicit recognition hypothesis

All geometric and homological inputs about the original constructed threefold
are proved by imported unconditional results. The only additional hypothesis
is the general `SphereRecognition.SmoothHomologySixSphereRecognition`.

From that one argument, this file obtains an actual smooth diffeomorphism to
the literal standard six-sphere, a complex atlas on that sphere, a genuine
biholomorphism from the constructed threefold, and agreement of the underlying
real smooth structure with the original stereographic one.

No recognition assumption is added to the environment. These conditional
theorems do not claim an unconditional solution or supply the explicit gluing
identification being pursued independently in Route II.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.ConditionalSphereRecognition

open SphereRecognition SpecialPeriods

local notation "Model" => ℂ × ComplexPlane₂
local notation "IC" => 𝓘(ℂ, Model)
local notation "IR" => 𝓘(ℝ, Model)

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold
  Threefold.space_isSmoothRealManifold Threefold.space_compact
  Threefold.space_t2Space Threefold.space_secondCountable Threefold.space_simplyConnected

/-- The homology input of the general recognition statement is already unconditional. -/
theorem threefold_isIntegralHomologySixSphere : IsIntegralHomologySixSphere Threefold.Space :=
  Threefold.HomologySphere.integralHomologySphere

/-- Theorem 8.1's smooth identification, conditional on the single general recognition result. -/
theorem smoothIdentification_nonempty (hRecognition : SmoothHomologySixSphereRecognition) :
    Nonempty SixSphereComplexTransport.SmoothIdentification :=
  hRecognition Model Threefold.Space Threefold.real_dimension
    threefold_isIntegralHomologySixSphere

/-- A chosen actual diffeomorphism, with the only extra premise displayed. -/
def smoothIdentification (hRecognition : SmoothHomologySixSphereRecognition) :
    SixSphereComplexTransport.SmoothIdentification :=
  Classical.choice (smoothIdentification_nonempty hRecognition)

/-- The complex atlas on the actual standard sphere supplied by conditional Route I. -/
@[instance_reducible] def complexChartedSpace
    (hRecognition : SmoothHomologySixSphereRecognition) : ChartedSpace Model SixSphere :=
  SixSphereComplexTransport.complexChartedSpace (smoothIdentification hRecognition)

theorem complex_isManifold (hRecognition : SmoothHomologySixSphereRecognition) :
    letI := complexChartedSpace hRecognition
    IsManifold IC ω SixSphere :=
  SixSphereComplexTransport.complex_isManifold (smoothIdentification hRecognition)

/-- The original construction is genuinely biholomorphic to this complex six-sphere. -/
def biholomorph (hRecognition : SmoothHomologySixSphereRecognition) :
    letI := complexChartedSpace hRecognition
    Threefold.Space ≃ₘ^ω⟮IC, IC⟯ SixSphere :=
  SixSphereComplexTransport.biholomorph (smoothIdentification hRecognition)

@[simp] theorem biholomorph_apply (hRecognition : SmoothHomologySixSphereRecognition)
    (x : Threefold.Space) :
    letI := complexChartedSpace hRecognition
    biholomorph hRecognition x = smoothIdentification hRecognition x := rfl

/-- Compatibility is with the sphere's original smooth atlas, not another transported atlas. -/
theorem original_smooth_structure_agrees (hRecognition : SmoothHomologySixSphereRecognition) :
    letI := complexChartedSpace hRecognition
    ContMDiff IR (𝓡 6) ∞ (id : SixSphere → SixSphere) ∧
      ContMDiff (𝓡 6) IR ∞ (id : SixSphere → SixSphere) :=
  SixSphereComplexTransport.original_smooth_structure_agrees (smoothIdentification hRecognition)

/-- Corollary 1.1 with exactly one external mathematical hypothesis.

The topology and original real smooth structure are those of the literal unit
sphere in Euclidean real seven-space. No hypothesis about the construction's
compactness, simple connectivity, homology, or charts remains in this theorem.
-/
theorem exists_compatible_complex_atlas (hRecognition : SmoothHomologySixSphereRecognition) :
    ∃ c : ChartedSpace Model SixSphere,
      letI := c
      IsManifold IC ω SixSphere ∧
        ContMDiff IR (𝓡 6) ∞ (id : SixSphere → SixSphere) ∧
        ContMDiff (𝓡 6) IR ∞ (id : SixSphere → SixSphere) :=
  SixSphereComplexTransport.exists_compatible_complex_atlas (smoothIdentification hRecognition)

end Wikipedia.HopfProblem.ConditionalSphereRecognition
