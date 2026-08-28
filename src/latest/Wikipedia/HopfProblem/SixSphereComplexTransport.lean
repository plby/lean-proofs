import Wikipedia.HopfProblem.SixSphereComplexTransportAtlas
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldRealManifold
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# The complex-atlas transport step for the standard six-sphere

The sphere here is literally the unit sphere in Euclidean real seven-space,
with its existing topology and Mathlib's stereographic real smooth atlas.
Given an actual smooth diffeomorphism from the constructed threefold to this
sphere, its complex atlas transports to the sphere. The identity between
the resulting underlying real manifold and the original smooth sphere is
smooth in both directions.

Every result in this file explicitly requires that diffeomorphism as data.
No existence, classification, or sphere-recognition theorem is asserted.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem

/-- The standard unit six-sphere, not a synonym for the constructed threefold. -/
abbrev SixSphere := Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1

namespace SixSphereComplexTransport

open SpecialPeriods

local notation "Model" => ℂ × ComplexPlane₂
local notation "IC" => 𝓘(ℂ, Model)
local notation "IR" => 𝓘(ℝ, Model)

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold
  Threefold.space_isSmoothRealManifold

/-- The still-required recognition data uses the original real atlases
on both the constructed manifold and the standard sphere. -/
abbrev SmoothIdentification := Threefold.Space ≃ₘ⟮IR, 𝓡 6⟯ SixSphere

/-- The actual complex atlas transported using the supplied diffeomorphism. -/
@[instance_reducible] def complexChartedSpace (d : SmoothIdentification) :
    ChartedSpace Model SixSphere :=
  ManifoldAtlasTransport.chartedSpace (H := Model) d.toHomeomorph

theorem complex_isManifold (d : SmoothIdentification) :
    letI := complexChartedSpace d
    IsManifold IC ω SixSphere :=
  ManifoldAtlasTransport.isManifold IC ω d.toHomeomorph

/-- Transport makes the same supplied map holomorphic with holomorphic inverse. -/
def biholomorph (d : SmoothIdentification) :
    letI := complexChartedSpace d
    Threefold.Space ≃ₘ^ω⟮IC, IC⟯ SixSphere :=
  ManifoldAtlasTransport.diffeomorph IC ω d.toHomeomorph

@[simp] theorem biholomorph_apply (d : SmoothIdentification) (x : Threefold.Space) :
    letI := complexChartedSpace d
    biholomorph d x = d x := rfl

@[simp] theorem biholomorph_symm_apply (d : SmoothIdentification) (x : SixSphere) :
    letI := complexChartedSpace d
    (biholomorph d).symm x = d.symm x := rfl

/-- Restriction of scalars in the transported complex atlas, without
any change to its charts, gives a real analytic manifold. -/
theorem underlying_isRealAnalyticManifold (d : SmoothIdentification) :
    letI := complexChartedSpace d
    IsManifold IR ω SixSphere := by
  let := complexChartedSpace d
  let := complex_isManifold d
  exact complexManifold_isRealManifold SixSphere ω

theorem underlying_isSmoothRealManifold (d : SmoothIdentification) :
    letI := complexChartedSpace d
    IsManifold IR ∞ SixSphere := by
  let := complexChartedSpace d
  let := underlying_isRealAnalyticManifold d
  infer_instance

/-- An identity-on-points diffeomorphism from the transported underlying
real structure to the sphere's original stereographic smooth structure. -/
def smoothIdentity (d : SmoothIdentification) :
    letI := complexChartedSpace d
    SixSphere ≃ₘ⟮IR, 𝓡 6⟯ SixSphere := by
  letI := complexChartedSpace d
  exact (ManifoldAtlasTransport.diffeomorph IR ∞ d.toHomeomorph).symm.trans d

@[simp] theorem smoothIdentity_apply (d : SmoothIdentification) (x : SixSphere) :
    letI := complexChartedSpace d
    smoothIdentity d x = x :=
  d.apply_symm_apply x

@[simp] theorem smoothIdentity_symm_apply (d : SmoothIdentification) (x : SixSphere) :
    letI := complexChartedSpace d
    (smoothIdentity d).symm x = x :=
  d.apply_symm_apply x

/-- The two real smooth structures agree via the literal identity map.
This compares with the original sphere atlas, not a second transported atlas. -/
theorem original_smooth_structure_agrees (d : SmoothIdentification) :
    letI := complexChartedSpace d
    ContMDiff IR (𝓡 6) ∞ (id : SixSphere → SixSphere) ∧
      ContMDiff (𝓡 6) IR ∞ (id : SixSphere → SixSphere) := by
  let := complexChartedSpace d
  have hf : (smoothIdentity d : SixSphere → SixSphere) = id :=
    funext (smoothIdentity_apply d)
  have hg : ((smoothIdentity d).symm : SixSphere → SixSphere) = id :=
    funext (smoothIdentity_symm_apply d)
  exact ⟨hf ▸ (smoothIdentity d).contMDiff, hg ▸ (smoothIdentity d).symm.contMDiff⟩

/-- A ready-to-apply transport wrapper. The parameter `d` is indispensable:
this theorem does not construct a diffeomorphism to the standard sphere. -/
theorem exists_compatible_complex_atlas (d : SmoothIdentification) :
    ∃ c : ChartedSpace Model SixSphere,
      letI := c
      IsManifold IC ω SixSphere ∧
        ContMDiff IR (𝓡 6) ∞ (id : SixSphere → SixSphere) ∧
        ContMDiff (𝓡 6) IR ∞ (id : SixSphere → SixSphere) :=
  ⟨complexChartedSpace d, complex_isManifold d, original_smooth_structure_agrees d⟩

end SixSphereComplexTransport

end Wikipedia.HopfProblem
