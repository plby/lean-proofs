import Wikipedia.NoExoticSixSphere.SphereFourTubeNativeMeridian
import Wikipedia.NoExoticSixSphere.ManifoldFourDiskOperator
import Wikipedia.NoExoticSixSphere.SphereDiskExtension

/-!
# The original meridian operator extends over its actual normal disk

The original ambient normal columns and the derivative of the actual
normal disk give an injective operator at every point of the four-space.
Restriction to the closed unit disk supplies an exact extension of its
original unit-sphere boundary operator.
-/

noncomputable section

open Function Set ContinuousMap
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SphereFourTube

open GLOrthonormalization Stiefel DiskBoundary Wikipedia.HopfProblem.DegreeCollapse

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M]
  (Φ : PartialDiffeomorph ((𝓡 3).prod (𝓡 4)) (𝓡 7) (Sphere 3 × Vector 4) M ∞)
  (hΦ : Φ.source = univ) (e : EuclideanEmbedding 7 M)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)

def normalDiskOperatorMap (s : Sphere 3) :
    C(Vector 4, Monomorphism.Space e.ambientDimension ((e.ambientDimension - 7) + 4)) := by
  have hg := contMDiff_normalDisk Φ hΦ s
  refine ⟨fun v ↦ ⟨e.normalFourDiskOperator a (normalDisk Φ s) v,
    e.normalFourDiskOperator_injective a (normalDisk Φ s) v
      (hg.mdifferentiableAt (by simp)) (normalDisk_mfderiv_injective Φ hΦ s v)⟩, ?_⟩
  apply Continuous.subtype_mk
  apply continuous_iff_continuousAt.mpr
  intro v
  exact (e.contDiffAt_normalFourDiskOperator a (normalDisk Φ s) v hg.contMDiffAt).continuousAt

def normalDiskBoundaryOperator (s : Sphere 3) :
    C(Sphere 3, Monomorphism.Space e.ambientDimension ((e.ambientDimension - 7) + 4)) :=
  (normalDiskOperatorMap Φ hΦ e a s).comp ⟨Subtype.val, continuous_subtype_val⟩

theorem normalDiskBoundaryOperator_value (s v : Sphere 3) :
    (normalDiskBoundaryOperator Φ hΦ e a s v).val =
      e.normalFourDiskOperator a (normalDisk Φ s) v.val := rfl

theorem normalDiskBoundaryOperator_extends (s : Sphere 3) :
    Extends (normalDiskBoundaryOperator Φ hΦ e a s) :=
  ⟨(normalDiskOperatorMap Φ hΦ e a s).comp
      (⟨Subtype.val, continuous_subtype_val⟩ : C(DiskCylinder.Disk (E := Vector 4), Vector 4)),
    fun _ ↦ rfl⟩

end NoExoticSixSphere.SphereFourTube
