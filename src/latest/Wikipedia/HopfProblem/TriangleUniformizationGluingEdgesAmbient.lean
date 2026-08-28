import Wikipedia.HopfProblem.SpecialPeriodsTriangleActions
import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-!
# The triangle action in ambient complex coordinates

The actual biholomorphic triangle action determines an open partial
homeomorphism of `ℂ`, with both source and target equal to the upper
half-plane.  Its two functions are complex differentiable on their
respective domains.  These maps transport analytic removability while
retaining the concrete group action on every upper-half-plane point.
-/

noncomputable section

open Set UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.TriangleUniformizationGluing

open SpecialPeriods

/-- The actual triangle-group action, expressed in ambient complex coordinates. -/
def triangleAmbientMap (g : TriangleGroup) : OpenPartialHomeomorph ℂ ℂ :=
  (UpperHalfPlane.ofComplex.trans
    (triangleGeometricBiholomorph g).toHomeomorph.toOpenPartialHomeomorph).trans
    UpperHalfPlane.ofComplex.symm

@[simp] theorem triangleAmbientMap_source (g : TriangleGroup) :
    (triangleAmbientMap g).source = UpperHalfPlane.upperHalfPlaneSet := by
  simp [triangleAmbientMap, UpperHalfPlane.ofComplex, UpperHalfPlane.range_coe]

@[simp] theorem triangleAmbientMap_target (g : TriangleGroup) :
    (triangleAmbientMap g).target = UpperHalfPlane.upperHalfPlaneSet := by
  simp [triangleAmbientMap, UpperHalfPlane.ofComplex, UpperHalfPlane.range_coe]

/-- The extension outside the open source uses exactly `ofComplex`. -/
theorem triangleAmbientMap_apply (g : TriangleGroup) (z : ℂ) :
    triangleAmbientMap g z =
      (triangleGeometricRepresentation g (UpperHalfPlane.ofComplex z) : ℂ) := rfl

@[simp] theorem triangleAmbientMap_apply_coe (g : TriangleGroup) (z : ℍ) :
    triangleAmbientMap g (z : ℂ) = (triangleGeometricRepresentation g z : ℂ) := by
  rw [triangleAmbientMap_apply, UpperHalfPlane.ofComplex_apply]

/-- The inverse ambient function is the extension of the inverse group action. -/
theorem triangleAmbientMap_symm_apply (g : TriangleGroup) (z : ℂ) :
    (triangleAmbientMap g).symm z =
      (triangleGeometricRepresentation g⁻¹ (UpperHalfPlane.ofComplex z) : ℂ) := by
  rw [map_inv]
  rfl

@[simp] theorem triangleAmbientMap_symm_apply_coe (g : TriangleGroup) (z : ℍ) :
    (triangleAmbientMap g).symm (z : ℂ) =
      (triangleGeometricRepresentation g⁻¹ z : ℂ) := by
  rw [triangleAmbientMap_symm_apply, UpperHalfPlane.ofComplex_apply]

/-- Inversion of the ambient partial homeomorphism agrees with group inversion. -/
@[simp] theorem triangleAmbientMap_symm (g : TriangleGroup) :
    (triangleAmbientMap g).symm = triangleAmbientMap g⁻¹ := by
  apply OpenPartialHomeomorph.ext
  · intro z
    rw [triangleAmbientMap_symm_apply, triangleAmbientMap_apply]
  · intro z
    simp only [OpenPartialHomeomorph.symm_symm, triangleAmbientMap_apply,
      triangleAmbientMap_symm_apply, inv_inv]
  · simp only [OpenPartialHomeomorph.symm_source, triangleAmbientMap_source,
      triangleAmbientMap_target]

/-- Holomorphicity on the genuine open source comes from the actual manifold action. -/
theorem triangleAmbientMap_differentiableOn (g : TriangleGroup) :
    DifferentiableOn ℂ (triangleAmbientMap g) (triangleAmbientMap g).source := by
  rw [triangleAmbientMap_source]
  exact UpperHalfPlane.mdifferentiable_iff.mp
    (UpperHalfPlane.mdifferentiable_coe.comp
      ((triangleGeometricRepresentation_holomorphic g).mdifferentiable (by simp)))

/-- The actual inverse function is holomorphic on the open target. -/
theorem triangleAmbientMap_symm_differentiableOn (g : TriangleGroup) :
    DifferentiableOn ℂ (triangleAmbientMap g).symm (triangleAmbientMap g).target := by
  simpa only [triangleAmbientMap_source, triangleAmbientMap_target,
    triangleAmbientMap_symm] using triangleAmbientMap_differentiableOn g⁻¹

theorem triangleAmbientMap_mapsTo_upperHalfPlaneSet (g : TriangleGroup) :
    MapsTo (triangleAmbientMap g) UpperHalfPlane.upperHalfPlaneSet
      UpperHalfPlane.upperHalfPlaneSet := by
  simpa only [triangleAmbientMap_source, triangleAmbientMap_target] using
    (triangleAmbientMap g).mapsTo

/-- The ambient image is exactly the upper half-plane, not merely a subset of it. -/
theorem triangleAmbientMap_image_upperHalfPlaneSet (g : TriangleGroup) :
    triangleAmbientMap g '' UpperHalfPlane.upperHalfPlaneSet =
      UpperHalfPlane.upperHalfPlaneSet := by
  simpa only [triangleAmbientMap_source, triangleAmbientMap_target] using
    (triangleAmbientMap g).image_source_eq_target

/-- Ambient images of upper-half-plane sets are the concrete group-action images. -/
theorem triangleAmbientMap_image_coe (g : TriangleGroup) (S : Set ℍ) :
    triangleAmbientMap g '' (((↑) : ℍ → ℂ) '' S) =
      ((↑) : ℍ → ℂ) '' (triangleGeometricRepresentation g '' S) := by
  rw [Set.image_image, Set.image_image]
  apply Set.image_congr
  intro z _
  exact triangleAmbientMap_apply_coe g z

end Wikipedia.HopfProblem.TriangleUniformizationGluing
