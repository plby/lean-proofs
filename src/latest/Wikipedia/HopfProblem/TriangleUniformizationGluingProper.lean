import Wikipedia.HopfProblem.TriangleUniformizationGluingProperFold
import Wikipedia.HopfProblem.TriangleUniformizationGluingQuotient
import Wikipedia.HopfProblem.SpecialPeriodsTriangleCuspCompactification
import Wikipedia.HopfProblem.RiemannSphere
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# Properness and the actual quotient homeomorphism

Local properness of the supplied half-triangle map gives global
properness of the descended map on the existing triangle quotient.
For signed half-plane data, its proved bijectivity then gives an actual
quotient homeomorphism to `ℂ`, and hence a homeomorphism of the actual
one-point compactifications. No global properness or homeomorphism is
an input field.
-/

noncomputable section

open Set UpperHalfPlane
open scoped Topology OnePoint

namespace Wikipedia.HopfProblem.TriangleUniformizationGluing

open SpecialPeriods SpecialPeriods.Triangle

namespace BoundaryMap

variable (D : BoundaryMap)

/-- Quotient preimages are precisely images of the closed Ford preimages. -/
theorem quotientMap_preimage_eq_image_ford (K : Set ℂ) :
    D.quotientMap ⁻¹' K =
      triangleOrbitProjection '' (fordRegion ∩ D.foldedFordMap ⁻¹' K) := by
  ext q
  constructor
  · intro hq
    exact ⟨fordRepresentative q, ⟨(fordRepresentative q).property, hq⟩,
      fordRepresentative_projection q⟩
  · rintro ⟨z, ⟨hz, hzK⟩, rfl⟩
    change D.quotientMap (triangleOrbitProjection z) ∈ K
    rw [D.quotientMap_projection z hz]
    exact hzK

/-- Global properness follows from properness on the supplied half-triangle. -/
theorem quotientMap_isProperMap
    (hlocal : IsProperMap (fun z : halfFordRegion => D.toFun z)) :
    IsProperMap D.quotientMap := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨D.quotientMap_continuous, ?_⟩
  intro K hK
  rw [D.quotientMap_preimage_eq_image_ford K]
  exact (D.foldedFordMap_compact_preimage hlocal K hK).image
    triangleOrbitProjection_continuous

end BoundaryMap

namespace SignedHalfPlaneMap

variable (D : SignedHalfPlaneMap)

/-- A matching actual homeomorphism onto the closed signed half-plane
discharges the only local properness hypothesis. The inclusion into
`ℂ` is proper because the signed half-plane is closed. -/
theorem local_isProperMap_of_homeomorph
    (e : halfFordRegion ≃ₜ {w : ℂ // 0 ≤ D.orientation * w.im})
    (he : ∀ z : halfFordRegion, (e z : ℂ) = D.toFun z) :
    IsProperMap (fun z : halfFordRegion => D.toFun z) := by
  have hclosed : IsClosed {w : ℂ | 0 ≤ D.orientation * w.im} :=
    isClosed_le continuous_const (continuous_const.mul Complex.continuous_im)
  have h := hclosed.isProperMap_subtypeVal.comp e.isProperMap
  change IsProperMap (fun z : halfFordRegion => (e z : ℂ)) at h
  simpa only [he] using h

variable (hlocal : IsProperMap (fun z : halfFordRegion => D.toFun z))

include hlocal

theorem quotientMap_isProperMap : IsProperMap D.quotientMap :=
  D.toBoundaryMap.quotientMap_isProperMap hlocal

/-- The actual quotient topology is homeomorphic to the complex plane. -/
def quotientHomeomorph : TriangleOrbitSpace ≃ₜ ℂ :=
  D.quotientEquiv.toHomeomorphOfContinuousClosed D.quotientMap_continuous
    (D.quotientMap_isProperMap hlocal).isClosedMap

@[simp] theorem quotientHomeomorph_apply (q : TriangleOrbitSpace) :
    D.quotientHomeomorph hlocal q = D.quotientMap q := rfl

theorem quotientHomeomorph_projection (z : ℍ) (hz : z ∈ fordRegion) :
    D.quotientHomeomorph hlocal (triangleOrbitProjection z) = D.foldedFordMap z :=
  D.toBoundaryMap.quotientMap_projection z hz

/-- Extend to the already constructed cusp compactification and the
standard topological Riemann sphere. -/
def compactifiedHomeomorph : TriangleCompactifiedOrbitSpace ≃ₜ RiemannSphere :=
  (D.quotientHomeomorph hlocal).onePointCongr

@[simp] theorem compactifiedHomeomorph_cusp :
    D.compactifiedHomeomorph hlocal triangleCuspPoint = (∞ : RiemannSphere) := rfl

@[simp] theorem compactifiedHomeomorph_openInclusion (q : TriangleOrbitSpace) :
    D.compactifiedHomeomorph hlocal (triangleOpenInclusion q) =
      (D.quotientMap q : RiemannSphere) := rfl

theorem compactifiedHomeomorph_projection (z : ℍ) (hz : z ∈ fordRegion) :
    D.compactifiedHomeomorph hlocal (triangleOpenInclusion (triangleOrbitProjection z)) =
      (D.foldedFordMap z : RiemannSphere) := by
  rw [D.compactifiedHomeomorph_openInclusion hlocal]
  exact congrArg (fun w : ℂ => (w : RiemannSphere))
    (D.toBoundaryMap.quotientMap_projection z hz)

theorem compactifiedHomeomorph_eq_infty_iff (q : TriangleCompactifiedOrbitSpace) :
    D.compactifiedHomeomorph hlocal q = (∞ : RiemannSphere) ↔ q = triangleCuspPoint := by
  constructor
  · intro hq
    apply (D.compactifiedHomeomorph hlocal).injective
    rw [hq, D.compactifiedHomeomorph_cusp hlocal]
  · rintro rfl
    exact D.compactifiedHomeomorph_cusp hlocal

end SignedHalfPlaneMap
end Wikipedia.HopfProblem.TriangleUniformizationGluing
