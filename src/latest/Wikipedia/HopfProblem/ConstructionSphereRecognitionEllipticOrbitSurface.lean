import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticOrbitFullProduct

/-!
# The original central-surface factor and the delta-orbit model

The map from the actual central surface to the residual finite affine
three-dimensional quotient is verified on the original finite period cover.
The full cap orbit map is the original full-cap product followed by this
map on its second factor.  No product coordinate or covering is replaced.
-/

noncomputable section

open Topology

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticOrbit

open Elliptic SpecialPeriods EllipticModel EllipticNative EllipticOrbitFlat
open EllipticGamma EllipticFullProduct
open ThreefoldOverlapMappingTorus.Elliptic (affine_pow_order)

variable {j : Kind} (D : Equivariant.Data j)

/-- The original central-surface finite period cover, in its unchanged real coordinates. -/
def surfaceCover : C(RealTorus₄, Surface j D.centralPeriod j.twist (mainTwist_admissible j)) :=
  (fibreSurfaceHomeomorph j D.centralPeriod j.twist (mainTwist_admissible j) :
    C(FibreQuotient j.order (flatTorusAffine j j.twist)
      (affine_pow_order j j.twist j.matrix_fixes_twist), _)).comp
    ⟨fibreProject j.order (flatTorusAffine j j.twist)
      (affine_pow_order j j.twist j.matrix_fixes_twist),
      (fibreProject_isOpenQuotientMap j.order (flatTorusAffine j j.twist)
        (affine_pow_order j j.twist j.matrix_fixes_twist)).continuous⟩

@[simp] theorem surfaceCover_apply (x : RealTorus₄) :
    surfaceCover D x =
      surfaceProjection j D.centralPeriod j.twist (mainTwist_admissible j)
        (flatTorusPeriodHomeomorph D.centralPeriod.val x) := rfl

theorem surfaceCover_isOpenQuotientMap : IsOpenQuotientMap (surfaceCover D) :=
  (fibreSurfaceHomeomorph j D.centralPeriod j.twist
    (mainTwist_admissible j)).isOpenQuotientMap.comp
      (fibreProject_isOpenQuotientMap j.order (flatTorusAffine j j.twist)
        (affine_pow_order j j.twist j.matrix_fixes_twist))

/-- The map on the original central surface, using the actual full product at root zero. -/
def surfaceModelMap : C(Surface j D.centralPeriod j.twist (mainTwist_admissible j), FibreModel j) :=
  ⟨fun y => (fullOrbitMap D ((fillingProductHomeomorph D).symm (discZero, y))).2,
    continuous_snd.comp ((fullOrbitMap D).continuous.comp
      ((fillingProductHomeomorph D).symm.continuous.comp
        (continuous_const.prodMk continuous_id)))⟩

/-- The map forgets precisely delta on the genuine original finite period cover. -/
@[simp] theorem surfaceModelMap_surfaceCover (x : RealTorus₄) :
    surfaceModelMap D (surfaceCover D x) = fibreModelProjection j (dropDelta x) := by
  change (fullOrbitMap D ((fillingProductHomeomorph D).symm
    (discZero, surfaceCover D x))).2 = _
  rw [surfaceCover_apply, fillingProductHomeomorph_symm_surfaceProjection,
    fullOrbitMap_quotient]

/-- This is an open quotient between the original surface and the genuine residual model. -/
theorem surfaceModelMap_isOpenQuotientMap : IsOpenQuotientMap (surfaceModelMap D) := by
  apply IsOpenQuotientMap.of_comp (surfaceCover D).continuous
    (surfaceCover_isOpenQuotientMap D).surjective (surfaceModelMap D).continuous
  have he : surfaceModelMap D ∘ surfaceCover D = fibreModelProjection j ∘ dropDelta :=
    funext (surfaceModelMap_surfaceCover D)
  rw [he]
  exact (fibreModelProjection_isOpenQuotientMap j).comp dropDelta_isOpenQuotientMap

/-- The original full-cap product commutes exactly with its actual circle quotient. -/
theorem fullOrbitMap_originalProduct (x : D.Space j.twist (mainTwist_admissible j)) :
    fullOrbitMap D x =
      ((fillingProductHomeomorph D x).1,
        surfaceModelMap D (fillingProductHomeomorph D x).2) := by
  obtain ⟨⟨s, y⟩, rfl⟩ := D.quotient_surjective j.twist (mainTwist_admissible j) x
  rw [fullOrbitMap_quotient, fillingProductHomeomorph_quotient]
  change (rotate (normalizedGamma j y) s, fibreModelProjection j (dropDelta y)) =
    (rotate (normalizedGamma j y) s, surfaceModelMap D (surfaceCover D y))
  rw [surfaceModelMap_surfaceCover]

/-- Equality of the original continuous maps, including their literal product factors. -/
theorem fullOrbitMap_originalProduct_comp :
    fullOrbitMap D =
      (ContinuousMap.prodMap (ContinuousMap.id Disc) (surfaceModelMap D)).comp
        (fillingProductHomeomorph D : C(_, _)) := by
  ext x
  exact fullOrbitMap_originalProduct D x

end Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticOrbit

