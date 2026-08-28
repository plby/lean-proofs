import Wikipedia.HopfProblem.DegreeCollapseSevenPrimitiveMeridian
import Wikipedia.HopfProblem.DegreeCollapsePrimitiveIntegerCoordinate

/-!
# Actual surgery on a primitive class removes precisely its free summand

The proved original exterior isomorphism identifies the new inclusion
with a genuine quotient map from the old half. Its kernel is the
integer multiples of the original attaching class. The specified
primitive integer coordinate identifies the actual new H3 with its
kernel, retaining the quotient on every original exterior class.
-/

noncomputable section

open Function AddSubgroup
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
namespace FramedAttachingProduct.UnitSurgery.ExteriorTwist

open NoExoticSixSphere GLOrthonormalization
open SingularMayerVietoris SphereHomology

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] [SimplyConnectedSpace M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hA : A.radius = 2) (T : TimeData A)
  {B : Type} [TopologicalSpace B] (C : TimeCollar T.time B)
  [Subsingleton (SingularHomology B 2)] [Subsingleton (SingularHomology B 3)]
  [Subsingleton (SingularHomology B 4)]
  (σ : SingularHomology (OldPositiveHalf A T) 3 →ₗ[ℤ] ℤ)
  (hσ : σ (singularHomologyMap (halfBoundaryPair A hA T).attachingSphere 3
    (unitSphereTopClass 2)) = 1)

def primitiveSurgeryMap : SingularHomology (OldPositiveHalf A T) 3 →+
    SingularHomology (PositiveHalf A hA T) 3 :=
  (singularHomologyMap (halfNewInclusion A hA T) 3).toAddMonoidHom.comp
    (LinearEquiv.ofBijective (singularHomologyMap (halfOldInclusion A hA T) 3)
      (primitive_halfOldInclusion_bijective A hA T C σ hσ)).symm.toAddMonoidHom

theorem primitiveSurgeryMap_surjective : Surjective (primitiveSurgeryMap A hA T C σ hσ) :=
  (halfNewInclusion_surjective A hA T).comp
    (LinearEquiv.ofBijective (singularHomologyMap (halfOldInclusion A hA T) 3)
      (primitive_halfOldInclusion_bijective A hA T C σ hσ)).symm.surjective

theorem primitiveSurgeryMap_oldInclusion (x : SingularHomology (HalfExterior A hA T) 3) :
    primitiveSurgeryMap A hA T C σ hσ (singularHomologyMap (halfOldInclusion A hA T) 3 x) =
      singularHomologyMap (halfNewInclusion A hA T) 3 x := by
  let e := LinearEquiv.ofBijective (singularHomologyMap (halfOldInclusion A hA T) 3)
    (primitive_halfOldInclusion_bijective A hA T C σ hσ)
  change singularHomologyMap (halfNewInclusion A hA T) 3 (e.symm (e x)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem primitiveSurgeryMap_kernel :
    (primitiveSurgeryMap A hA T C σ hσ).ker =
      zmultiples (singularHomologyMap (halfBoundaryPair A hA T).attachingSphere 3
        (unitSphereTopClass 2)) := by
  let e := LinearEquiv.ofBijective (singularHomologyMap (halfOldInclusion A hA T) 3)
    (primitive_halfOldInclusion_bijective A hA T C σ hσ)
  let v := spherePole 3
  let ε := halfSectionClass A hA T v
  have he : e ε = singularHomologyMap (halfBoundaryPair A hA T).attachingSphere 3
      (unitSphereTopClass 2) := halfOldInclusion_section A hA T v (unitSphereTopClass 2)
  have hk : (singularHomologyMap (halfNewInclusion A hA T) 3).toAddMonoidHom.ker =
      zmultiples ε := by
    change (LinearMap.ker (singularHomologyMap (halfNewInclusion A hA T) 3)).toAddSubgroup = _
    rw [halfNew_kernel_span A hA T v, CyclicSurgeryIndex.span_toAddSubgroup]
  ext x
  constructor
  · intro hx
    have hx' : e.symm x ∈ zmultiples ε := by
      rw [← hk]
      exact hx
    obtain ⟨k, hkx⟩ := mem_zmultiples_iff.mp hx'
    refine mem_zmultiples_iff.mpr ⟨k, ?_⟩
    have h := congrArg e hkx
    rw [map_zsmul, he, LinearEquiv.apply_symm_apply] at h
    exact h
  · intro hx
    obtain ⟨k, hkx⟩ := mem_zmultiples_iff.mp hx
    have hx' : e.symm x ∈ zmultiples ε := by
      refine mem_zmultiples_iff.mpr ⟨k, e.injective ?_⟩
      rw [map_zsmul, he, LinearEquiv.apply_symm_apply]
      exact hkx
    rw [← hk] at hx'
    exact hx'

def primitiveThirdHomologyEquiv :
    SingularHomology (PositiveHalf A hA T) 3 ≃+ σ.toAddMonoidHom.ker := by
  let c := singularHomologyMap (halfBoundaryPair A hA T).attachingSphere 3 (unitSphereTopClass 2)
  let r := primitiveSurgeryMap A hA T C σ hσ
  let p := IntegerSplit.projection σ.toAddMonoidHom c hσ
  have hk : r.ker = p.ker := (primitiveSurgeryMap_kernel A hA T C σ hσ).trans
    (IntegerSplit.projection_kernel σ.toAddMonoidHom c hσ).symm
  exact (QuotientAddGroup.quotientKerEquivOfSurjective r
    (primitiveSurgeryMap_surjective A hA T C σ hσ)).symm.trans
      ((QuotientAddGroup.quotientAddEquivOfEq hk).trans
        (QuotientAddGroup.quotientKerEquivOfSurjective p
          (IntegerSplit.projection_surjective σ.toAddMonoidHom c hσ)))

theorem primitiveThirdHomologyEquiv_surgeryMap
    (x : SingularHomology (OldPositiveHalf A T) 3) :
    primitiveThirdHomologyEquiv A hA T C σ hσ (primitiveSurgeryMap A hA T C σ hσ x) =
      IntegerSplit.projection σ.toAddMonoidHom
        (singularHomologyMap (halfBoundaryPair A hA T).attachingSphere 3
          (unitSphereTopClass 2)) hσ x := by
  let r := primitiveSurgeryMap A hA T C σ hσ
  let p := IntegerSplit.projection σ.toAddMonoidHom
    (singularHomologyMap (halfBoundaryPair A hA T).attachingSphere 3 (unitSphereTopClass 2)) hσ
  let er := QuotientAddGroup.quotientKerEquivOfSurjective r
    (primitiveSurgeryMap_surjective A hA T C σ hσ)
  let ep := QuotientAddGroup.quotientKerEquivOfSurjective p
    (IntegerSplit.projection_surjective σ.toAddMonoidHom _ hσ)
  have hk : r.ker = p.ker := (primitiveSurgeryMap_kernel A hA T C σ hσ).trans
    (IntegerSplit.projection_kernel σ.toAddMonoidHom _ hσ).symm
  have hx : er (QuotientAddGroup.mk x) = r x := rfl
  change ep (QuotientAddGroup.quotientAddEquivOfEq hk (er.symm (r x))) = p x
  rw [← hx, er.symm_apply_apply, QuotientAddGroup.quotientAddEquivOfEq_mk]
  rfl

include C hσ in
theorem primitive_new_third_finite [Finite σ.toAddMonoidHom.ker] :
    Finite (SingularHomology (PositiveHalf A hA T) 3) :=
  Finite.of_injective _ (primitiveThirdHomologyEquiv A hA T C σ hσ).injective

include C hσ in
theorem primitive_new_third_card :
    Nat.card (SingularHomology (PositiveHalf A hA T) 3) = Nat.card σ.toAddMonoidHom.ker :=
  Nat.card_congr (primitiveThirdHomologyEquiv A hA T C σ hσ).toEquiv

include C hσ in
theorem primitive_new_third_two (h2 : ∀ x : σ.toAddMonoidHom.ker, (2 : ℤ) • x = 0)
    (x : SingularHomology (PositiveHalf A hA T) 3) : (2 : ℤ) • x = 0 := by
  apply (primitiveThirdHomologyEquiv A hA T C σ hσ).injective
  rw [map_zsmul, h2, map_zero]

end FramedAttachingProduct.UnitSurgery.ExteriorTwist
end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
