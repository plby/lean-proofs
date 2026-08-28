import Wikipedia.HopfProblem.DegreeCollapseSevenExteriorHomology
import Wikipedia.HopfProblem.DegreeCollapseSevenTwistHalfExterior
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Both actual filling halves as quotients of their common exterior homology

The old inclusion kills exactly the original meridian; the new inclusion
kills exactly the original section. Reversal swaps the actual two corner
parameters, with no unspecified orientation or comparison map. The first
isomorphism theorem retains each genuine inclusion on every quotient class.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery.ExteriorTwist

open NoExoticSixSphere GLOrthonormalization
open SingularMayerVietoris
open Wikipedia.SmoothSixDPoincare

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hA : A.radius = 2) (T : TimeData A)

def halfOldInclusion : C(HalfExterior A hA T, OldPositiveHalf A T) :=
  SurgeryExteriorSequence.Seven.inclusion (halfBoundaryPair A hA T)

def halfNewInclusion : C(HalfExterior A hA T, PositiveHalf A hA T) :=
  SurgeryExteriorSequence.Seven.inclusion (halfBoundaryPair A hA T).reverse

theorem halfOldInclusion_val (x : HalfExterior A hA T) :
    (halfOldInclusion A hA T x).val = x.val.val := rfl

theorem halfNewInclusion_val (x : HalfExterior A hA T) :
    (halfNewInclusion A hA T x).val = (closedBoundaryPair A hA).newExterior x.val := rfl

theorem halfOldInclusion_surjective :
    Surjective (singularHomologyMap (halfOldInclusion A hA T) 3) :=
  SurgeryExteriorSequence.Seven.inclusion_surjective (halfBoundaryPair A hA T)

theorem halfNewInclusion_surjective :
    Surjective (singularHomologyMap (halfNewInclusion A hA T) 3) :=
  SurgeryExteriorSequence.Seven.inclusion_surjective (halfBoundaryPair A hA T).reverse

theorem halfMeridian_range_eq_old_kernel (s : Sphere 3) :
    LinearMap.range (singularHomologyMap (halfMeridianMap A hA T s) 3) =
      LinearMap.ker (singularHomologyMap (halfOldInclusion A hA T) 3) :=
  SurgeryExteriorSequence.Seven.meridian_range_eq_kernel (halfBoundaryPair A hA T) s

theorem halfSection_range_eq_new_kernel (v : Sphere 3) :
    LinearMap.range (singularHomologyMap (halfSectionMap A hA T v) 3) =
      LinearMap.ker (singularHomologyMap (halfNewInclusion A hA T) 3) :=
  SurgeryExteriorSequence.Seven.meridian_range_eq_kernel (halfBoundaryPair A hA T).reverse v

theorem halfOldInclusion_section (v : Sphere 3) (c : SingularHomology (Sphere 3) 3) :
    singularHomologyMap (halfOldInclusion A hA T) 3
      (singularHomologyMap (halfSectionMap A hA T v) 3 c) =
        singularHomologyMap (halfBoundaryPair A hA T).attachingSphere 3 c :=
  SurgeryExteriorSequence.Seven.inclusion_section (halfBoundaryPair A hA T) v c

theorem halfNewInclusion_meridian (s : Sphere 3) (c : SingularHomology (Sphere 3) 3) :
    singularHomologyMap (halfNewInclusion A hA T) 3
      (singularHomologyMap (halfMeridianMap A hA T s) 3 c) =
        singularHomologyMap (halfBoundaryPair A hA T).beltSphere 3 c :=
  SurgeryExteriorSequence.Seven.inclusion_section (halfBoundaryPair A hA T).reverse s c

def halfExteriorOldQuotientEquiv (s : Sphere 3) :
    (SingularHomology (HalfExterior A hA T) 3 ⧸
      LinearMap.range (singularHomologyMap (halfMeridianMap A hA T s) 3)) ≃ₗ[ℤ]
        SingularHomology (OldPositiveHalf A T) 3 := by
  let q := (Submodule.quotEquivOfEq _ _ (halfMeridian_range_eq_old_kernel A hA T s)).trans
    ((singularHomologyMap (halfOldInclusion A hA T) 3).quotKerEquivOfSurjective
      (halfOldInclusion_surjective A hA T))
  let qa : (SingularHomology (HalfExterior A hA T) 3 ⧸
      LinearMap.range (singularHomologyMap (halfMeridianMap A hA T s) 3)) ≃+
        SingularHomology (OldPositiveHalf A T) 3 :=
    { toEquiv := q.toEquiv, map_add' := fun x y ↦ q.map_add' x y }
  exact qa.toIntLinearEquiv

def halfExteriorNewQuotientEquiv (v : Sphere 3) :
    (SingularHomology (HalfExterior A hA T) 3 ⧸
      LinearMap.range (singularHomologyMap (halfSectionMap A hA T v) 3)) ≃ₗ[ℤ]
        SingularHomology (PositiveHalf A hA T) 3 := by
  let q := (Submodule.quotEquivOfEq _ _ (halfSection_range_eq_new_kernel A hA T v)).trans
    ((singularHomologyMap (halfNewInclusion A hA T) 3).quotKerEquivOfSurjective
      (halfNewInclusion_surjective A hA T))
  let qa : (SingularHomology (HalfExterior A hA T) 3 ⧸
      LinearMap.range (singularHomologyMap (halfSectionMap A hA T v) 3)) ≃+
        SingularHomology (PositiveHalf A hA T) 3 :=
    { toEquiv := q.toEquiv, map_add' := fun x y ↦ q.map_add' x y }
  exact qa.toIntLinearEquiv

theorem halfExteriorOldQuotientEquiv_mk (s : Sphere 3)
    (c : SingularHomology (HalfExterior A hA T) 3) :
    halfExteriorOldQuotientEquiv A hA T s (Submodule.Quotient.mk c) =
      singularHomologyMap (halfOldInclusion A hA T) 3 c := by
  change (singularHomologyMap (halfOldInclusion A hA T) 3).quotKerEquivOfSurjective
    (halfOldInclusion_surjective A hA T)
    (Submodule.quotEquivOfEq _ _ (halfMeridian_range_eq_old_kernel A hA T s)
      (Submodule.Quotient.mk c)) = _
  rw [Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

theorem halfExteriorNewQuotientEquiv_mk (v : Sphere 3)
    (c : SingularHomology (HalfExterior A hA T) 3) :
    halfExteriorNewQuotientEquiv A hA T v (Submodule.Quotient.mk c) =
      singularHomologyMap (halfNewInclusion A hA T) 3 c := by
  change (singularHomologyMap (halfNewInclusion A hA T) 3).quotKerEquivOfSurjective
    (halfNewInclusion_surjective A hA T)
    (Submodule.quotEquivOfEq _ _ (halfSection_range_eq_new_kernel A hA T v)
      (Submodule.Quotient.mk c)) = _
  rw [Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

theorem halfMeridian_injective [Subsingleton (SingularHomology (OldPositiveHalf A T) 4)]
    (s : Sphere 3) : Injective (singularHomologyMap (halfMeridianMap A hA T s) 3) :=
  SurgeryExteriorSequence.Seven.meridian_injective (halfBoundaryPair A hA T) s

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery.ExteriorTwist
