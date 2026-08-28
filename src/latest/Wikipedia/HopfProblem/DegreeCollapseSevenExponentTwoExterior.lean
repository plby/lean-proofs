import Wikipedia.HopfProblem.DegreeCollapseExponentTwoSurgeryQuotient
import Wikipedia.HopfProblem.DegreeCollapseSevenMeridianCharacter

/-!
# Exponent-two alternatives on the actual seven-dimensional exterior

The original meridian character constructs a half-meridian in the original
exterior homology. After a prescribed twist, the genuine new inclusion
sends that element to an infinite-order class or an exact order-four class.
The finite case has the same cardinality as the original half. No splitting
or abstract replacement of the original homology groups is used.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
namespace FramedAttachingProduct.UnitSurgery.ExteriorTwist

open NoExoticSixSphere GLOrthonormalization OrthogonalPaths
open SingularMayerVietoris SphereHomology

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hA : A.radius = 2) (T : TimeData A)
  [Subsingleton (SingularHomology (OldPositiveHalf A T) 4)]
  [Finite (SingularHomology (OldPositiveHalf A T) 3)]

theorem exists_half_meridian_of_exponent_two (s : Sphere 3)
    (h2 : ∀ x : SingularHomology (OldPositiveHalf A T) 3, (2 : ℤ) • x = 0)
    (hn : ∃ x, meridianCharacter A hA T s x ≠ 0) :
    ∃ h : SingularHomology (HalfExterior A hA T) 3,
      (2 : ℤ) • h = halfMeridianClass A hA T s :=
  CyclicExtensionCharacter.exists_half_meridian_of_character_ne_zero
    (halfMeridianClass A hA T s)
    (singularHomologyMap (halfOldInclusion A hA T) 3).toAddMonoidHom
    (halfOldInclusion_addKernel A hA T s) h2
    (halfMeridian_coefficient_injective A hA T s) (halfOldInclusion_surjective A hA T) hn

theorem exists_even_twist_double_section (v s : Sphere 3)
    (h2 : ∀ x : SingularHomology (OldPositiveHalf A T) 3, (2 : ℤ) • x = 0)
    (hz : meridianCharacter A hA T s
      (singularHomologyMap (halfBoundaryPair A hA T).attachingSphere 3
        (unitSphereTopClass 2)) = 0) :
    ∃ j : ℤ,
      (2 : ℤ) • (halfSectionClass A hA T v + (2 * j) • halfMeridianClass A hA T s) = 0 ∨
      (2 : ℤ) • (halfSectionClass A hA T v + (2 * j) • halfMeridianClass A hA T s) =
        (2 : ℤ) • halfMeridianClass A hA T s := by
  apply CyclicExtensionCharacter.exists_even_twist_double_relation
    (halfMeridianClass A hA T s)
    (singularHomologyMap (halfOldInclusion A hA T) 3).toAddMonoidHom
    (halfOldInclusion_addKernel A hA T s) h2
    (halfMeridian_coefficient_injective A hA T s) (halfOldInclusion_surjective A hA T)
      (halfSectionClass A hA T v)
  change meridianCharacter A hA T s
    (singularHomologyMap (halfOldInclusion A hA T) 3 (halfSectionClass A hA T v)) = 0
  rw [halfSectionClass, halfOldInclusion_section]
  exact hz

variable (B : FramedAttachingProduct e a f) (hB : B.radius = 2)
  (ρ : C(Sphere 3, OrthogonalOperators 4))
  (ht : ∀ (s : Sphere 3) (w : Vector 4), B.tube (s, w) = A.tube (s, (ρ s).1.1 w))

omit [Subsingleton (SingularHomology (OldPositiveHalf A T) 4)]
  [Finite (SingularHomology (OldPositiveHalf A T) 3)] in
theorem halfTwistedNewMap_addKernel (v s : Sphere 3) (j : ℤ)
    (hρ : ∀ c : SingularHomology (Sphere 3) 3,
      singularHomologyMap (column v ρ) 3 c = j • c) :
    (halfTwistedNewMap A hA T B hB ρ ht).toAddMonoidHom.ker =
      AddSubgroup.zmultiples (halfSectionClass A hA T v + j • halfMeridianClass A hA T s) := by
  change (LinearMap.ker (halfTwistedNewMap A hA T B hB ρ ht)).toAddSubgroup = _
  rw [halfTwistedNewMap_kernel A hA T B hB ρ ht v s j hρ,
    CyclicSurgeryIndex.span_toAddSubgroup]

omit [Finite (SingularHomology (OldPositiveHalf A T) 3)] in
theorem halfTwist_infinite_order (v s : Sphere 3) (j : ℤ)
    (hρ : ∀ c : SingularHomology (Sphere 3) 3,
      singularHomologyMap (column v ρ) 3 c = j • c)
    (h : SingularHomology (HalfExterior A hA T) 3)
    (hh : (2 : ℤ) • h = halfMeridianClass A hA T s)
    (hβ : (2 : ℤ) • (halfSectionClass A hA T v + j • halfMeridianClass A hA T s) = 0) :
    Injective (fun n : ℤ ↦ n • halfTwistedNewMap A hA T B hB ρ ht h) :=
  ExponentTwoSurgeryQuotient.infinite_order_of_double_section_zero
    (halfMeridianClass A hA T s) _ h (halfMeridian_coefficient_injective A hA T s) hh
    (halfTwistedNewMap A hA T B hB ρ ht).toAddMonoidHom
    (halfTwistedNewMap_addKernel A hA T B hB ρ ht v s j hρ) hβ

omit [Finite (SingularHomology (OldPositiveHalf A T) 3)] in
theorem halfTwist_order_four (v s : Sphere 3) (j : ℤ)
    (hρ : ∀ c : SingularHomology (Sphere 3) 3,
      singularHomologyMap (column v ρ) 3 c = j • c)
    (h : SingularHomology (HalfExterior A hA T) 3)
    (hh : (2 : ℤ) • h = halfMeridianClass A hA T s)
    (hc : singularHomologyMap (halfBoundaryPair A hA T).attachingSphere 3
      (unitSphereTopClass 2) ≠ 0)
    (hβ : (2 : ℤ) • (halfSectionClass A hA T v + j • halfMeridianClass A hA T s) =
      (2 : ℤ) • halfMeridianClass A hA T s) :
    (4 : ℤ) • halfTwistedNewMap A hA T B hB ρ ht h = 0 ∧
      (2 : ℤ) • halfTwistedNewMap A hA T B hB ρ ht h ≠ 0 := by
  have hqμ : singularHomologyMap (halfOldInclusion A hA T) 3
      (halfMeridianClass A hA T s) = 0 := by
    change halfMeridianClass A hA T s ∈
      (singularHomologyMap (halfOldInclusion A hA T) 3).toAddMonoidHom.ker
    rw [halfOldInclusion_addKernel]
    exact AddSubgroup.mem_zmultiples _
  apply ExponentTwoSurgeryQuotient.order_four_of_double_section_eq_double_meridian
    (halfMeridianClass A hA T s) _ h (halfMeridian_coefficient_injective A hA T s) hh
    (halfTwistedNewMap A hA T B hB ρ ht).toAddMonoidHom
    (halfTwistedNewMap_addKernel A hA T B hB ρ ht v s j hρ)
    (singularHomologyMap (halfOldInclusion A hA T) 3).toAddMonoidHom hqμ _ hβ
  change singularHomologyMap (halfOldInclusion A hA T) 3
    (halfSectionClass A hA T v + j • halfMeridianClass A hA T s) ≠ 0
  rw [map_add, map_zsmul, hqμ, zsmul_zero, add_zero,
    halfSectionClass, halfOldInclusion_section]
  exact hc

theorem halfTwist_card_eq (v s : Sphere 3) (j : ℤ)
    (hρ : ∀ c : SingularHomology (Sphere 3) 3,
      singularHomologyMap (column v ρ) 3 c = j • c)
    (hβ : (2 : ℤ) • (halfSectionClass A hA T v + j • halfMeridianClass A hA T s) =
      (2 : ℤ) • halfMeridianClass A hA T s) :
    Finite (SingularHomology (PositiveHalf B hB (twistTimeData A hA B hB ρ ht T)) 3) ∧
      Nat.card (SingularHomology (PositiveHalf B hB (twistTimeData A hA B hB ρ ht T)) 3) =
        Nat.card (SingularHomology (OldPositiveHalf A T) 3) := by
  have he := ExponentTwoSurgeryQuotient.card_eq_of_double_section_eq_double_meridian
    (halfMeridianClass A hA T s)
    (halfSectionClass A hA T v + j • halfMeridianClass A hA T s)
    (halfMeridian_coefficient_injective A hA T s)
    (halfTwistedNewMap A hA T B hB ρ ht).toAddMonoidHom
    (halfTwistedNewMap_addKernel A hA T B hB ρ ht v s j hρ)
    (singularHomologyMap (halfOldInclusion A hA T) 3).toAddMonoidHom
    (halfOldInclusion_surjective A hA T) (halfOldInclusion_addKernel A hA T s)
    (halfTwistedNewMap_surjective A hA T B hB ρ ht) hβ
  refine ⟨Nat.finite_of_card_ne_zero ?_, he⟩
  rw [he]
  exact Nat.card_pos.ne'

end FramedAttachingProduct.UnitSurgery.ExteriorTwist
end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
