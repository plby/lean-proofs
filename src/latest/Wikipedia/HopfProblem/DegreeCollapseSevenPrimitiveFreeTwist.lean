import Wikipedia.HopfProblem.DegreeCollapseSevenExponentTwoExterior
import Wikipedia.HopfProblem.DegreeCollapseExponentTwoFreeQuotient

/-!
# A primitive free class and the exact finite torsion size after the actual twist

Apply the integral-coordinate construction to the original old and new
exterior homology maps. In the zero doubled-section branch, the genuine
new half has a primitive integer coordinate and its full torsion kernel
has one quarter of the original half's third-homology cardinality.
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
  (B : FramedAttachingProduct e a f) (hB : B.radius = 2)
  (ρ : C(Sphere 3, OrthogonalOperators 4))
  (ht : ∀ (s : Sphere 3) (w : Vector 4), B.tube (s, w) = A.tube (s, (ρ s).1.1 w))

theorem halfTwist_primitive_free_part (v s : Sphere 3) (j : ℤ)
    (hρ : ∀ c : SingularHomology (Sphere 3) 3,
      singularHomologyMap (column v ρ) 3 c = j • c)
    (h2 : ∀ x : SingularHomology (OldPositiveHalf A T) 3, (2 : ℤ) • x = 0)
    (h : SingularHomology (HalfExterior A hA T) 3)
    (hh : (2 : ℤ) • h = halfMeridianClass A hA T s)
    (hc : singularHomologyMap (halfBoundaryPair A hA T).attachingSphere 3
      (unitSphereTopClass 2) ≠ 0)
    (hβ : (2 : ℤ) • (halfSectionClass A hA T v + j • halfMeridianClass A hA T s) = 0) :
    ∃ σ : SingularHomology (PositiveHalf B hB (twistTimeData A hA B hB ρ ht T)) 3 →+ ℤ,
      σ (halfTwistedNewMap A hA T B hB ρ ht h) = 1 ∧ Finite σ.ker ∧
      (∀ x : σ.ker, (2 : ℤ) • x = 0) ∧
        4 * Nat.card σ.ker = Nat.card (SingularHomology (OldPositiveHalf A T) 3) := by
  have hqμ : singularHomologyMap (halfOldInclusion A hA T) 3
      (halfMeridianClass A hA T s) = 0 := by
    change halfMeridianClass A hA T s ∈
      (singularHomologyMap (halfOldInclusion A hA T) 3).toAddMonoidHom.ker
    rw [halfOldInclusion_addKernel]
    exact AddSubgroup.mem_zmultiples _
  have hqβ : singularHomologyMap (halfOldInclusion A hA T) 3
      (halfSectionClass A hA T v + j • halfMeridianClass A hA T s) ≠ 0 := by
    rw [map_add, map_zsmul, hqμ, zsmul_zero, add_zero,
      halfSectionClass, halfOldInclusion_section]
    exact hc
  have hβne : halfSectionClass A hA T v + j • halfMeridianClass A hA T s ≠ 0 := by
    intro he
    apply hqβ
    rw [he, map_zero]
  exact ExponentTwoFreeQuotient.primitive_free_part (halfMeridianClass A hA T s)
    (singularHomologyMap (halfOldInclusion A hA T) 3).toAddMonoidHom
    (halfOldInclusion_addKernel A hA T s) h2 (halfMeridian_coefficient_injective A hA T s)
    (halfOldInclusion_surjective A hA T) h hh
    (halfSectionClass A hA T v + j • halfMeridianClass A hA T s) hβ hβne
    (halfTwistedNewMap A hA T B hB ρ ht).toAddMonoidHom
    (halfTwistedNewMap_surjective A hA T B hB ρ ht)
    (halfTwistedNewMap_addKernel A hA T B hB ρ ht v s j hρ)

end FramedAttachingProduct.UnitSurgery.ExteriorTwist
end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
