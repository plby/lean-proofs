import Wikipedia.NoExoticSixSphere.SmallRelativeModTwoCochains
import Wikipedia.NoExoticSixSphere.CommonSmallChains
import Wikipedia.NoExoticSixSphere.SmallModTwoCapBoundary

/-!
# Cap localized to the actual overlap

Capping a common-small chain with a small-relative cochain gives a
chain supported in both neighborhoods. The proved intersection of
actual chain images gives a unique chain in their actual overlap.
-/

noncomputable section

open Wikipedia.HopfProblem SphereHomologyCoefficients

namespace NoExoticSixSphere.CommonSmallModTwoCap

open ModTwoCapProduct (Coefficient)
open SmallRelativeModTwoCochains (Cochain toAbsolute)

variable {X : Type} [TopologicalSpace X] (U A V B : Set X)

abbrev complex := (SingularSubcomplex.commonSmall U A V B : SSet).chainComplex Coefficient

abbrev inclusion := SingularSubcomplex.commonSmallChainInclusion U A V B Coefficient

/-- The original ambient cap lies in the actual overlap-chain image. -/
theorem cap_mem_overlap {p q n : ℕ} (h : p + q = n) (α : Cochain A B p)
    (c : (complex U A V B).X n) :
    ModTwoCapProduct.capInDegree h (toAbsolute A B p α) (((inclusion U A V B).f n).hom c) ∈
      LinearMap.range ((RelativeCoefficients.inclusion Coefficient (U ∩ V)).f q).hom := by
  have hc := (SingularSubcomplex.commonSmallInclusion_range U A V B Coefficient n).le ⟨c, rfl⟩
  apply (SingularSubcomplex.inclusion_range_inter Coefficient U V q).ge
  exact ⟨ModTwoCapProduct.capInDegree_mem_range_of_mem_sup U A h (toAbsolute A B p α)
    (SmallRelativeModTwoCochains.pullback_toAbsolute_left A B p α) _
    ((SingularSubcomplex.smallInclusion_range Coefficient U A n).le hc.1),
    ModTwoCapProduct.capInDegree_mem_range_of_mem_sup V B h (toAbsolute A B p α)
    (SmallRelativeModTwoCochains.pullback_toAbsolute_right A B p α) _
    ((SingularSubcomplex.smallInclusion_range Coefficient V B n).le hc.2)⟩

/-- Cap lifted through the original injective overlap inclusion. -/
def capInDegree {p q n : ℕ} (h : p + q = n) (α : Cochain A B p) :
    (complex U A V B).X n →ₗ[ℤ] ModTwoChains.Chains (U ∩ V : Set X) q :=
  LinearMap.codRestrictOfInjective
    ((ModTwoCapProduct.capInDegree h (toAbsolute A B p α)).comp
      ((inclusion U A V B).f n).hom)
    ((RelativeCoefficients.inclusion Coefficient (U ∩ V)).f q).hom
    (SmallModTwoCap.inclusion_injective (U ∩ V) q) (cap_mem_overlap U A V B h α)

/-- The lifted chain has exactly the original ambient cap as its image. -/
theorem inclusion_capInDegree {p q n : ℕ} (h : p + q = n) (α : Cochain A B p)
    (c : (complex U A V B).X n) :
    ((RelativeCoefficients.inclusion Coefficient (U ∩ V)).f q).hom
        (capInDegree U A V B h α c) =
      ModTwoCapProduct.capInDegree h (toAbsolute A B p α) (((inclusion U A V B).f n).hom c) :=
  LinearMap.codRestrictOfInjective_comp_apply _ _ _ _ c

theorem capInDegree_zero {p q n : ℕ} (h : p + q = n) :
    capInDegree U A V B h (0 : Cochain A B p) = 0 := by
  apply LinearMap.ext
  intro c
  apply SmallModTwoCap.inclusion_injective (U ∩ V) q
  apply (inclusion_capInDegree U A V B h 0 c).trans
  rw [map_zero, ModTwoCapProduct.capInDegree_zero, LinearMap.zero_apply]
  exact ((RelativeCoefficients.inclusion Coefficient (U ∩ V)).f q).hom.map_zero.symm

theorem capInDegree_add {p q n : ℕ} (h : p + q = n) (α β : Cochain A B p) :
    capInDegree U A V B h (α + β) = capInDegree U A V B h α + capInDegree U A V B h β := by
  apply LinearMap.ext
  intro c
  apply SmallModTwoCap.inclusion_injective (U ∩ V) q
  rw [LinearMap.add_apply, map_add, inclusion_capInDegree, inclusion_capInDegree,
    inclusion_capInDegree, map_add, ModTwoCapProduct.capInDegree_add]
  rfl

end NoExoticSixSphere.CommonSmallModTwoCap
