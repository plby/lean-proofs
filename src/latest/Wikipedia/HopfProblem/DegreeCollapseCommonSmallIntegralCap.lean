import Wikipedia.HopfProblem.DegreeCollapseSmallRelativeIntegralCochains
import Wikipedia.HopfProblem.DegreeCollapseSmallIntegralCapDifference
import Wikipedia.NoExoticSixSphere.CommonSmallChains

/-!
# Integral cap localized in the actual overlap

A small-relative integral cochain vanishes on both annihilated pieces.
On a common-small chain, the original cap therefore lies in both
neighborhood-chain images. Their proved intersection is the original
overlap-chain image, whose injective inclusion gives the unique lift.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.CommonSmallIntegralCap

open FirstHurewicz SingularMayerVietoris NoExoticSixSphere
open IntegralCap (Coefficient)
open SmallRelativeIntegralCochains (Cochain toAbsolute)

variable {X : Type} [TopologicalSpace X] (U A V B : Set X)

abbrev complex := (SingularSubcomplex.commonSmall U A V B : SSet).chainComplex Coefficient

abbrev inclusion := SingularSubcomplex.commonSmallChainInclusion U A V B Coefficient

theorem cap_mem_overlap {p q n : ℕ} (h : p + q = n) (α : Cochain A B p)
    (c : (complex U A V B).X n) :
    IntegralCap.capInDegree h (toAbsolute A B p α) (((inclusion U A V B).f n).hom c) ∈
      LinearMap.range (inducedChain (subtypeInclusion (U ∩ V)) q) := by
  have hc := (SingularSubcomplex.commonSmallInclusion_range U A V B Coefficient n).le ⟨c, rfl⟩
  apply (SingularSubcomplex.inclusion_range_inter Coefficient U V q).ge
  exact ⟨IntegralCap.capInDegree_mem_range_of_mem_sup U A h (toAbsolute A B p α)
    (SmallRelativeIntegralCochains.pullback_toAbsolute_left A B p α) _
    ((SingularSubcomplex.smallInclusion_range Coefficient U A n).le hc.1),
    IntegralCap.capInDegree_mem_range_of_mem_sup V B h (toAbsolute A B p α)
    (SmallRelativeIntegralCochains.pullback_toAbsolute_right A B p α) _
    ((SingularSubcomplex.smallInclusion_range Coefficient V B n).le hc.2)⟩

/-- The original overlap cap, lifted through the actual injective integral inclusion. -/
def capInDegree {p q n : ℕ} (h : p + q = n) (α : Cochain A B p) :
    (complex U A V B).X n →ₗ[ℤ] Chains (U ∩ V : Set X) q :=
  LinearMap.codRestrictOfInjective
    ((IntegralCap.capInDegree h (toAbsolute A B p α)).comp
      ((inclusion U A V B).f n).hom)
    (inducedChain (subtypeInclusion (U ∩ V)) q)
    (SmallIntegralCap.inclusion_injective (U ∩ V) q) (cap_mem_overlap U A V B h α)

theorem inclusion_capInDegree {p q n : ℕ} (h : p + q = n) (α : Cochain A B p)
    (c : (complex U A V B).X n) :
    inducedChain (subtypeInclusion (U ∩ V)) q (capInDegree U A V B h α c) =
      IntegralCap.capInDegree h (toAbsolute A B p α) (((inclusion U A V B).f n).hom c) :=
  LinearMap.codRestrictOfInjective_comp_apply _ _ _ _ c

theorem capInDegree_zero {p q n : ℕ} (h : p + q = n) :
    capInDegree U A V B h (0 : Cochain A B p) = 0 := by
  apply LinearMap.ext
  intro c
  apply SmallIntegralCap.inclusion_injective (U ∩ V) q
  let z : Chains X n := ((inclusion U A V B).f n).hom c
  exact (inclusion_capInDegree U A V B h 0 c).trans
    ((congrArg (fun α => IntegralCap.capInDegree (q := q) h α z)
      (toAbsolute A B p).map_zero).trans
        ((LinearMap.congr_fun (IntegralCap.capInDegree_zero h) z).trans
          (inducedChain (subtypeInclusion (U ∩ V)) q).map_zero.symm))

theorem capInDegree_add {p q n : ℕ} (h : p + q = n) (α β : Cochain A B p) :
    capInDegree U A V B h (α + β) = capInDegree U A V B h α + capInDegree U A V B h β := by
  apply LinearMap.ext
  intro c
  apply SmallIntegralCap.inclusion_injective (U ∩ V) q
  let z : Chains X n := ((inclusion U A V B).f n).hom c
  have he : IntegralCap.capInDegree (q := q) h (toAbsolute A B p (α + β)) =
      IntegralCap.capInDegree h (toAbsolute A B p α) +
        IntegralCap.capInDegree h (toAbsolute A B p β) :=
    (congrArg (IntegralCap.capInDegree (q := q) h) ((toAbsolute A B p).map_add α β)).trans
      (IntegralCap.capInDegree_add h _ _)
  exact (inclusion_capInDegree U A V B h (α + β) c).trans
    ((LinearMap.congr_fun he z).trans
      ((congrArg₂ (fun x y => x + y) (inclusion_capInDegree U A V B h α c).symm
        (inclusion_capInDegree U A V B h β c).symm).trans
          ((inducedChain (subtypeInclusion (U ∩ V)) q).map_add _ _).symm))

end Wikipedia.HopfProblem.DegreeCollapse.CommonSmallIntegralCap
