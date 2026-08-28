import Wikipedia.NoExoticSixSphere.ModTwoCapSupport
import Wikipedia.NoExoticSixSphere.SmallCoefficientChainRange

/-!
# The original cap localized to an actual subspace

A relative cochain vanishes on chains in the second subspace. Capping
an actual small chain therefore lies in the image of the first subspace.
Its original injective chain inclusion gives a unique actual subspace
chain. The inclusion formula and both piece formulas retain the native
front/back cap operation.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.SmallModTwoCap

open ModTwoCapProduct (Coefficient)
open SingularSubcomplex (SmallChains smallInclusionMap)

variable {X : Type} [TopologicalSpace X] (U V : Set X)

abbrev complex := (SingularSubcomplex.Small U V).chainComplex Coefficient

/-- The actual subspace coefficient-chain inclusion is injective in every degree. -/
theorem inclusion_injective (q : ℕ) :
    Function.Injective ((RelativeCoefficients.inclusion Coefficient U).f q).hom :=
  (ModuleCat.mono_iff_injective ((RelativeCoefficients.inclusion Coefficient U).f q)).mp
    inferInstance

/-- The original cap, uniquely lifted to the actual first subspace chain group. -/
def capInDegree {p q n : ℕ} (h : p + q = n) (α : RelativeModTwoCochains.Cochain V p) :
    SmallChains Coefficient U V n →ₗ[ℤ] ModTwoChains.Chains U q :=
  LinearMap.codRestrictOfInjective
    ((ModTwoCapProduct.capInDegree h (RelativeModTwoCochains.toAbsolute V p α)).comp
      (smallInclusionMap Coefficient U V n))
    ((RelativeCoefficients.inclusion Coefficient U).f q).hom (inclusion_injective U q)
    (fun c => ModTwoCapProduct.relative_capInDegree_mem_range U V h α _
      (SingularSubcomplex.smallInclusion_mem_sup Coefficient U V n c))

/-- Inclusion gives exactly the original cap of the original small-chain image. -/
theorem inclusion_capInDegree {p q n : ℕ} (h : p + q = n)
    (α : RelativeModTwoCochains.Cochain V p) (c : SmallChains Coefficient U V n) :
    ((RelativeCoefficients.inclusion Coefficient U).f q).hom (capInDegree U V h α c) =
      ModTwoCapProduct.capInDegree h (RelativeModTwoCochains.toAbsolute V p α)
        (smallInclusionMap Coefficient U V n c) :=
  LinearMap.codRestrictOfInjective_comp_apply _ _ _ _ c

theorem capInDegree_zero {p q n : ℕ} (h : p + q = n) :
    capInDegree U V h (0 : RelativeModTwoCochains.Cochain V p) = 0 := by
  apply LinearMap.ext
  intro c
  apply inclusion_injective U q
  apply (inclusion_capInDegree U V h 0 c).trans
  rw [map_zero, ModTwoCapProduct.capInDegree_zero, LinearMap.zero_apply]
  exact ((RelativeCoefficients.inclusion Coefficient U).f q).hom.map_zero.symm

theorem capInDegree_add {p q n : ℕ} (h : p + q = n)
    (α β : RelativeModTwoCochains.Cochain V p) :
    capInDegree U V h (α + β) = capInDegree U V h α + capInDegree U V h β := by
  apply LinearMap.ext
  intro c
  apply inclusion_injective U q
  rw [LinearMap.add_apply, map_add, inclusion_capInDegree, inclusion_capInDegree,
    inclusion_capInDegree, map_add, ModTwoCapProduct.capInDegree_add, LinearMap.add_apply]

/-- On the original left piece, localized cap is the original cap of the restricted cochain. -/
theorem capInDegree_toSmallLeft {p q n : ℕ} (h : p + q = n)
    (α : RelativeModTwoCochains.Cochain V p) (c : ModTwoChains.Chains U n) :
    capInDegree U V h α
        ((((SimplicialCoefficients.chains Coefficient).map
          (SingularSubcomplex.toSmallLeft U V)).f n).hom c) =
      ModTwoCapProduct.capInDegree h
        (ModTwoCapProduct.pullback (subtypeInclusion U) p
          (RelativeModTwoCochains.toAbsolute V p α)) c := by
  subst n
  apply inclusion_injective U q
  apply (inclusion_capInDegree U V rfl α _).trans
  have he := congrArg (fun m => (m.f (p + q)).hom c)
    (SingularSubcomplex.chainToSmallLeft_inclusion U V Coefficient)
  apply (congrArg (ModTwoCapProduct.capInDegree (q := q) rfl
    (RelativeModTwoCochains.toAbsolute V p α)) he).trans
  exact (ModTwoCapProduct.spaceMap_cap (subtypeInclusion U) p q
    (RelativeModTwoCochains.toAbsolute V p α) c).symm

/-- On the original right piece, the relative cochain makes localized cap zero. -/
theorem capInDegree_toSmallRight {p q n : ℕ} (h : p + q = n)
    (α : RelativeModTwoCochains.Cochain V p) (c : ModTwoChains.Chains V n) :
    capInDegree U V h α
      ((((SimplicialCoefficients.chains Coefficient).map
        (SingularSubcomplex.toSmallRight U V)).f n).hom c) = 0 := by
  apply inclusion_injective U q
  apply (inclusion_capInDegree U V h α _).trans
  have he := congrArg (fun m => (m.f n).hom c)
    (SingularSubcomplex.chainToSmallRight_inclusion U V Coefficient)
  apply (congrArg (ModTwoCapProduct.capInDegree h
    (RelativeModTwoCochains.toAbsolute V p α)) he).trans
  exact (RelativeModTwoCap.capInDegree_inclusion_zero V h α c).trans
    ((RelativeCoefficients.inclusion Coefficient U).f q).hom.map_zero.symm

end NoExoticSixSphere.SmallModTwoCap
