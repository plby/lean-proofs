import Wikipedia.NoExoticSixSphere.CommonSmallCapCohomology

/-!
# The original overlap cap maps to both original localized caps

The two actual intersection inclusions preserve cap representatives.
These chain identities identify the overlap cap with the boundaries
of the two localized cochain lifts used for Mayer--Vietoris.
-/

noncomputable section

open CategoryTheory

namespace NoExoticSixSphere.CommonSmallModTwoCap

open ModTwoCapProduct (Coefficient)
open SmallRelativeModTwoCochains (Cochain)
open SingularSubcomplex (SmallChains smallInclusionMap)

variable {X : Type} [TopologicalSpace X] (U A V B : Set X)

abbrev leftChainMap :=
  (SimplicialCoefficients.chains Coefficient).map (SingularSubcomplex.intersectionLeft U V)

abbrev rightChainMap :=
  (SimplicialCoefficients.chains Coefficient).map (SingularSubcomplex.intersectionRight U V)

theorem leftChainMap_inclusion :
    leftChainMap U V ≫ RelativeCoefficients.inclusion Coefficient U =
      RelativeCoefficients.inclusion Coefficient (U ∩ V) :=
  ((SimplicialCoefficients.chains Coefficient).map_comp
    (SingularSubcomplex.intersectionLeft U V) (SingularSubcomplex.inclusion U)).symm.trans
      (congrArg (SimplicialCoefficients.chains Coefficient).map
        (SingularSubcomplex.intersectionLeft_inclusion U V))

theorem rightChainMap_inclusion :
    rightChainMap U V ≫ RelativeCoefficients.inclusion Coefficient V =
      RelativeCoefficients.inclusion Coefficient (U ∩ V) :=
  ((SimplicialCoefficients.chains Coefficient).map_comp
    (SingularSubcomplex.intersectionRight U V) (SingularSubcomplex.inclusion V)).symm.trans
      (congrArg (SimplicialCoefficients.chains Coefficient).map
        (SingularSubcomplex.intersectionRight_inclusion U V))

/-- The original left intersection map sends overlap cap to the actual left localized cap. -/
theorem leftChainMap_capInDegree {p q n : ℕ} (h : p + q = n) (α : Cochain A B p)
    (c : (complex U A V B).X n) (cU : SmallChains Coefficient U A n)
    (hcU : smallInclusionMap Coefficient U A n cU = ((inclusion U A V B).f n).hom c) :
    ((leftChainMap U V).f q).hom (capInDegree U A V B h α c) =
      SmallModTwoCap.capInDegree U A h
        (((RelativeModTwoMayerVietoris.smallRestrictionLeft A B).f p).hom α) cU := by
  apply SmallModTwoCap.inclusion_injective U q
  have hi := congrArg (fun m => (m.f q).hom (capInDegree U A V B h α c))
    (leftChainMap_inclusion U V)
  have he := SmallModTwoCap.inclusion_capInDegree U A h
    (((RelativeModTwoMayerVietoris.smallRestrictionLeft A B).f p).hom α) cU
  exact hi.trans ((inclusion_capInDegree U A V B h α c).trans
    (he.trans (congrArg₂ (fun γ t => ModTwoCapProduct.capInDegree h γ t)
      (SmallRelativeModTwoCochains.toAbsolute_left A B p α) hcU)).symm)

/-- The original right intersection map sends the same overlap cap to the right localized cap. -/
theorem rightChainMap_capInDegree {p q n : ℕ} (h : p + q = n) (α : Cochain A B p)
    (c : (complex U A V B).X n) (cV : SmallChains Coefficient V B n)
    (hcV : smallInclusionMap Coefficient V B n cV = ((inclusion U A V B).f n).hom c) :
    ((rightChainMap U V).f q).hom (capInDegree U A V B h α c) =
      SmallModTwoCap.capInDegree V B h
        (((RelativeModTwoMayerVietoris.smallRestrictionRight A B).f p).hom α) cV := by
  apply SmallModTwoCap.inclusion_injective V q
  have hi := congrArg (fun m => (m.f q).hom (capInDegree U A V B h α c))
    (rightChainMap_inclusion U V)
  have he := SmallModTwoCap.inclusion_capInDegree V B h
    (((RelativeModTwoMayerVietoris.smallRestrictionRight A B).f p).hom α) cV
  exact hi.trans ((inclusion_capInDegree U A V B h α c).trans
    (he.trans (congrArg₂ (fun γ t => ModTwoCapProduct.capInDegree h γ t)
      (SmallRelativeModTwoCochains.toAbsolute_right A B p α) hcV)).symm)

end NoExoticSixSphere.CommonSmallModTwoCap
