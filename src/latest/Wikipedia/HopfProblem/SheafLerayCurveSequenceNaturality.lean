import Wikipedia.HopfProblem.SheafLerayCurveSequence
import Wikipedia.HopfProblem.SheafLerayCurveAbstractNaturality
import Wikipedia.HopfProblem.SheafLerayCurveSheafComparisonsNaturality
import Wikipedia.HopfProblem.SheafLerayLowDegreesSequenceComparisons

/-!
# Actual coefficient naturality of the higher curve-type Leray edges

Every square uses the original coefficient sheaf morphism, its native
lift to the chosen injective resolutions, and the genuine right-derived
coefficient map. The finite vanishing hypotheses serve only to make
the original quotient-induced left comparison invertible.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.SheafLerayCurve

open SheafHigherDirectImage
open SheafLerayLowDegrees (coefficientResolutionMap sourceCohomologyIso)
open CuspNormalization.SheafCohomologyFinitePushforward (integerSheaf)

attribute [local irreducible] Abstract.curveFirstMap

variable {X Y : TopCat.{0}} (f : X ⟶ Y) {F G : AbelianSheaf X}
  (g : F ⟶ G) (n : ℕ)

/-- The original left edge commutes with actual maps on both higher
direct images and source cohomology. -/
theorem inflation_naturality (hF : CohomologyVanishing f F (n + 3))
    (hG : CohomologyVanishing f G (n + 3))
    (x : CategoryTheory.Sheaf.H.{0} (sheaf f F (n + 1)) 1) :
    inflation f G n hG
        (CategoryTheory.Sheaf.H.map ((functor f (n + 1)).map g) 1 x) =
      CategoryTheory.Sheaf.H.map g (n + 2) (inflation f F n hF x) := by
  rw [inflation_apply, inflation_apply]
  let a := (resolutionCohomologyIso f (injectiveResolution F) (n + 1) 1).inv x
  have h₀ := ConcreteCategory.congr_hom
    (coefficient_resolutionCohomologyIso_inv_naturality f g (n + 1) 1) x
  have h₁ := ConcreteCategory.congr_hom
    (Abstract.curveFirstMap_naturality (integerSheaf Y) (coefficientResolutionMap f g) n
      (canonicalComplex_term_injective f F) (canonicalComplex_term_injective f G)
      (canonicalComplex_higherVanishing f F _ hF)
      (canonicalComplex_higherVanishing f G _ hG)) a
  have h₂ := ConcreteCategory.congr_hom
    (SheafLerayLowDegrees.coefficient_sourceCohomologyIso_inv_naturality f g (n + 2))
    (Abstract.curveFirstMap (integerSheaf Y) (canonicalComplex f F)
      (canonicalComplex_term_injective f F) n (canonicalComplex_higherVanishing f F _ hF) a)
  exact (congrArg (fun b => (sourceCohomologyIso f G (injectiveResolution G) (n + 2)).inv
    (Abstract.curveFirstMap (integerSheaf Y) (canonicalComplex f G)
      (canonicalComplex_term_injective f G) n (canonicalComplex_higherVanishing f G _ hG) b))
        h₀).trans
      ((congrArg (sourceCohomologyIso f G (injectiveResolution G) (n + 2)).inv h₁).trans h₂)

/-- The original right edge commutes with every actual coefficient map,
without any vanishing hypotheses. -/
theorem edge_naturality (x : CategoryTheory.Sheaf.H.{0} F (n + 2)) :
    edge f G n (CategoryTheory.Sheaf.H.map g (n + 2) x) =
      CategoryTheory.Sheaf.H.map ((functor f (n + 2)).map g) 0 (edge f F n x) := by
  rw [edge_apply, edge_apply]
  let a := (sourceCohomologyIso f F (injectiveResolution F) (n + 2)).hom x
  have h₀ := ConcreteCategory.congr_hom
    (SheafLerayLowDegrees.coefficient_sourceCohomologyIso_hom_naturality f g (n + 2)) x
  have h₁ := ConcreteCategory.congr_hom
    (Abstract.curveEdgeMap_naturality (integerSheaf Y) (coefficientResolutionMap f g) n) a
  have h₂ := ConcreteCategory.congr_hom
    (coefficient_resolutionExtZeroIso_inv_naturality f g (n + 2))
    (Abstract.curveEdgeMap (integerSheaf Y) (canonicalComplex f F) n a)
  exact (congrArg (fun b => (resolutionExtZeroIso f (injectiveResolution G) (n + 2)).inv
    (Abstract.curveEdgeMap (integerSheaf Y) (canonicalComplex f G) n b)) h₀).trans
      ((congrArg (resolutionExtZeroIso f (injectiveResolution G) (n + 2)).inv h₁).trans h₂)

end Wikipedia.HopfProblem.SheafLerayCurve
