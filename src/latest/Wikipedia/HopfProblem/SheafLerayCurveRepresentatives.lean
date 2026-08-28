import Wikipedia.HopfProblem.SheafLerayCurveSequence
import Wikipedia.HopfProblem.SheafLerayCurveCyclesSequenceRepresentatives

/-!
# The original higher Leray edge on genuine cycle representatives

The right edge sends an actual global cycle representative of the pushed
injective resolution to its composition with the original homology
quotient. All outer comparisons are the native ones for the source Ext
group and the genuine higher direct image.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.SheafLerayCurve

open SheafHigherDirectImage
open SheafLerayLowDegrees.Abstract (homComplex homCyclesIso)
open CuspNormalization.SheafCohomologyFinitePushforward (integerSheaf)

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (F : AbelianSheaf X) (n : ℕ)

/-- The exact original representative formula, with no vanishing assumptions. -/
theorem edge_homologyClass
    (z : integerSheaf Y ⟶ (canonicalComplex f F).cycles (n + 2)) :
    edge f F n
      ((SheafLerayLowDegrees.sourceCohomologyIso f F (injectiveResolution F) (n + 2)).inv
        ((homComplex (integerSheaf Y) (canonicalComplex f F)).homologyπ (n + 2)
          ((homCyclesIso (integerSheaf Y) (canonicalComplex f F) (n + 2)).hom z))) =
      (resolutionExtZeroIso f (injectiveResolution F) (n + 2)).inv
        (z ≫ (canonicalComplex f F).homologyπ (n + 2)) := by
  let s := SheafLerayLowDegrees.sourceCohomologyIso f F (injectiveResolution F) (n + 2)
  let c := (homComplex (integerSheaf Y) (canonicalComplex f F)).homologyπ (n + 2)
    ((homCyclesIso (integerSheaf Y) (canonicalComplex f F) (n + 2)).hom z)
  have hs : s.hom (s.inv c) = c := ConcreteCategory.congr_hom s.inv_hom_id c
  rw [edge_apply]
  change (resolutionExtZeroIso f (injectiveResolution F) (n + 2)).inv
    (Abstract.curveEdgeMap (integerSheaf Y) (canonicalComplex f F) n (s.hom (s.inv c))) = _
  rw [hs]
  exact congrArg (resolutionExtZeroIso f (injectiveResolution F) (n + 2)).inv
    (Abstract.cyclesEdgeMap_homologyClass (integerSheaf Y) (canonicalComplex f F) (n + 1) z)

end Wikipedia.HopfProblem.SheafLerayCurve
