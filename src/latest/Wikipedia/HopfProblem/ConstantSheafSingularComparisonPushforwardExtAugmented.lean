import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPushforwardExtAugmentedTwoExt
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPushforwardExtAugmentedOne
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPushforwardExtIsoForms
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPushforwardExtConnecting

/-!
# Native sheaf cohomology of the actual pushed augmented resolution

The canonical finite-pushforward Ext map commutes with both original
resolution comparisons, as follows from its connecting-map compatibility
and its literal degree-zero global-section action.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.PushforwardExt

open CuspNormalization.SheafCohomologyResolution
open CuspNormalization.SheafCohomologyFinitePushforward

variable {X Y : TopCat.{0}} [T2Space X] (f : X ⟶ Y)
  (hf : IsClosedMap f) (hfinite : ∀ y : Y, (f ⁻¹' {y}).Finite)
  (R : AugmentedResolution (AbelianSheaf X))

/-- Native degree-two sheaf cohomology and the canonical resolution
comparison commute with the genuine finite closed pushforward map. -/
theorem augmented_h2_forward
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 2)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₂ 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0}
      (pushforwardAugmentedResolution f hf hfinite R).complex.X₁ 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0}
      (pushforwardAugmentedResolution f hf hfinite R).complex.X₁ 2)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0}
      (pushforwardAugmentedResolution f hf hfinite R).complex.X₂ 1)] :
    forwardHom f hf hfinite R.F 2 ≫
        (pushforwardAugmentedResolution f hf hfinite R).h2Iso.hom = R.h2Iso.hom := by
  let Q := pushforwardAugmentedResolution f hf hfinite R
  have : Epi R.globalConnectingTwo :=
    (AddCommGrpCat.epi_iff_surjective _).mpr R.globalConnectingTwo_surjective
  apply (cancel_epi R.globalConnectingTwo).mp
  have h₁ : R.globalConnectingTwo ≫
        (forwardHom f hf hfinite R.F 2 ≫ Q.h2Iso.hom) =
      Q.globalConnectingTwo ≫ Q.h2Iso.hom :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ Q.h2Iso.hom) (globalConnectingTwo_forward f hf hfinite R))
  exact h₁.trans (Q.h2Iso_connecting.trans R.h2Iso_connecting.symm)

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.PushforwardExt
