import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPushforwardExtAugmentedBasic

/-!
# Actual global connecting representatives under finite pushforward
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.PushforwardExt

open CuspNormalization.SheafCohomologyResolution
open CuspNormalization.SheafCohomologyFinitePushforward

variable {X Y : TopCat.{0}} [T2Space X] (f : X ⟶ Y)
  (hf : IsClosedMap f) (hfinite : ∀ y : Y, (f ⁻¹' {y}).Finite)

/-- The literal global-section representative gives the same
native Ext-zero class after finite pushforward. -/
theorem h0Global_forward_inv (F : AbelianSheaf X) :
    (h0GlobalIso F).inv ≫ forwardHom f hf hfinite F 0 =
      (h0GlobalIso ((pushforward f).obj F)).inv := by
  apply (cancel_mono (h0GlobalIso ((pushforward f).obj F)).hom).mp
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => (h0GlobalIso F).inv ≫ k) (h0Global_forward f hf hfinite F)).trans
      ((h0GlobalIso F).inv_hom_id.trans
        (h0GlobalIso ((pushforward f).obj F)).inv_hom_id.symm))

/-- The native double connecting class of a literal global section
is preserved by the original finite-pushforward cohomology map. -/
theorem globalConnectingTwo_forward (R : AugmentedResolution (AbelianSheaf X)) :
    R.globalConnectingTwo ≫ forwardHom f hf hfinite R.F 2 =
      (pushforwardAugmentedResolution f hf hfinite R).globalConnectingTwo := by
  let : PreservesFiniteLimits (pushforward f) :=
    (pushforward_preservesFiniteLimitsAndColimits f hf hfinite).1
  let : PreservesFiniteColimits (pushforward f) :=
    pushforward_preservesFiniteColimits f hf hfinite
  let Q := pushforwardAugmentedResolution f hf hfinite R
  have h : AddCommGrpCat.ofHom (R.connectingTwo (unitSheaf X)) ≫
        forwardHom f hf hfinite R.F 2 =
      forwardHom f hf hfinite R.complex.X₃ 0 ≫
        AddCommGrpCat.ofHom (Q.connectingTwo (unitSheaf Y)) :=
    (PushforwardExtFunctor.connectingTwo_naturality
      (pushforward f) (integerUnit f) R).symm
  change ((h0GlobalIso R.complex.X₃).inv ≫
      AddCommGrpCat.ofHom (R.connectingTwo (unitSheaf X))) ≫
        forwardHom f hf hfinite R.F 2 =
    (h0GlobalIso Q.complex.X₃).inv ≫ AddCommGrpCat.ofHom (Q.connectingTwo (unitSheaf Y))
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => (h0GlobalIso R.complex.X₃).inv ≫ k) h).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun k => k ≫ AddCommGrpCat.ofHom (Q.connectingTwo (unitSheaf Y)))
          (h0Global_forward_inv f hf hfinite R.complex.X₃))))

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.PushforwardExt
