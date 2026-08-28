import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPullbackSheafBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyFinitePushforwardGlobal

/-!
# The native integer map underlying cohomological pullback

The constant-sheaf pullback obtained from actual raw coefficient values
is the original integer-sheaf unit already used in the native Ext and
pushforward comparisons. The comparison is checked on the original
global unit value of one, through the actual representing equivalence.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.PullbackSheaf

open CuspNormalization.SheafCohomologyFinitePushforward

variable {X Y : TopCat.{0}}

/-- The actual global-section representing equivalence evaluates an
integer-sheaf morphism at the original constant section of value one. -/
theorem homGlobalEquiv_apply_one (F : AbelianSheaf X) (h : integerSheaf X ⟶ F) :
    homGlobalEquiv X F h =
      h.hom.app (op ⊤)
        ((ConstantSheafFirstCohomology.Constant.unit X
          (AddCommGrpCat.of (ULift.{0} ℤ))).app (op ⊤) ⟨1⟩) := by
  rfl

/-- The constructed constant pullback is literally the native
integer-sheaf unit used by the actual Ext pushforward comparison. -/
theorem constantPullback_integer_eq (f : X ⟶ Y) :
    constantPullback f (AddCommGrpCat.of (ULift.{0} ℤ)) = integerUnit f := by
  apply (homGlobalEquiv Y ((pushforward f).obj (integerSheaf X))).injective
  have hleft := homGlobalEquiv_apply_one ((pushforward f).obj (integerSheaf X))
    (constantPullback f (AddCommGrpCat.of (ULift.{0} ℤ)))
  have hunit := constantPullback_app_unit f (AddCommGrpCat.of (ULift.{0} ℤ)) ⊤ ⟨1⟩
  have hid := homGlobalEquiv_apply_one (integerSheaf X) (𝟙 (integerSheaf X))
  have hright := homPushforwardEquiv_global f (integerSheaf X) (𝟙 (integerSheaf X))
  exact hleft.trans (hunit.trans (hid.symm.trans hright.symm))

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.PullbackSheaf
