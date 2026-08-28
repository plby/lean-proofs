import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPushforwardExtResolution

/-!
# The native pushforward comparison as actual group morphisms
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.PushforwardExt

open CuspNormalization.SheafCohomologyResolution
open CuspNormalization.SheafCohomologyFinitePushforward

variable {X Y : TopCat.{0}} [T2Space X] (f : X ⟶ Y)
  (hf : IsClosedMap f) (hfinite : ∀ y : Y, (f ⁻¹' {y}).Finite)

/-- The original exact-pushforward map of native sheaf cohomology,
bundled as a morphism of its original abelian groups. -/
def forwardHom (F : AbelianSheaf X) (n : ℕ) :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} F n) ⟶
      AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} ((pushforward f).obj F) n) :=
  AddCommGrpCat.ofHom (cohomologyForward f hf hfinite F n)

/-- In degree zero the native Ext comparison is literally the
identity on the actual global section. -/
theorem h0Global_forward (F : AbelianSheaf X) :
    forwardHom f hf hfinite F 0 ≫ (h0GlobalIso ((pushforward f).obj F)).hom =
      (h0GlobalIso F).hom := by
  ext e
  exact cohomologyForward_zero_global f hf hfinite F e

/-- The original native comparison is natural for actual sheaf maps. -/
theorem forwardHom_naturality {F G : AbelianSheaf X} (g : F ⟶ G) (n : ℕ) :
    (CategoryTheory.Sheaf.functorH _ n).map g ≫ forwardHom f hf hfinite G n =
      forwardHom f hf hfinite F n ≫
        (CategoryTheory.Sheaf.functorH _ n).map ((pushforward f).map g) := by
  ext e
  exact cohomologyForward_naturality f hf hfinite g n e

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.PushforwardExt
