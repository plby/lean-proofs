import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPushforwardExtBasic
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPullbackSheafGlobal
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonResolution

/-!
# The genuine constant-sheaf cohomology pullback for finite closed maps

The map uses the actual constant-sheaf morphism into the original
pushforward, followed by the already proved native finite-pushforward
cohomology equivalence. It is defined solely in native sheaf `Ext`,
independently of singular cohomology and of its comparison isomorphisms.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.PullbackExt

open CuspNormalization.SheafCohomologyFinitePushforward

variable {X Y : TopCat.{0}} [T2Space X] (f : X ⟶ Y)
  (hf : IsClosedMap f) (hfinite : ∀ y : Y, (f ⁻¹' {y}).Finite)
  (A : AddCommGrpCat.{0})

/-- Native constant-sheaf cohomology pullback, defined using only the
original constant morphism and genuine finite-pushforward equivalence. -/
def constantCohomologyPullback (n : ℕ) :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
      (ConstantSheafFirstCohomology.Constant.sheaf Y A) n) ⟶
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
      (ConstantSheafFirstCohomology.Constant.sheaf X A) n) :=
  AddCommGrpCat.ofHom
    ((cohomologyEquiv f hf hfinite
      (ConstantSheafFirstCohomology.Constant.sheaf X A) n).toAddMonoidHom.comp
        (CategoryTheory.Sheaf.H.map.{0} (PullbackSheaf.constantPullback f A) n))

/-- The forward finite-pushforward comparison cancels precisely the
existing inverse equivalence used in the native pullback. -/
@[reassoc]
theorem constantCohomologyPullback_forward (n : ℕ) :
    constantCohomologyPullback f hf hfinite A n ≫
      PushforwardExt.forwardHom f hf hfinite
        (ConstantSheafFirstCohomology.Constant.sheaf X A) n =
      (CategoryTheory.Sheaf.functorH _ n).map (PullbackSheaf.constantPullback f A) := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro ξ
  exact cohomologyForward_equiv f hf hfinite
    (ConstantSheafFirstCohomology.Constant.sheaf X A) n
    (CategoryTheory.Sheaf.H.map.{0} (PullbackSheaf.constantPullback f A) n ξ)

/-- Actual continuous cochain pullback is a genuine augmented map into
the native exact pushforward of the actual singular sheaf resolution. -/
def resolutionPullback (hX : LocallyContractibleSpace X)
    (hY : LocallyContractibleSpace Y) :
    (singularSheafResolution Y A hY).Hom
      (PushforwardExt.pushforwardResolution f hf hfinite (singularSheafResolution X A hX)) where
  augmentation := PullbackSheaf.constantPullback f A
  complex := PullbackSheaf.cochainPullbackComplex f A
  comm := (PullbackSheaf.cochainPullback_augmentation f A).symm

/-- On global sections this is the original sheaf pullback cochain map,
with only the literal top-open identification of native pushforward. -/
theorem resolutionPullback_globalMap (hX : LocallyContractibleSpace X)
    (hY : LocallyContractibleSpace Y) :
    (resolutionPullback f hf hfinite A hX hY).globalMap ≫
      (PushforwardExt.globalCochainIso f hf hfinite
        (singularSheafResolution X A hX)).inv =
      PullbackSheaf.globalSheafPullback f A := by
  apply HomologicalComplex.Hom.ext
  funext n
  rfl

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.PullbackExt
