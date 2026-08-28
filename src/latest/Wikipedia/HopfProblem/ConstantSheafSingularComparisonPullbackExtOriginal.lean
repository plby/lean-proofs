import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPullbackExtBasic
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonOriginalConstants
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonConcreteCoefficients

/-!
# The original complex constant-sheaf cohomology pullback

This map starts with the manuscript's original additive complex sheaf
and its original ring-sheaf pullback map. The native finite-pushforward
cohomology equivalence gives the original-space Ext pullback. The
already proved original/native constant-sheaf square identifies this
map with native constant pullback in every degree.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.PullbackExt

open CuspNormalization.SheafConstants
open CuspNormalization.SheafCohomologyFinitePushforward

variable {X Y : TopCat.{0}} [T2Space X] (f : X ⟶ Y)
  (hf : IsClosedMap f) (hfinite : ∀ y : Y, (f ⁻¹' {y}).Finite)

/-- Genuine Ext pullback using the original additive image of the
manuscript's constant complex ring sheaf and original pullback map. -/
def complexCohomologyPullback (n : ℕ) :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} (complexAdditiveSheaf Y) n) ⟶
      AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} (complexAdditiveSheaf X) n) :=
  AddCommGrpCat.ofHom
    ((cohomologyEquiv f hf hfinite (complexAdditiveSheaf X) n).toAddMonoidHom.comp
      (CategoryTheory.Sheaf.H.map.{0} (additivePullbackMap f) n))

/-- The comparison with native constants uses the actual sheaf
isomorphism and commutes with the original Ext pullback, in every degree. -/
theorem complexCohomologyPullback_native (n : ℕ) :
    complexCohomologyPullback f hf hfinite n ≫
      (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n).map
        (complexAdditiveSheafIso X).hom =
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology Y) n).map
        (complexAdditiveSheafIso Y).hom ≫
      constantCohomologyPullback f hf hfinite (AddCommGrpCat.of ℂ) n := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro ξ
  let E := CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology Y) n
  have hmap : E.map (additivePullbackMap f) ≫
      E.map ((TopCat.Sheaf.pushforward AddCommGrpCat f).map
        (complexAdditiveSheafIso X).hom) =
      E.map (complexAdditiveSheafIso Y).hom ≫
        E.map (PullbackSheaf.constantPullback f (AddCommGrpCat.of ℂ)) :=
    (E.map_comp _ _).symm.trans
      ((E.congr_map (OriginalConstants.additivePullbackMap_complexAdditiveSheafIso f)).trans
        (E.map_comp _ _))
  have hξ := ConcreteCategory.congr_hom hmap ξ
  have hnat := cohomologyEquiv_naturality f hf hfinite (complexAdditiveSheafIso X).hom n
    (CategoryTheory.Sheaf.H.map.{0} (additivePullbackMap f) n ξ)
  exact hnat.symm.trans
    (congrArg (cohomologyEquiv f hf hfinite
      (ConstantSheafFirstCohomology.Constant.sheaf X (AddCommGrpCat.of ℂ)) n) hξ)

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.PullbackExt
