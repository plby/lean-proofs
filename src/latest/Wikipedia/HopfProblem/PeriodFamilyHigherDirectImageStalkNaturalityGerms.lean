import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageStalkNaturalityStalk
import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageGlobalStalk

/-!
# Native coefficient maps preserve original neighborhood and global germs

The original stalk-comparison square and the native presheaf germ
square show that every actual neighborhood class transforms by its
original cohomology coefficient map. The original global germ is
therefore natural for the genuine `Sheaf.H.map` as well.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.StalkNaturality

open SheafHigherDirectImage

variable {X Y : TopCat.{0}} (f : X ⟶ Y) {F G : AbelianSheaf X} (g : F ⟶ G)
  (y : Y) (n : ℕ) (U : Opens Y) (hy : y ∈ U)

/-- The original neighborhood germ commutes with the actual
right-derived stalk map and native neighborhood cohomology map. -/
theorem derivedNeighborhoodGerm_naturality :
    FibreNeighborhood.derivedNeighborhoodGerm (F := F) f y n U hy ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map (((functor f n).map g).hom) =
      ((CategoryTheory.Sheaf.cohomologyPresheafFunctor
          (Opens.grothendieckTopology X) n).map g).app (op ((Opens.map f).obj U)) ≫
        FibreNeighborhood.derivedNeighborhoodGerm (F := G) f y n U hy := by
  let P := TopCat.Presheaf.stalkFunctor AddCommGrpCat y
  let PF := FibreNeighborhood.sourceCohomologyPresheaf (F := F) f n
  let PG := FibreNeighborhood.sourceCohomologyPresheaf (F := G) f n
  let α := Functor.whiskerLeft (Opens.map f).op
    ((CategoryTheory.Sheaf.cohomologyPresheafFunctor
      (Opens.grothendieckTopology X) n).map g)
  let eF := stalkCohomologyPresheafIso f F n y
  let eG := stalkCohomologyPresheafIso f G n y
  let d := P.map (((functor f n).map g).hom)
  have he : P.map α ≫ eG.inv = eF.inv ≫ d :=
    stalkCohomologyPresheafIso_inv_naturality f g n y
  have hg : PF.germ U y hy ≫ P.map α = α.app (op U) ≫ PG.germ U y hy :=
    TopCat.Presheaf.stalkFunctor_map_germ U y hy α
  change (PF.germ U y hy ≫ eF.inv) ≫ d = α.app (op U) ≫ (PG.germ U y hy ≫ eG.inv)
  exact (Category.assoc (PF.germ U y hy) eF.inv d).trans
    ((congrArg (fun a => PF.germ U y hy ≫ a) he.symm).trans
      ((Category.assoc (PF.germ U y hy) (P.map α) eG.inv).symm.trans
        ((congrArg (fun a => a ≫ eG.inv) hg).trans
          (Category.assoc (α.app (op U)) (PG.germ U y hy) eG.inv))))

/-- Pointwise form for an arbitrary original neighborhood cohomology
class, without requiring a global representative. -/
theorem derivedNeighborhoodGerm_naturality_apply
    (a : CategoryTheory.Sheaf.H'.{0} F n ((Opens.map f).obj U)) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map (((functor f n).map g).hom)
        (FibreNeighborhood.derivedNeighborhoodGerm (F := F) f y n U hy a) =
      FibreNeighborhood.derivedNeighborhoodGerm (F := G) f y n U hy
        (((CategoryTheory.Sheaf.cohomologyPresheafFunctor
          (Opens.grothendieckTopology X) n).map g).app (op ((Opens.map f).obj U)) a) :=
  ConcreteCategory.congr_hom (derivedNeighborhoodGerm_naturality f g y n U hy) a

/-- The actual native derived-stalk map carries an original global
class germ to the germ of its actual cohomology coefficient image. -/
theorem globalStalkClass_naturality (a : CategoryTheory.Sheaf.H.{0} F n) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map (((functor f n).map g).hom)
        (GlobalRestriction.globalStalkClass f F y n a) =
      GlobalRestriction.globalStalkClass f G y n (CategoryTheory.Sheaf.H.map g n a) :=
  (derivedNeighborhoodGerm_naturality_apply f g y n ⊤ (by trivial)
    (GlobalRestriction.restrictionMap F ((Opens.map f).obj ⊤) n a)).trans
      (congrArg (FibreNeighborhood.derivedNeighborhoodGerm (F := G) f y n ⊤ (by trivial))
        (GlobalRestriction.restrictionMap_naturality g ((Opens.map f).obj ⊤) n a))

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.StalkNaturality
