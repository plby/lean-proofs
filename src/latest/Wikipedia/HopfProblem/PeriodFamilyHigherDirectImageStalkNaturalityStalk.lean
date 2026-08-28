import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageStalkNaturalityResolution
import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageStalkNaturalityCohomology
import Wikipedia.HopfProblem.SheafHigherDirectImageStalk
import Wikipedia.HopfProblem.SheafLerayLowDegreesTransportNaturality

/-!
# Coefficient naturality of the original higher-direct-image stalk comparison

The native lift between the chosen injective resolutions gives the
actual right-derived coefficient map and the original Ext coefficient
map. The proved resolution squares show that the existing stalk
comparison intertwines them in every degree. Its components are not
changed, and the left map is never defined by transport.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.StalkNaturality

open SheafHigherDirectImage

variable {X Y : TopCat.{0}} (f : X ⟶ Y) {F G : AbelianSheaf X} (g : F ⟶ G)

/-- The existing stalk comparison is natural for the native
right-derived coefficient map and the original cohomology-presheaf map. -/
theorem stalkCohomologyPresheafIso_hom_naturality (n : ℕ) (y : Y) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map (((functor f n).map g).hom) ≫
        (stalkCohomologyPresheafIso f G n y).hom =
      (stalkCohomologyPresheafIso f F n y).hom ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
          (Functor.whiskerLeft (Opens.map f).op
            ((CategoryTheory.Sheaf.cohomologyPresheafFunctor
              (Opens.grothendieckTopology X) n).map g)) := by
  let I : InjectiveResolution F := injectiveResolution F
  let J : InjectiveResolution G := injectiveResolution G
  let φ : I.cocomplex ⟶ J.cocomplex := InjectiveResolution.desc g J I
  have hφ : I.ι.f 0 ≫ φ.f 0 = g ≫ J.ι.f 0 :=
    InjectiveResolution.desc_commutes_zero g J I
  let P := TopCat.Presheaf.stalkFunctor AddCommGrpCat y
  let rI := resolutionStalkIso f I n y
  let rJ := resolutionStalkIso f J n y
  let cI := pushedResolutionCohomologyPresheafIso f I n
  let cJ := pushedResolutionCohomologyPresheafIso f J n
  let d := P.map (((functor f n).map g).hom)
  let m := HomologicalComplex.homologyMap
    (((TopCat.Sheaf.forget AddCommGrpCat Y).mapHomologicalComplex _).map
      (((pushforward f).mapHomologicalComplex _).map φ)) n
  let a := Functor.whiskerLeft (Opens.map f).op
    ((CategoryTheory.Sheaf.cohomologyPresheafFunctor
      (Opens.grothendieckTopology X) n).map g)
  have hr : d ≫ rJ.hom = rI.hom ≫ P.map m :=
    resolutionStalkIso_hom_coefficient_naturality f g I J φ hφ n y
  have hc : m ≫ cJ.hom = cI.hom ≫ a :=
    pushedResolutionCohomologyPresheafIso_hom_naturality_of_lift I J g φ hφ f n
  have hPc : P.map m ≫ P.map cJ.hom = P.map cI.hom ≫ P.map a :=
    (P.map_comp _ _).symm.trans ((congrArg P.map hc).trans (P.map_comp _ _))
  change d ≫ (rJ.hom ≫ P.map cJ.hom) = (rI.hom ≫ P.map cI.hom) ≫ P.map a
  exact (Category.assoc d rJ.hom (P.map cJ.hom)).symm.trans
    ((congrArg (fun k => k ≫ P.map cJ.hom) hr).trans
      ((Category.assoc rI.hom (P.map m) (P.map cJ.hom)).trans
        ((congrArg (fun k => rI.hom ≫ k) hPc).trans
          (Category.assoc rI.hom (P.map cI.hom) (P.map a)).symm)))

/-- The inverse original comparison also intertwines the actual
cohomology coefficient map with the native right-derived coefficient map. -/
theorem stalkCohomologyPresheafIso_inv_naturality (n : ℕ) (y : Y) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
        (Functor.whiskerLeft (Opens.map f).op
          ((CategoryTheory.Sheaf.cohomologyPresheafFunctor
            (Opens.grothendieckTopology X) n).map g)) ≫
      (stalkCohomologyPresheafIso f G n y).inv =
    (stalkCohomologyPresheafIso f F n y).inv ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map (((functor f n).map g).hom) :=
  SheafLerayLowDegrees.inverse_naturality
    (stalkCohomologyPresheafIso f F n y) (stalkCohomologyPresheafIso f G n y)
    _ _ (stalkCohomologyPresheafIso_hom_naturality f g n y)

/-- Pointwise naturality for every actual element of the genuine
higher-direct-image stalk, not only for chosen global classes. -/
theorem stalkCohomologyPresheafIso_hom_naturality_apply (n : ℕ) (y : Y)
    (s : ↥(TopCat.Presheaf.stalk (sheaf f F n).obj y)) :
    (stalkCohomologyPresheafIso f G n y).hom
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map (((functor f n).map g).hom) s) =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
        (Functor.whiskerLeft (Opens.map f).op
          ((CategoryTheory.Sheaf.cohomologyPresheafFunctor
            (Opens.grothendieckTopology X) n).map g))
        ((stalkCohomologyPresheafIso f F n y).hom s) :=
  ConcreteCategory.congr_hom (stalkCohomologyPresheafIso_hom_naturality f g n y) s

/-- The same original component isomorphisms form a genuine natural
isomorphism from the native derived-stalk functor to the original
cohomology-presheaf stalk functor. -/
def stalkCohomologyPresheafNatIso (n : ℕ) (y : Y) :
    functor f n ⋙ TopCat.Sheaf.forget AddCommGrpCat Y ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat y ≅
      CategoryTheory.Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n ⋙
        presheafPushforward f ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat y :=
  NatIso.ofComponents (fun F => stalkCohomologyPresheafIso f F n y)
    (fun g => stalkCohomologyPresheafIso_hom_naturality f g n y)

@[simp] theorem stalkCohomologyPresheafNatIso_hom_app (n : ℕ) (y : Y) (F : AbelianSheaf X) :
    (stalkCohomologyPresheafNatIso f n y).hom.app F =
      (stalkCohomologyPresheafIso f F n y).hom := rfl

@[simp] theorem stalkCohomologyPresheafNatIso_inv_app (n : ℕ) (y : Y) (F : AbelianSheaf X) :
    (stalkCohomologyPresheafNatIso f n y).inv.app F =
      (stalkCohomologyPresheafIso f F n y).inv := rfl

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.StalkNaturality
