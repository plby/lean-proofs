import Wikipedia.HopfProblem.SheafHigherDirectImageResolution

/-!
# Native derived coefficient maps and actual resolution stalks

An actual morphism of injective resolutions computes the native
right-derived coefficient map. Applying the original stalk functor and
the existing homology comparison preserves this naturality square.
No coefficient action is defined by transport through an isomorphism.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.StalkNaturality

open SheafHigherDirectImage

variable {X Y : TopCat.{0}} (f : X ⟶ Y) {F G : AbelianSheaf X}
  (g : F ⟶ G) (I : InjectiveResolution F) (J : InjectiveResolution G)
  (φ : I.cocomplex ⟶ J.cocomplex) (hφ : I.ι.f 0 ≫ φ.f 0 = g ≫ J.ι.f 0)

include hφ in
/-- The original resolution-stalk comparison commutes with the actual
right-derived coefficient map and actual resolution homology map. -/
theorem resolutionStalkIso_hom_coefficient_naturality (n : ℕ) (y : Y) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map (((functor f n).map g).hom) ≫
        (resolutionStalkIso f J n y).hom =
      (resolutionStalkIso f I n y).hom ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
          (HomologicalComplex.homologyMap
            (((TopCat.Sheaf.forget AddCommGrpCat Y).mapHomologicalComplex _).map
              (((pushforward f).mapHomologicalComplex _).map φ)) n) := by
  let P := TopCat.Presheaf.stalkFunctor AddCommGrpCat y
  let Q := TopCat.Sheaf.forget AddCommGrpCat Y ⋙ P
  let ψ := ((pushforward f).mapHomologicalComplex _).map φ
  let rI := resolutionIso f F I n
  let rJ := resolutionIso f G J n
  let sI := stalkHomologyPresheafIso y (pushedResolution f I) n
  let sJ := stalkHomologyPresheafIso y (pushedResolution f J) n
  let m := HomologicalComplex.homologyMap ψ n
  let m' := HomologicalComplex.homologyMap
    (((TopCat.Sheaf.forget AddCommGrpCat Y).mapHomologicalComplex _).map ψ) n
  have hr : (functor f n).map g ≫ rJ.hom = rI.hom ≫ m :=
    InjectiveResolution.isoRightDerivedObj_hom_naturality g I J φ hφ (pushforward f) n
  have hQr : Q.map ((functor f n).map g) ≫ Q.map rJ.hom =
      Q.map rI.hom ≫ Q.map m :=
    (Q.map_comp _ _).symm.trans ((congrArg Q.map hr).trans (Q.map_comp _ _))
  have hs : Q.map m ≫ sJ.hom = sI.hom ≫ P.map m' :=
    stalkHomologyPresheafIso_hom_naturality y ψ n
  change Q.map ((functor f n).map g) ≫ (Q.map rJ.hom ≫ sJ.hom) =
    (Q.map rI.hom ≫ sI.hom) ≫ P.map m'
  exact (Category.assoc (Q.map ((functor f n).map g)) (Q.map rJ.hom) sJ.hom).symm.trans
    ((congrArg (fun a => a ≫ sJ.hom) hQr).trans
      ((Category.assoc (Q.map rI.hom) (Q.map m) sJ.hom).trans
        ((congrArg (fun a => Q.map rI.hom ≫ a) hs).trans
          (Category.assoc (Q.map rI.hom) sI.hom (P.map m')).symm)))

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.StalkNaturality
