import Wikipedia.HopfProblem.ConstantSheafSingularComparisonLowDegrees
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPullbackSheafGlobal

/-!
# The original comparison square detected on actual global cohomology

The singular-to-global-sheaf comparison is natural for every continuous
map. Its proved isomorphisms therefore turn compatibility with actual
global sections into compatibility with original singular cohomology.
This is a categorical helper for the genuine Ext pullback constructed
independently for finite closed maps.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.PullbackExt

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (A : AddCommGrpCat.{0})

/-- The actual singular-to-global-sheaf comparison square, on native
homology and for the original continuous-map pullbacks. -/
@[reassoc]
theorem globalCochainComparison_homology_naturality (n : ℕ) :
    HomologicalComplex.homologyMap (singularPullback A f.hom) n ≫
      HomologicalComplex.homologyMap (globalCochainComparison X A) n =
    HomologicalComplex.homologyMap (globalCochainComparison Y A) n ≫
      HomologicalComplex.homologyMap (PullbackSheaf.globalSheafPullback f A) n :=
  (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    ((congrArg (fun g => HomologicalComplex.homologyMap g n)
      (PullbackSheaf.globalCochainComparison_naturality f A)).trans
        (HomologicalComplex.homologyMap_comp _ _ n))

private theorem compare_naturality {C : Type*} [Category C]
    {H H' S S' G G' : C}
    (e : H ⟶ S) (e' : H' ⟶ S') (u : S ⟶ G) (u' : S' ⟶ G') [Mono u']
    (r : H ⟶ G) (r' : H' ⟶ G') (a : H ⟶ H') (b : S ⟶ S') (c : G ⟶ G')
    (he : e ≫ u = r) (he' : e' ≫ u' = r')
    (hr : a ≫ r' = r ≫ c) (hu : b ≫ u' = u ≫ c) :
    a ≫ e' = e ≫ b := by
  apply (cancel_mono u').mp
  calc
    (a ≫ e') ≫ u' = a ≫ r' := by rw [Category.assoc, he']
    _ = r ≫ c := hr
    _ = (e ≫ u) ≫ c := by rw [he]
    _ = e ≫ (b ≫ u') := by rw [Category.assoc, hu]
    _ = (e ≫ b) ≫ u' := (Category.assoc _ _ _).symm

variable [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]

/-- In degree one the actual global-unit comparison detects the exact
continuous-map naturality square of a given genuine Ext morphism. -/
theorem h1_naturality_of_global
    (hX : LocallyContractibleSpace X) (hY : LocallyContractibleSpace Y)
    (a : AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
      (ConstantSheafFirstCohomology.Constant.sheaf Y A) 1) ⟶
      AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
        (ConstantSheafFirstCohomology.Constant.sheaf X A) 1))
    (h : a ≫ (constantSheafGlobalH1Iso X A hX).hom =
      (constantSheafGlobalH1Iso Y A hY).hom ≫
        HomologicalComplex.homologyMap (PullbackSheaf.globalSheafPullback f A) 1) :
    a ≫ (constantSheafH1Iso X A hX).hom =
      (constantSheafH1Iso Y A hY).hom ≫
        HomologicalComplex.homologyMap (singularPullback A f.hom) 1 := by
  let := globalCochainComparison_homology_isIso X A 0
  exact compare_naturality
    (constantSheafH1Iso Y A hY).hom (constantSheafH1Iso X A hX).hom
    (HomologicalComplex.homologyMap (globalCochainComparison Y A) 1)
    (HomologicalComplex.homologyMap (globalCochainComparison X A) 1)
    (constantSheafGlobalH1Iso Y A hY).hom (constantSheafGlobalH1Iso X A hX).hom
    a (HomologicalComplex.homologyMap (singularPullback A f.hom) 1)
    (HomologicalComplex.homologyMap (PullbackSheaf.globalSheafPullback f A) 1)
    (constantSheafH1Iso_global Y A hY) (constantSheafH1Iso_global X A hX) h
    (globalCochainComparison_homology_naturality f A 1)

/-- The same native-global comparison criterion in degree two. -/
theorem h2_naturality_of_global
    (hX : LocallyContractibleSpace X) (hY : LocallyContractibleSpace Y)
    (a : AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
      (ConstantSheafFirstCohomology.Constant.sheaf Y A) 2) ⟶
      AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
        (ConstantSheafFirstCohomology.Constant.sheaf X A) 2))
    (h : a ≫ (constantSheafGlobalH2Iso X A hX).hom =
      (constantSheafGlobalH2Iso Y A hY).hom ≫
        HomologicalComplex.homologyMap (PullbackSheaf.globalSheafPullback f A) 2) :
    a ≫ (constantSheafH2Iso X A hX).hom =
      (constantSheafH2Iso Y A hY).hom ≫
        HomologicalComplex.homologyMap (singularPullback A f.hom) 2 := by
  let := globalCochainComparison_homology_isIso X A 1
  exact compare_naturality
    (constantSheafH2Iso Y A hY).hom (constantSheafH2Iso X A hX).hom
    (HomologicalComplex.homologyMap (globalCochainComparison Y A) 2)
    (HomologicalComplex.homologyMap (globalCochainComparison X A) 2)
    (constantSheafGlobalH2Iso Y A hY).hom (constantSheafGlobalH2Iso X A hX).hom
    a (HomologicalComplex.homologyMap (singularPullback A f.hom) 2)
    (HomologicalComplex.homologyMap (PullbackSheaf.globalSheafPullback f A) 2)
    (constantSheafH2Iso_global Y A hY) (constantSheafH2Iso_global X A hX) h
    (globalCochainComparison_homology_naturality f A 2)

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.PullbackExt
