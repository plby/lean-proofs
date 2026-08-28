import Wikipedia.HopfProblem.ConstantSheafSingularComparisonLowDegrees
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCoefficientGlobal

/-!
# Genuine Ext--singular comparison is natural in the coefficient group

The source maps are Mathlib's actual constant-sheaf maps and native
`Sheaf.H` maps. The target maps are literal postcomposition on original
singular cochains. Naturality of the actual acyclic resolution and of the
native global unit proves the comparison square in degrees one and two.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

variable (X : TopCat.{0}) {A B : AddCommGrpCat.{0}}

/-- The genuine coefficient map is a map of the actual augmented
singular cochain sheaf resolutions. -/
def singularSheafResolutionCoefficientHom (hLC : LocallyContractibleSpace X)
    (α : A ⟶ B) :
    (singularSheafResolution X A hLC).Hom (singularSheafResolution X B hLC) where
  augmentation := (CategoryTheory.constantSheaf
    (Opens.grothendieckTopology X) AddCommGrpCat.{0}).map α
  complex := sheafCoefficientComplexMap X α
  comm := sheafAugmentation_coefficient_naturality X α

variable [CompactSpace X] [T2Space X]

/-- Native degree-one Ext-to-global-sections comparison respects the
original coefficient morphism. -/
theorem constantSheafGlobalH1Iso_coefficient_naturality
    (hLC : LocallyContractibleSpace X) (α : A ⟶ B) :
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 1).map
        ((CategoryTheory.constantSheaf (Opens.grothendieckTopology X)
          AddCommGrpCat.{0}).map α) ≫ (constantSheafGlobalH1Iso X B hLC).hom =
      (constantSheafGlobalH1Iso X A hLC).hom ≫
        HomologicalComplex.homologyMap (globalSheafCoefficientMap X α) 1 := by
  let R := singularSheafResolution X A hLC
  let S := singularSheafResolution X B hLC
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 1) :=
    FineCochains.cochainSheaf_higher_subsingleton X A 0 0
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (S.K.X 0) 1) :=
    FineCochains.cochainSheaf_higher_subsingleton X B 0 0
  exact (singularSheafResolutionCoefficientHom X hLC α).h1Iso_naturality

/-- The same native coefficient naturality in degree two. -/
theorem constantSheafGlobalH2Iso_coefficient_naturality
    (hLC : LocallyContractibleSpace X) (α : A ⟶ B) :
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 2).map
        ((CategoryTheory.constantSheaf (Opens.grothendieckTopology X)
          AddCommGrpCat.{0}).map α) ≫ (constantSheafGlobalH2Iso X B hLC).hom =
      (constantSheafGlobalH2Iso X A hLC).hom ≫
        HomologicalComplex.homologyMap (globalSheafCoefficientMap X α) 2 := by
  let R := singularSheafResolution X A hLC
  let S := singularSheafResolution X B hLC
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 1) :=
    FineCochains.cochainSheaf_higher_subsingleton X A 0 0
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 2) :=
    FineCochains.cochainSheaf_higher_subsingleton X A 0 1
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 1) 1) :=
    FineCochains.cochainSheaf_higher_subsingleton X A 1 0
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (S.K.X 0) 1) :=
    FineCochains.cochainSheaf_higher_subsingleton X B 0 0
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (S.K.X 0) 2) :=
    FineCochains.cochainSheaf_higher_subsingleton X B 0 1
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (S.K.X 1) 1) :=
    FineCochains.cochainSheaf_higher_subsingleton X B 1 0
  exact (singularSheafResolutionCoefficientHom X hLC α).h2Iso_naturality

private theorem comparison_naturality_of_mono
    {C : Type*} [Category C] {H H' S S' G G' : C}
    (e : H ⟶ S) (e' : H' ⟶ S') (u : S ⟶ G) (u' : S' ⟶ G') [Mono u']
    (r : H ⟶ G) (r' : H' ⟶ G') (a : H ⟶ H') (b : S ⟶ S') (c : G ⟶ G')
    (he : e ≫ u = r) (he' : e' ≫ u' = r')
    (hr : a ≫ r' = r ≫ c) (hu : u ≫ c = b ≫ u') :
    a ≫ e' = e ≫ b := by
  apply (cancel_mono u').mp
  calc
    (a ≫ e') ≫ u' = a ≫ r' := by rw [Category.assoc, he']
    _ = r ≫ c := hr
    _ = (e ≫ u) ≫ c := by rw [he]
    _ = e ≫ (b ≫ u') := by rw [Category.assoc, hu]
    _ = (e ≫ b) ≫ u' := (Category.assoc _ _ _).symm

/-- The canonical H¹ Ext--singular isomorphism is natural for every
actual homomorphism of coefficient groups, including `ℤ → ℂ`. -/
theorem constantSheafH1Iso_coefficient_naturality
    (hLC : LocallyContractibleSpace X) (α : A ⟶ B) :
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 1).map
        ((CategoryTheory.constantSheaf (Opens.grothendieckTopology X)
          AddCommGrpCat.{0}).map α) ≫ (constantSheafH1Iso X B hLC).hom =
      (constantSheafH1Iso X A hLC).hom ≫
        HomologicalComplex.homologyMap (coefficientMap X α) 1 := by
  let := globalCochainComparison_homology_isIso X B 0
  exact comparison_naturality_of_mono
    (constantSheafH1Iso X A hLC).hom (constantSheafH1Iso X B hLC).hom
    (HomologicalComplex.homologyMap (globalCochainComparison X A) 1)
    (HomologicalComplex.homologyMap (globalCochainComparison X B) 1)
    (constantSheafGlobalH1Iso X A hLC).hom (constantSheafGlobalH1Iso X B hLC).hom
    ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 1).map
      ((CategoryTheory.constantSheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{0}).map α))
    (HomologicalComplex.homologyMap (coefficientMap X α) 1)
    (HomologicalComplex.homologyMap (globalSheafCoefficientMap X α) 1)
    (constantSheafH1Iso_global X A hLC) (constantSheafH1Iso_global X B hLC)
    (constantSheafGlobalH1Iso_coefficient_naturality X hLC α)
    (globalCochainComparison_homology_coefficient_naturality X α 1)

/-- The same genuine coefficient naturality for the canonical H²
Ext--singular comparison. -/
theorem constantSheafH2Iso_coefficient_naturality
    (hLC : LocallyContractibleSpace X) (α : A ⟶ B) :
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 2).map
        ((CategoryTheory.constantSheaf (Opens.grothendieckTopology X)
          AddCommGrpCat.{0}).map α) ≫ (constantSheafH2Iso X B hLC).hom =
      (constantSheafH2Iso X A hLC).hom ≫
        HomologicalComplex.homologyMap (coefficientMap X α) 2 := by
  let := globalCochainComparison_homology_isIso X B 1
  exact comparison_naturality_of_mono
    (constantSheafH2Iso X A hLC).hom (constantSheafH2Iso X B hLC).hom
    (HomologicalComplex.homologyMap (globalCochainComparison X A) 2)
    (HomologicalComplex.homologyMap (globalCochainComparison X B) 2)
    (constantSheafGlobalH2Iso X A hLC).hom (constantSheafGlobalH2Iso X B hLC).hom
    ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 2).map
      ((CategoryTheory.constantSheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{0}).map α))
    (HomologicalComplex.homologyMap (coefficientMap X α) 2)
    (HomologicalComplex.homologyMap (globalSheafCoefficientMap X α) 2)
    (constantSheafH2Iso_global X A hLC) (constantSheafH2Iso_global X B hLC)
    (constantSheafGlobalH2Iso_coefficient_naturality X hLC α)
    (globalCochainComparison_homology_coefficient_naturality X α 2)

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
