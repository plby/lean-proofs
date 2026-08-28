import Wikipedia.HopfProblem.SheafLerayCurveSheafComparisons
import Wikipedia.HopfProblem.SheafLerayLowDegreesCoefficientMaps

/-!
# Coefficient naturality of the all-degree Leray comparisons

The native higher-direct-image maps commute with their computations using
actual maps of injective resolutions.  The resulting comparison squares
hold in both directions on every cohomology group and on the genuine
degree-zero Ext-to-Hom term.  The chosen coefficient-resolution maps give
unconditional specializations for every coefficient-sheaf morphism.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.SheafLerayCurve

open SheafHigherDirectImage
open SheafLerayLowDegrees (coefficientResolutionMap inverse_naturality)
open CuspNormalization.SheafCohomologyFinitePushforward (integerSheaf)

variable {X Y : TopCat.{0}} (f : X ⟶ Y) {F G : AbelianSheaf X} (g : F ⟶ G)

section ResolutionMaps

variable (I : InjectiveResolution F) (J : InjectiveResolution G)
  (φ : I.cocomplex ⟶ J.cocomplex) (hφ : I.ι.f 0 ≫ φ.f 0 = g ≫ J.ι.f 0)

include hφ

/-- Naturality of the all-degree comparison for an actual map of
injective resolutions lifting the coefficient morphism. -/
@[reassoc] theorem resolutionCohomologyIso_hom_naturality (q p : ℕ) :
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology Y) p).map
        (HomologicalComplex.homologyMap (((pushforward f).mapHomologicalComplex _).map φ) q) ≫
      (resolutionCohomologyIso f J q p).hom =
    (resolutionCohomologyIso f I q p).hom ≫
      (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology Y) p).map
        ((functor f q).map g) := by
  let H := CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology Y) p
  have hr :=
    (InjectiveResolution.isoRightDerivedObj_inv_naturality g I J φ hφ (pushforward f) q).symm
  exact (H.map_comp _ _).symm.trans ((congrArg H.map hr).trans (H.map_comp _ _))

/-- The inverse comparison commutes with the same actual coefficient maps. -/
@[reassoc] theorem resolutionCohomologyIso_inv_naturality (q p : ℕ) :
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology Y) p).map
        ((functor f q).map g) ≫ (resolutionCohomologyIso f J q p).inv =
    (resolutionCohomologyIso f I q p).inv ≫
      (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology Y) p).map
        (HomologicalComplex.homologyMap (((pushforward f).mapHomologicalComplex _).map φ) q) :=
  inverse_naturality (resolutionCohomologyIso f I q p) (resolutionCohomologyIso f J q p)
    _ _ (resolutionCohomologyIso_hom_naturality f g I J φ hφ q p)

/-- The degree-zero Ext-to-Hom comparison is natural for every higher
direct image and every actual coefficient-resolution map. -/
@[reassoc] theorem resolutionExtZeroIso_hom_naturality (q : ℕ) :
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology Y) 0).map
        ((functor f q).map g) ≫ (resolutionExtZeroIso f J q).hom =
      (resolutionExtZeroIso f I q).hom ≫
        (preadditiveCoyoneda.obj (op (integerSheaf Y))).map
          (HomologicalComplex.homologyMap (((pushforward f).mapHomologicalComplex _).map φ) q) := by
  apply AddCommGrpCat.ext
  intro x
  let d := (functor f q).map g
  let rI := resolutionIso f F I q
  let rJ := resolutionIso f G J q
  let m := HomologicalComplex.homologyMap (((pushforward f).mapHomologicalComplex _).map φ) q
  have hr : d ≫ rJ.hom = rI.hom ≫ m :=
    InjectiveResolution.isoRightDerivedObj_hom_naturality g I J φ hφ (pushforward f) q
  change Ext.addEquiv₀ (CategoryTheory.Sheaf.H.map d 0 x) ≫ rJ.hom =
    (Ext.addEquiv₀ x ≫ rI.hom) ≫ m
  exact (congrArg (fun a => a ≫ rJ.hom) (CategoryTheory.Sheaf.H.addEquiv₀_map d x)).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun a => Ext.addEquiv₀ x ≫ a) hr).trans (Category.assoc _ _ _).symm))

/-- The inverse degree-zero comparison retains naturality for the
original Hom map and the actual right-derived coefficient map. -/
@[reassoc] theorem resolutionExtZeroIso_inv_naturality (q : ℕ) :
    (preadditiveCoyoneda.obj (op (integerSheaf Y))).map
        (HomologicalComplex.homologyMap (((pushforward f).mapHomologicalComplex _).map φ) q) ≫
      (resolutionExtZeroIso f J q).inv =
    (resolutionExtZeroIso f I q).inv ≫
      (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology Y) 0).map
        ((functor f q).map g) :=
  inverse_naturality (resolutionExtZeroIso f I q) (resolutionExtZeroIso f J q)
    _ _ (resolutionExtZeroIso_hom_naturality f g I J φ hφ q)

end ResolutionMaps

/-- The actual chosen coefficient-resolution map intertwines cohomology
of resolution homology and cohomology of the genuine higher direct image. -/
@[reassoc] theorem coefficient_resolutionCohomologyIso_naturality (q p : ℕ) :
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology Y) p).map
        (HomologicalComplex.homologyMap (coefficientResolutionMap f g) q) ≫
      (resolutionCohomologyIso f (injectiveResolution G) q p).hom =
    (resolutionCohomologyIso f (injectiveResolution F) q p).hom ≫
      AddCommGrpCat.ofHom (CategoryTheory.Sheaf.H.map ((functor f q).map g) p) :=
  resolutionCohomologyIso_hom_naturality f g (injectiveResolution F) (injectiveResolution G)
    (InjectiveResolution.desc g (injectiveResolution G) (injectiveResolution F))
    (InjectiveResolution.desc_commutes_zero g (injectiveResolution G) (injectiveResolution F)) q p

/-- Inverse coefficient naturality of the genuine all-degree
sheaf-cohomology comparison. -/
@[reassoc] theorem coefficient_resolutionCohomologyIso_inv_naturality (q p : ℕ) :
    AddCommGrpCat.ofHom (CategoryTheory.Sheaf.H.map ((functor f q).map g) p) ≫
      (resolutionCohomologyIso f (injectiveResolution G) q p).inv =
    (resolutionCohomologyIso f (injectiveResolution F) q p).inv ≫
      (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology Y) p).map
        (HomologicalComplex.homologyMap (coefficientResolutionMap f g) q) :=
  inverse_naturality
    (resolutionCohomologyIso f (injectiveResolution F) q p)
    (resolutionCohomologyIso f (injectiveResolution G) q p) _ _
    (coefficient_resolutionCohomologyIso_naturality f g q p)

/-- Forward coefficient naturality of the native degree-zero
Ext-to-Hom comparison, for every higher direct image. -/
@[reassoc] theorem coefficient_resolutionExtZeroIso_naturality (q : ℕ) :
    AddCommGrpCat.ofHom (CategoryTheory.Sheaf.H.map ((functor f q).map g) 0) ≫
      (resolutionExtZeroIso f (injectiveResolution G) q).hom =
    (resolutionExtZeroIso f (injectiveResolution F) q).hom ≫
      (preadditiveCoyoneda.obj (op (integerSheaf Y))).map
        (HomologicalComplex.homologyMap (coefficientResolutionMap f g) q) :=
  resolutionExtZeroIso_hom_naturality f g (injectiveResolution F) (injectiveResolution G)
    (InjectiveResolution.desc g (injectiveResolution G) (injectiveResolution F))
    (InjectiveResolution.desc_commutes_zero g (injectiveResolution G) (injectiveResolution F)) q

/-- Inverse coefficient naturality of the native degree-zero
Ext-to-Hom comparison, for every higher direct image. -/
@[reassoc] theorem coefficient_resolutionExtZeroIso_inv_naturality (q : ℕ) :
    (preadditiveCoyoneda.obj (op (integerSheaf Y))).map
        (HomologicalComplex.homologyMap (coefficientResolutionMap f g) q) ≫
      (resolutionExtZeroIso f (injectiveResolution G) q).inv =
    (resolutionExtZeroIso f (injectiveResolution F) q).inv ≫
      AddCommGrpCat.ofHom (CategoryTheory.Sheaf.H.map ((functor f q).map g) 0) :=
  inverse_naturality
    (resolutionExtZeroIso f (injectiveResolution F) q)
    (resolutionExtZeroIso f (injectiveResolution G) q) _ _
    (coefficient_resolutionExtZeroIso_naturality f g q)

end Wikipedia.HopfProblem.SheafLerayCurve
