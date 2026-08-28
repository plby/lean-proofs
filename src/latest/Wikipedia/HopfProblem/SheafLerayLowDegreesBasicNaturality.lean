import Wikipedia.HopfProblem.SheafLerayLowDegreesBasic

/-!
# Naturality of the native Leray term comparisons

An actual map of injective resolutions inducing a given coefficient
map gives the corresponding actual maps of higher direct images.
The degree-zero and degree-one comparisons commute with these maps.
This is the coefficient naturality needed, in particular, for scalar
endomorphisms of holomorphic-function sheaves.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.SheafLerayLowDegrees

open SheafHigherDirectImage
open CuspNormalization.SheafCohomologyFinitePushforward (integerSheaf)

variable {X Y : TopCat.{0}} (f : X ⟶ Y) {F G : AbelianSheaf X} (g : F ⟶ G)
  (I : InjectiveResolution F) (J : InjectiveResolution G)
  (φ : I.cocomplex ⟶ J.cocomplex) (hφ : I.ι.f 0 ≫ φ.f 0 = g ≫ J.ι.f 0)

include hφ

/-- Naturality of the degree-zero sheaf comparison with actual ordinary pushforward. -/
@[reassoc] theorem homologyZeroPushforwardIso_hom_naturality :
    HomologicalComplex.homologyMap (((pushforward f).mapHomologicalComplex _).map φ) 0 ≫
        (homologyZeroPushforwardIso f J).hom =
      (homologyZeroPushforwardIso f I).hom ≫ (pushforward f).map g := by
  let rI := resolutionIso f F I 0
  let rJ := resolutionIso f G J 0
  let zI := (zeroIso f).app F
  let zJ := (zeroIso f).app G
  let m := HomologicalComplex.homologyMap (((pushforward f).mapHomologicalComplex _).map φ) 0
  have hr : m ≫ rJ.inv = rI.inv ≫ (functor f 0).map g :=
    (InjectiveResolution.isoRightDerivedObj_inv_naturality g I J φ hφ (pushforward f) 0).symm
  have hz : (functor f 0).map g ≫ zJ.hom = zI.hom ≫ (pushforward f).map g :=
    (zeroIso f).hom.naturality g
  change m ≫ (rJ.inv ≫ zJ.hom) = (rI.inv ≫ zI.hom) ≫ (pushforward f).map g
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ zJ.hom) hr).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun a => rI.inv ≫ a) hz).trans (Category.assoc _ _ _).symm)))

/-- The same naturality on every genuine sheaf-cohomology degree. -/
@[reassoc] theorem homologyZeroCohomologyIso_hom_naturality (n : ℕ) :
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology Y) n).map
        (HomologicalComplex.homologyMap (((pushforward f).mapHomologicalComplex _).map φ) 0) ≫
      (homologyZeroCohomologyIso f J n).hom =
    (homologyZeroCohomologyIso f I n).hom ≫
      (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology Y) n).map
        ((pushforward f).map g) := by
  let H := CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology Y) n
  exact (H.map_comp _ _).symm.trans
    ((congrArg H.map (homologyZeroPushforwardIso_hom_naturality f g I J φ hφ)).trans
      (H.map_comp _ _))

/-- The edge-term comparison commutes with the actual first derived
coefficient map and the actual map of resolution homology. -/
@[reassoc] theorem homologyOneExtZeroIso_hom_naturality :
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology Y) 0).map
        ((functor f 1).map g) ≫ (homologyOneExtZeroIso f J).hom =
      (homologyOneExtZeroIso f I).hom ≫
        (preadditiveCoyoneda.obj (op (integerSheaf Y))).map
          (HomologicalComplex.homologyMap (((pushforward f).mapHomologicalComplex _).map φ) 1) := by
  apply AddCommGrpCat.ext
  intro x
  let d := (functor f 1).map g
  let rI := resolutionIso f F I 1
  let rJ := resolutionIso f G J 1
  let m := HomologicalComplex.homologyMap (((pushforward f).mapHomologicalComplex _).map φ) 1
  have hr : d ≫ rJ.hom = rI.hom ≫ m :=
    InjectiveResolution.isoRightDerivedObj_hom_naturality g I J φ hφ (pushforward f) 1
  change Ext.addEquiv₀ (CategoryTheory.Sheaf.H.map d 0 x) ≫ rJ.hom =
    (Ext.addEquiv₀ x ≫ rI.hom) ≫ m
  exact (congrArg (fun a => a ≫ rJ.hom) (CategoryTheory.Sheaf.H.addEquiv₀_map d x)).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun a => Ext.addEquiv₀ x ≫ a) hr).trans (Category.assoc _ _ _).symm))

end Wikipedia.HopfProblem.SheafLerayLowDegrees
