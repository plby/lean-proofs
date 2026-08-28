import Wikipedia.HopfProblem.SheafHigherDirectImageBasic
import Mathlib.Algebra.Homology.Functor

/-!
# Exact stalks and the cohomology presheaf of a sheaf complex

Filtered colimits of abelian groups are exact.  Thus both the presheaf
stalk functor and the native sheaf stalk functor commute with homology.
For an actual complex of sheaves, the stalk of its sheaf cohomology is
therefore the stalk of the presheaf obtained by taking cohomology before
sheafification.  This is the local algebra used in the higher-direct-
image stalk comparison.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits
open TopCat.Presheaf

namespace Wikipedia.HopfProblem.SheafHigherDirectImage

variable {X : TopCat.{0}} (x : X)

/-- Presheaf stalks preserve finite limits: they are filtered colimits
of evaluations, and filtered colimits in abelian groups are exact. -/
instance presheafStalk_preservesFiniteLimits :
    PreservesFiniteLimits (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x) := by
  change PreservesFiniteLimits
    ((Functor.whiskeringLeft _ _ AddCommGrpCat).obj (OpenNhds.inclusion x).op ⋙ colim)
  infer_instance

/-- Presheaf stalks also preserve finite colimits. -/
instance presheafStalk_preservesFiniteColimits :
    PreservesFiniteColimits (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x) := by
  change PreservesFiniteColimits
    ((Functor.whiskeringLeft _ _ AddCommGrpCat).obj (OpenNhds.inclusion x).op ⋙ colim)
  infer_instance

section ExactFunctor

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  {ι : Type*} {c : ComplexShape ι}

/-- The native short-complex homology comparison, stated for a whole
homological complex. -/
def mapComplexHomologyIso (K : HomologicalComplex C c) (F : C ⥤ D)
    [F.Additive] [F.PreservesHomology] (n : ι) :
    ((F.mapHomologicalComplex c).obj K).homology n ≅ F.obj (K.homology n) :=
  (K.sc n).mapHomologyIso F

/-- The comparison uses the actual maps on homology. -/
@[reassoc] theorem mapComplexHomologyIso_hom_naturality
    {K L : HomologicalComplex C c} (φ : K ⟶ L) (F : C ⥤ D)
    [F.Additive] [F.PreservesHomology] (n : ι) :
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex c).map φ) n ≫
      (mapComplexHomologyIso L F n).hom =
        (mapComplexHomologyIso K F n).hom ≫ F.map (HomologicalComplex.homologyMap φ n) :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor C c n).map φ) F

/-- Naturality of the inverse homology comparison. -/
@[reassoc] theorem mapComplexHomologyIso_inv_naturality
    {K L : HomologicalComplex C c} (φ : K ⟶ L) (F : C ⥤ D)
    [F.Additive] [F.PreservesHomology] (n : ι) :
    F.map (HomologicalComplex.homologyMap φ n) ≫
      (mapComplexHomologyIso L F n).inv =
        (mapComplexHomologyIso K F n).inv ≫
          HomologicalComplex.homologyMap ((F.mapHomologicalComplex c).map φ) n :=
  ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor C c n).map φ) F

end ExactFunctor

/-- Forgetting the sheaf condition gives the actual complex of presheaves. -/
abbrev underlyingPresheafComplex (K : CochainComplex (AbelianSheaf X) ℕ) :
    CochainComplex (TopCat.Presheaf AddCommGrpCat X) ℕ :=
  ((TopCat.Sheaf.forget AddCommGrpCat X).mapHomologicalComplex _).obj K

/-- The cohomology presheaf of the underlying actual presheaf complex. -/
abbrev homologyPresheaf (K : CochainComplex (AbelianSheaf X) ℕ) (n : ℕ) :
    TopCat.Presheaf AddCommGrpCat X := (underlyingPresheafComplex K).homology n

/-- Sheaf cohomology and presheaf cohomology of the same complex have
canonically identical stalks. -/
def stalkHomologyPresheafIso (K : CochainComplex (AbelianSheaf X) ℕ) (n : ℕ) :
    TopCat.Presheaf.stalk (K.homology n).obj x ≅
      TopCat.Presheaf.stalk (homologyPresheaf K n) x :=
  (mapComplexHomologyIso K
    (TopCat.Sheaf.forget AddCommGrpCat X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat x) n).symm ≪≫
  mapComplexHomologyIso (underlyingPresheafComplex K)
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat x) n

/-- The stalk comparison is natural for genuine maps of sheaf complexes. -/
@[reassoc] theorem stalkHomologyPresheafIso_hom_naturality
    {K L : CochainComplex (AbelianSheaf X) ℕ} (φ : K ⟶ L) (n : ℕ) :
    (TopCat.Sheaf.forget AddCommGrpCat X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        (HomologicalComplex.homologyMap φ n) ≫ (stalkHomologyPresheafIso x L n).hom =
      (stalkHomologyPresheafIso x K n).hom ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (HomologicalComplex.homologyMap
            (((TopCat.Sheaf.forget AddCommGrpCat X).mapHomologicalComplex _).map φ) n) := by
  let S := TopCat.Sheaf.forget AddCommGrpCat X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat x
  let P := TopCat.Presheaf.stalkFunctor AddCommGrpCat x
  let φ' := ((TopCat.Sheaf.forget AddCommGrpCat X).mapHomologicalComplex _).map φ
  let aK := mapComplexHomologyIso K S n
  let aL := mapComplexHomologyIso L S n
  let bK := mapComplexHomologyIso (underlyingPresheafComplex K) P n
  let bL := mapComplexHomologyIso (underlyingPresheafComplex L) P n
  change S.map (HomologicalComplex.homologyMap φ n) ≫ (aL.inv ≫ bL.hom) =
    (aK.inv ≫ bK.hom) ≫ P.map (HomologicalComplex.homologyMap φ' n)
  calc
    _ = (S.map (HomologicalComplex.homologyMap φ n) ≫ aL.inv) ≫ bL.hom :=
      (Category.assoc _ _ _).symm
    _ = (aK.inv ≫ HomologicalComplex.homologyMap ((S.mapHomologicalComplex _).map φ) n) ≫
        bL.hom := congrArg (fun g => g ≫ bL.hom) (mapComplexHomologyIso_inv_naturality φ S n)
    _ = aK.inv ≫ (HomologicalComplex.homologyMap ((P.mapHomologicalComplex _).map φ') n ≫
        bL.hom) := Category.assoc _ _ _
    _ = aK.inv ≫ (bK.hom ≫ P.map (HomologicalComplex.homologyMap φ' n)) :=
      congrArg (fun g => aK.inv ≫ g) (mapComplexHomologyIso_hom_naturality φ' P n)
    _ = _ := (Category.assoc _ _ _).symm

end Wikipedia.HopfProblem.SheafHigherDirectImage
