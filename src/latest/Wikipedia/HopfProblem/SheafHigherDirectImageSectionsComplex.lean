import Wikipedia.HopfProblem.SheafHigherDirectImageSectionsBasic
import Wikipedia.HopfProblem.SheafHigherDirectImageHomology
import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite

/-!
# The section comparison on actual cochain complexes

The free-open-sheaf representation of sections gives a degreewise
isomorphism on any complex of abelian sheaves.  Its open-set naturality
passes to the genuine homology groups and the actual cohomology
presheaf of that complex.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafHigherDirectImage.Sections

open HolomorphicSheafCohomology.OpenRestriction

variable {X : TopCat.{0}}

instance sectionsFunctor_additive (U : Opens X) : (sectionsFunctor U).Additive where
  map_add := by intros; rfl

/-- Evaluation of an abelian presheaf at an actual open set. -/
abbrev presheafEvaluation (U : Opens X) : TopCat.Presheaf AddCommGrpCat.{0} X ⥤
    AddCommGrpCat.{0} :=
  (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op U)

instance presheafEvaluation_additive (U : Opens X) : (presheafEvaluation U).Additive where
  map_add := by intros; rfl

instance presheafEvaluation_preservesFiniteLimits (U : Opens X) :
    PreservesFiniteLimits (presheafEvaluation U) :=
  inferInstanceAs (PreservesFiniteLimits
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{0}).obj (op U)))

instance presheafEvaluation_preservesFiniteColimits (U : Opens X) :
    PreservesFiniteColimits (presheafEvaluation U) :=
  inferInstanceAs (PreservesFiniteColimits
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{0}).obj (op U)))

/-- Hom from the free sheaf on an open and sections on that open give
canonically isomorphic cochain complexes. -/
def homSectionsComplexIso (K : CochainComplex (AbelianSheaf X) ℕ) (U : Opens X) :
    (((preadditiveCoyoneda.obj (op (freeOpen U))).mapHomologicalComplex _).obj K) ≅
      (((sectionsFunctor U).mapHomologicalComplex _).obj K) :=
  (NatIso.mapHomologicalComplex (freeOpenSectionsIso U) _).app K

/-- The complex comparison commutes with restriction along an actual
inclusion of open sets. -/
@[reassoc] theorem homSectionsComplexIso_hom_naturality_open
    (K : CochainComplex (AbelianSheaf X) ℕ) {U V : Opens X} (i : U ⟶ V) :
    (NatTrans.mapHomologicalComplex
        (preadditiveCoyoneda.map ((freeOpenFunctor X).map i).op) _).app K ≫
      (homSectionsComplexIso K U).hom =
    (homSectionsComplexIso K V).hom ≫
      (NatTrans.mapHomologicalComplex
        ((TopCat.Sheaf.forget AddCommGrpCat X).flip.map i.op) _).app K := by
  ext n h
  exact freeHomEquiv_naturality_open i (K.X n) h

/-- The complex comparison is also natural in the actual complex. -/
@[reassoc] theorem homSectionsComplexIso_hom_naturality_complex
    {K L : CochainComplex (AbelianSheaf X) ℕ} (φ : K ⟶ L) (U : Opens X) :
    ((preadditiveCoyoneda.obj (op (freeOpen U))).mapHomologicalComplex _).map φ ≫
      (homSectionsComplexIso L U).hom =
    (homSectionsComplexIso K U).hom ≫
      ((sectionsFunctor U).mapHomologicalComplex _).map φ :=
  NatTrans.mapHomologicalComplex_naturality (freeOpenSectionsIso U).hom φ

/-- Exact evaluation commutes with homology, compatibly with the
actual open-set restriction maps. -/
@[reassoc] theorem evaluationHomologyIso_hom_naturality_open
    (L : CochainComplex (TopCat.Presheaf AddCommGrpCat X) ℕ)
    {U V : Opens X} (i : U ⟶ V) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex
          ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).map i.op) _).app L) n ≫
      (mapComplexHomologyIso L (presheafEvaluation U) n).hom =
    (mapComplexHomologyIso L (presheafEvaluation V) n).hom ≫
      (L.homology n).map i.op := by
  have h := ShortComplex.homologyMap_mapNatTrans (L.sc n)
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).map i.op)
  exact (congrArg
    (fun a => a ≫ (mapComplexHomologyIso L (presheafEvaluation U) n).hom) h).trans
      (by
        let e := mapComplexHomologyIso L (presheafEvaluation U) n
        let a := (mapComplexHomologyIso L (presheafEvaluation V) n).hom
        let b := (L.homology n).map i.op
        change (a ≫ b ≫ e.inv) ≫ e.hom = a ≫ b
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

/-- The Hom-complex homology is the value of the actual homology
presheaf at the open set. -/
def homSectionsHomologyIso (K : CochainComplex (AbelianSheaf X) ℕ)
    (U : Opens X) (n : ℕ) :
    ((((preadditiveCoyoneda.obj (op (freeOpen U))).mapHomologicalComplex _).obj K).homology n) ≅
      (homologyPresheaf K n).obj (op U) :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) n).mapIso
      (homSectionsComplexIso K U) ≪≫
    mapComplexHomologyIso (underlyingPresheafComplex K) (presheafEvaluation U) n

/-- Naturality in the open set survives taking the genuine homology. -/
@[reassoc] theorem homSectionsHomologyIso_hom_naturality_open
    (K : CochainComplex (AbelianSheaf X) ℕ) {U V : Opens X} (i : U ⟶ V) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex
          (preadditiveCoyoneda.map ((freeOpenFunctor X).map i).op) _).app K) n ≫
      (homSectionsHomologyIso K U n).hom =
    (homSectionsHomologyIso K V n).hom ≫ (homologyPresheaf K n).map i.op := by
  have h := congrArg
    ((HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) n).map)
    (homSectionsComplexIso_hom_naturality_open K i)
  simp only [Functor.map_comp] at h
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) n
  let a := H.map (homSectionsComplexIso K V).hom
  let b := H.map (homSectionsComplexIso K U).hom
  let c := H.map ((NatTrans.mapHomologicalComplex
    (preadditiveCoyoneda.map ((freeOpenFunctor X).map i).op) _).app K)
  let d := H.map ((NatTrans.mapHomologicalComplex
    ((TopCat.Sheaf.forget AddCommGrpCat X).flip.map i.op) _).app K)
  let eU := mapComplexHomologyIso (underlyingPresheafComplex K) (presheafEvaluation U) n
  let eV := mapComplexHomologyIso (underlyingPresheafComplex K) (presheafEvaluation V) n
  have hd : d ≫ eU.hom = eV.hom ≫ (homologyPresheaf K n).map i.op :=
    evaluationHomologyIso_hom_naturality_open (underlyingPresheafComplex K) i n
  change c ≫ (b ≫ eU.hom) = (a ≫ eV.hom) ≫ (homologyPresheaf K n).map i.op
  calc
    _ = (c ≫ b) ≫ eU.hom := (Category.assoc _ _ _).symm
    _ = (a ≫ d) ≫ eU.hom := congrArg (fun t => t ≫ eU.hom) h
    _ = a ≫ (d ≫ eU.hom) := Category.assoc _ _ _
    _ = a ≫ (eV.hom ≫ (homologyPresheaf K n).map i.op) := congrArg (fun t => a ≫ t) hd
    _ = _ := (Category.assoc _ _ _).symm

end Wikipedia.HopfProblem.SheafHigherDirectImage.Sections
