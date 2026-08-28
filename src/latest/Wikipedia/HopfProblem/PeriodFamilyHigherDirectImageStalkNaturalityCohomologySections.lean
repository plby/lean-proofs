import Wikipedia.HopfProblem.SheafHigherDirectImageSectionsComplex

/-!
# Complex-map naturality of the native section homology comparison

The actual Hom-complex comparison with sections is natural in a map of
sheaf complexes. Taking its genuine homology and the exact evaluation
comparison gives the original map on the cohomology presheaf.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.StalkNaturality

open SheafHigherDirectImage SheafHigherDirectImage.Sections
open HolomorphicSheafCohomology.OpenRestriction

variable {X : TopCat.{0}}

/-- The section homology comparison commutes with a genuine map of
sheaf complexes and its original underlying presheaf homology map. -/
@[reassoc] theorem homSectionsHomologyIso_hom_naturality_complex
    {K L : CochainComplex (AbelianSheaf X) ℕ} (φ : K ⟶ L) (U : Opens X) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((preadditiveCoyoneda.obj (op (freeOpen U))).mapHomologicalComplex _).map φ) n ≫
      (homSectionsHomologyIso L U n).hom =
    (homSectionsHomologyIso K U n).hom ≫
      (HomologicalComplex.homologyMap
        (((TopCat.Sheaf.forget AddCommGrpCat X).mapHomologicalComplex _).map φ) n).app
          (op U) := by
  have h := congrArg
    ((HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) n).map)
    (homSectionsComplexIso_hom_naturality_complex φ U)
  simp only [Functor.map_comp] at h
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) n
  let a := H.map (homSectionsComplexIso K U).hom
  let b := H.map (homSectionsComplexIso L U).hom
  let c := H.map
    (((preadditiveCoyoneda.obj (op (freeOpen U))).mapHomologicalComplex _).map φ)
  let d := H.map (((sectionsFunctor U).mapHomologicalComplex _).map φ)
  let φ' := ((TopCat.Sheaf.forget AddCommGrpCat X).mapHomologicalComplex _).map φ
  let m := (HomologicalComplex.homologyMap φ' n).app (op U)
  let eK := mapComplexHomologyIso (underlyingPresheafComplex K) (presheafEvaluation U) n
  let eL := mapComplexHomologyIso (underlyingPresheafComplex L) (presheafEvaluation U) n
  have hd : d ≫ eL.hom = eK.hom ≫ m :=
    mapComplexHomologyIso_hom_naturality φ' (presheafEvaluation U) n
  change c ≫ (b ≫ eL.hom) = (a ≫ eK.hom) ≫ m
  calc
    _ = (c ≫ b) ≫ eL.hom := (Category.assoc _ _ _).symm
    _ = (a ≫ d) ≫ eL.hom := congrArg (fun t => t ≫ eL.hom) h
    _ = a ≫ (d ≫ eL.hom) := Category.assoc _ _ _
    _ = a ≫ (eK.hom ≫ m) := congrArg (fun t => a ≫ t) hd
    _ = _ := (Category.assoc _ _ _).symm

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.StalkNaturality
