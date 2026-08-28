import Wikipedia.HopfProblem.SheafCupProductGodementCofaces
import Wikipedia.HopfProblem.SheafCupProductCofaceNaturality

/-!
# The actual Godement cofaces commute with ring-sheaf morphisms

All coefficient maps below are iterates of the original ring-sheaf map.
Germ naturality proves the coface squares.  Thus the genuine
Alexander--Whitney product on the actual coface quotients is natural for
these maps, including the original constants inclusion into holomorphic
functions.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.SheafCupProduct.GodementRing

variable {X : TopCat.{0}} {F G : RingSheaf X}

abbrev term0Map (f : F ⟶ G) : term0 F ⟶ term0 G := map f
abbrev term1Map (f : F ⟶ G) : term1 F ⟶ term1 G := map (term0Map f)
abbrev term2Map (f : F ⟶ G) : term2 F ⟶ term2 G := map (term1Map f)
abbrev term3Map (f : F ⟶ G) : term3 F ⟶ term3 G := map (term2Map f)

theorem face0_naturality (f : F ⟶ G) (i : Fin 2) :
    face0 F i ≫ term1Map f = term0Map f ≫ face0 G i := by
  fin_cases i
  · exact inclusion_naturality (term0Map f)
  · exact map_composition_eq _ _ _ _ (inclusion_naturality f)

theorem face1_naturality (f : F ⟶ G) (i : Fin 3) :
    face1 F i ≫ term2Map f = term1Map f ≫ face1 G i := by
  fin_cases i
  · exact inclusion_naturality (term1Map f)
  · exact map_composition_eq _ _ _ _ (face0_naturality f 0)
  · exact map_composition_eq _ _ _ _ (face0_naturality f 1)

theorem face2_naturality (f : F ⟶ G) (i : Fin 4) :
    face2 F i ≫ term3Map f = term2Map f ≫ face2 G i := by
  fin_cases i
  · exact inclusion_naturality (term2Map f)
  · exact map_composition_eq _ _ _ _ (face1_naturality f 0)
  · exact map_composition_eq _ _ _ _ (face1_naturality f 1)
  · exact map_composition_eq _ _ _ _ (face1_naturality f 2)

/-- The actual coefficient morphism of low-degree coface data. -/
def cofaceMap (f : F ⟶ G) (S : RingSheaf X ⥤ CommRingCat.{0}) :
    (cofaceData F S).Morphism (cofaceData G S) where
  f0 := (S.map (term0Map f)).hom
  f1 := (S.map (term1Map f)).hom
  f2 := (S.map (term2Map f)).hom
  f3 := (S.map (term3Map f)).hom
  comm0 i := by
    have h : S.map (face0 F i) ≫ S.map (term1Map f) =
        S.map (term0Map f) ≫ S.map (face0 G i) :=
      (S.map_comp _ _).symm.trans
        ((congrArg S.map (face0_naturality f i)).trans (S.map_comp _ _))
    exact congrArg (fun k => k.hom) h
  comm1 i := by
    have h : S.map (face1 F i) ≫ S.map (term2Map f) =
        S.map (term1Map f) ≫ S.map (face1 G i) :=
      (S.map_comp _ _).symm.trans
        ((congrArg S.map (face1_naturality f i)).trans (S.map_comp _ _))
    exact congrArg (fun k => k.hom) h
  comm2 i := by
    have h : S.map (face2 F i) ≫ S.map (term3Map f) =
        S.map (term2Map f) ≫ S.map (face2 G i) :=
      (S.map_comp _ _).symm.trans
        ((congrArg S.map (face2_naturality f i)).trans (S.map_comp _ _))
    exact congrArg (fun k => k.hom) h

/-- Actual ring-valued sections on the specified open set. -/
def sections (U : Opens X) : RingSheaf X ⥤ CommRingCat.{0} :=
  TopCat.Sheaf.forget CommRingCat X ⋙
    (CategoryTheory.evaluation (Opens X)ᵒᵖ CommRingCat).obj (op U)

/-- The cofaces act on genuine sections of the four actual Godement terms. -/
abbrev sectionData (F : RingSheaf X) (U : Opens X) := cofaceData F (sections U)

end Wikipedia.HopfProblem.SheafCupProduct.GodementRing
