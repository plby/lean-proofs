import Wikipedia.HopfProblem.SheafCupProductGodementRing
import Wikipedia.HopfProblem.SheafCupProductCofaceBasic

/-!
# Actual germ-insertion cofaces through degree three

Each displayed coface inserts the original natural germ inclusion into
an iterate of the actual product-of-stalks functor.  Their cosimplicial
identities follow from that proved naturality.  Applying an actual
ring-valued functor, such as sections on an open or a stalk, gives the
concrete coface data used for the Alexander--Whitney product.
-/

noncomputable section

open CategoryTheory
open scoped Matrix

namespace Wikipedia.HopfProblem.SheafCupProduct.GodementRing

variable {X : TopCat.{0}}

abbrev term0 (F : RingSheaf X) := sheaf F
abbrev term1 (F : RingSheaf X) := sheaf (term0 F)
abbrev term2 (F : RingSheaf X) := sheaf (term1 F)
abbrev term3 (F : RingSheaf X) := sheaf (term2 F)

def face0 (F : RingSheaf X) : Fin 2 → (term0 F ⟶ term1 F) :=
  ![inclusion (term0 F), map (inclusion F)]

def face1 (F : RingSheaf X) : Fin 3 → (term1 F ⟶ term2 F) :=
  ![inclusion (term1 F), map (inclusion (term0 F)), map (map (inclusion F))]

def face2 (F : RingSheaf X) : Fin 4 → (term2 F ⟶ term3 F) :=
  ![inclusion (term2 F), map (inclusion (term1 F)),
    map (map (inclusion (term0 F))), map (map (map (inclusion F)))]

theorem map_composition_eq {A B C D : RingSheaf X}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ C) (k : C ⟶ D) (e : f ≫ g = h ≫ k) :
    map f ≫ map g = map h ≫ map k :=
  (map_comp f g).symm.trans ((congrArg map e).trans (map_comp h k))

/-- The actual degree-zero coface identities are germ naturality. -/
theorem face01 (F : RingSheaf X) (i j : Fin 2) (hij : i ≤ j) :
    face0 F i ≫ face1 F j.succ = face0 F j ≫ face1 F i.castSucc := by
  fin_cases i <;> fin_cases j
  · exact inclusion_naturality (inclusion (term0 F))
  · exact inclusion_naturality (map (inclusion F))
  · exact False.elim ((by decide : ¬((1 : Fin 2) ≤ 0)) hij)
  · exact map_composition_eq _ _ _ _ (inclusion_naturality (inclusion F))

/-- The actual next coface identities are the same naturality and its
image under the actual Godement functor. -/
theorem face12 (F : RingSheaf X) (i j : Fin 3) (hij : i ≤ j) :
    face1 F i ≫ face2 F j.succ = face1 F j ≫ face2 F i.castSucc := by
  fin_cases i <;> fin_cases j
  · exact inclusion_naturality (inclusion (term1 F))
  · exact inclusion_naturality (map (inclusion (term0 F)))
  · exact inclusion_naturality (map (map (inclusion F)))
  · exact False.elim ((by decide : ¬((1 : Fin 3) ≤ 0)) hij)
  · exact map_composition_eq _ _ _ _ (face01 F 0 0 (by decide))
  · exact map_composition_eq _ _ _ _ (face01 F 0 1 (by decide))
  · exact False.elim ((by decide : ¬((2 : Fin 3) ≤ 0)) hij)
  · exact False.elim ((by decide : ¬((2 : Fin 3) ≤ 1)) hij)
  · exact map_composition_eq _ _ _ _ (face01 F 1 1 (by decide))

/-- Applying any actual ring-valued functor retains the proved coface equations. -/
def cofaceData (F : RingSheaf X) (S : RingSheaf X ⥤ CommRingCat.{0}) :
    Coface.Data (S.obj (term0 F)) (S.obj (term1 F))
      (S.obj (term2 F)) (S.obj (term3 F)) where
  δ0 i := (S.map (face0 F i)).hom
  δ1 i := (S.map (face1 F i)).hom
  δ2 i := (S.map (face2 F i)).hom
  coface01 i j hij := by
    have h : S.map (face0 F i) ≫ S.map (face1 F j.succ) =
        S.map (face0 F j) ≫ S.map (face1 F i.castSucc) :=
      (S.map_comp _ _).symm.trans
        ((congrArg S.map (face01 F i j hij)).trans (S.map_comp _ _))
    exact congrArg (fun k => k.hom) h
  coface12 i j hij := by
    have h : S.map (face1 F i) ≫ S.map (face2 F j.succ) =
        S.map (face1 F j) ≫ S.map (face2 F i.castSucc) :=
      (S.map_comp _ _).symm.trans
        ((congrArg S.map (face12 F i j hij)).trans (S.map_comp _ _))
    exact congrArg (fun k => k.hom) h

end Wikipedia.HopfProblem.SheafCupProduct.GodementRing
