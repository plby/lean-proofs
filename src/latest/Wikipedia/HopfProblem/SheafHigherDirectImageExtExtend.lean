import Wikipedia.HopfProblem.SheafHigherDirectImageExtExtendHomology
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# Coyoneda and extension from natural to integer cochain degrees

The homology isomorphism compares the literal mapped cochain complexes.  Its
naturality is with respect to the actual coyoneda precomposition map, and its
cycle formula records the underlying morphism in the original category.
-/

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits Opposite
open HomologicalComplex

namespace Wikipedia.HopfProblem.SheafHigherDirectImage.ExtBridge

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Coyoneda commutes with extension by zero from natural to integer degrees. -/
noncomputable def coyonedaExtendIso (A : C) (K : CochainComplex C ℕ) :
    ((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℤ)).obj
        (K.extend ComplexShape.embeddingUpNat) ≅
      (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℕ)).obj K).extend
        ComplexShape.embeddingUpNat :=
  mapExtendIso (preadditiveCoyoneda.obj (op A)) K ComplexShape.embeddingUpNat

/-- Actual coyoneda homology is unchanged by extending the original complex. -/
noncomputable def coyonedaExtendHomologyIso (A : C) (K : CochainComplex C ℕ) (n : ℕ) :
    (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℤ)).obj
        (K.extend ComplexShape.embeddingUpNat)).homology (n : ℤ) ≅
      (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℕ)).obj K).homology n :=
  mapExtendHomologyIso (preadditiveCoyoneda.obj (op A)) K
    ComplexShape.embeddingUpNat (i := n) rfl

/-- The cycles comparison underlying `coyonedaExtendHomologyIso`. -/
noncomputable def coyonedaExtendCyclesIso (A : C) (K : CochainComplex C ℕ) (n : ℕ) :
    (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℤ)).obj
        (K.extend ComplexShape.embeddingUpNat)).cycles (n : ℤ) ≅
      (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℕ)).obj K).cycles n :=
  mapExtendCyclesIso (preadditiveCoyoneda.obj (op A)) K
    ComplexShape.embeddingUpNat (i := n) rfl

/-- Naturality in the coyoneda variable, with genuine precomposition by `a`. -/
@[reassoc]
lemma coyonedaExtendHomologyIso_hom_naturality {A A' : C} (a : A' ⟶ A)
    (K : CochainComplex C ℕ) (n : ℕ) :
    homologyMap
        ((NatTrans.mapHomologicalComplex (preadditiveCoyoneda.map a.op) (.up ℤ)).app
          (K.extend ComplexShape.embeddingUpNat)) (n : ℤ) ≫
        (coyonedaExtendHomologyIso A' K n).hom =
      (coyonedaExtendHomologyIso A K n).hom ≫
        homologyMap
          ((NatTrans.mapHomologicalComplex (preadditiveCoyoneda.map a.op) (.up ℕ)).app K) n :=
  mapExtendHomologyIso_hom_natTrans (preadditiveCoyoneda.map a.op) K
    ComplexShape.embeddingUpNat (i := n) rfl

/-- Naturality in a map of the original cochain complexes. -/
@[reassoc]
lemma coyonedaExtendHomologyIso_hom_complexMap (A : C)
    {K L : CochainComplex C ℕ} (φ : K ⟶ L) (n : ℕ) :
    homologyMap
        (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℤ)).map
          (extendMap φ ComplexShape.embeddingUpNat)) (n : ℤ) ≫
        (coyonedaExtendHomologyIso A L n).hom =
      (coyonedaExtendHomologyIso A K n).hom ≫
        homologyMap
          (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℕ)).map φ) n :=
  mapExtendHomologyIso_hom_naturality (preadditiveCoyoneda.obj (op A)) φ
    ComplexShape.embeddingUpNat (i := n) rfl

/-- A cycle representative is carried through the canonical degree comparison. -/
@[reassoc]
lemma coyonedaExtendCyclesIso_hom_iCycles (A : C) (K : CochainComplex C ℕ) (n : ℕ) :
    (coyonedaExtendCyclesIso A K n).hom ≫
        (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℕ)).obj K).iCycles n =
      (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℤ)).obj
          (K.extend ComplexShape.embeddingUpNat)).iCycles (n : ℤ) ≫
        (preadditiveCoyoneda.obj (op A)).map
          (K.extendXIso ComplexShape.embeddingUpNat (i := n) rfl).hom :=
  mapExtendCyclesIso_hom_iCycles (preadditiveCoyoneda.obj (op A)) K
    ComplexShape.embeddingUpNat (i := n) rfl

/-- The isomorphism preserves the actual homology class of each cycle. -/
@[reassoc]
lemma homologyπ_coyonedaExtendHomologyIso_hom (A : C) (K : CochainComplex C ℕ) (n : ℕ) :
    (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℤ)).obj
          (K.extend ComplexShape.embeddingUpNat)).homologyπ (n : ℤ) ≫
        (coyonedaExtendHomologyIso A K n).hom =
      (coyonedaExtendCyclesIso A K n).hom ≫
        (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℕ)).obj K).homologyπ n :=
  homologyπ_mapExtendHomologyIso_hom (preadditiveCoyoneda.obj (op A)) K
    ComplexShape.embeddingUpNat (i := n) rfl

/-- On cycle elements the comparison is postcomposition by the canonical degree isomorphism. -/
lemma coyonedaExtendCyclesIso_hom_iCycles_apply (A : C) (K : CochainComplex C ℕ) (n : ℕ)
    (z : (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℤ)).obj
      (K.extend ComplexShape.embeddingUpNat)).cycles (n : ℤ)) :
    (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℕ)).obj K).iCycles n
        ((coyonedaExtendCyclesIso A K n).hom z) =
      ((((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℤ)).obj
          (K.extend ComplexShape.embeddingUpNat)).iCycles (n : ℤ) z) ≫
        (K.extendXIso ComplexShape.embeddingUpNat (i := n) rfl).hom :=
  ConcreteCategory.congr_hom (coyonedaExtendCyclesIso_hom_iCycles A K n) z

/-- The elementwise cycle-class formula for the homology comparison. -/
lemma coyonedaExtendHomologyIso_hom_homologyπ_apply (A : C)
    (K : CochainComplex C ℕ) (n : ℕ)
    (z : (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℤ)).obj
      (K.extend ComplexShape.embeddingUpNat)).cycles (n : ℤ)) :
    (coyonedaExtendHomologyIso A K n).hom
        ((((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℤ)).obj
          (K.extend ComplexShape.embeddingUpNat)).homologyπ (n : ℤ) z) =
      (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℕ)).obj K).homologyπ n
        ((coyonedaExtendCyclesIso A K n).hom z) :=
  ConcreteCategory.congr_hom (homologyπ_coyonedaExtendHomologyIso_hom A K n) z

end Wikipedia.HopfProblem.SheafHigherDirectImage.ExtBridge
