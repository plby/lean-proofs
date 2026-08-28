import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# Degree-zero Ext and the native Hom short complex

The canonical additive equivalence between degree-zero Ext and Hom is
natural in both objects.  Applying it to a short complex gives an
isomorphism of the actual short complexes and of their native opcycles.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

namespace Wikipedia.HopfProblem.SheafLerayLowDegrees.Abstract

universe u

variable {C : Type u} [Category.{0} C] [Abelian C] [HasExt.{0} C]

/-- The canonical degree-zero Ext–Hom isomorphism of abelian groups. -/
def extZeroHomIso (A B : C) :
    AddCommGrpCat.of (Ext A B 0) ≅ AddCommGrpCat.of (A ⟶ B) :=
  Ext.addEquiv₀.toAddCommGrpIso

@[simp]
theorem extZeroHomIso_hom_apply (A B : C) (x : Ext A B 0) :
    (extZeroHomIso A B).hom x = Ext.addEquiv₀ x := rfl

@[simp]
theorem extZeroHomIso_inv_apply (A B : C) (f : A ⟶ B) :
    (extZeroHomIso A B).inv f = Ext.mk₀ f := rfl

@[simp]
theorem extZeroHomIso_hom_mk₀ (A B : C) (f : A ⟶ B) :
    (extZeroHomIso A B).hom (Ext.mk₀ f) = f :=
  Ext.addEquiv₀.apply_symm_apply f

/-- The degree-zero comparison commutes with postcomposition. -/
@[reassoc]
theorem extZeroHomIso_hom_naturality (A : C) {B B' : C} (f : B ⟶ B') :
    (extFunctorObj A 0).map f ≫ (extZeroHomIso A B').hom =
      (extZeroHomIso A B).hom ≫ (preadditiveCoyoneda.obj (op A)).map f := by
  apply AddCommGrpCat.ext
  intro x
  obtain ⟨g, rfl⟩ := (Ext.addEquiv₀ (X := A) (Y := B)).symm.surjective x
  change (extZeroHomIso A B').hom
      ((Ext.mk₀ g).comp (Ext.mk₀ f) (zero_add 0)) =
    (extZeroHomIso A B).hom (Ext.mk₀ g) ≫ f
  rw [Ext.mk₀_comp_mk₀, extZeroHomIso_hom_mk₀, extZeroHomIso_hom_mk₀]

/-- Degree-zero Ext, naturally in the second object, is the Hom functor. -/
def extZeroHomNatIso (A : C) :
    extFunctorObj A 0 ≅ preadditiveCoyoneda.obj (op A) :=
  NatIso.ofComponents (extZeroHomIso A) (fun f => extZeroHomIso_hom_naturality A f)

@[simp]
theorem extZeroHomNatIso_hom_app (A B : C) :
    (extZeroHomNatIso A).hom.app B = (extZeroHomIso A B).hom := rfl

@[simp]
theorem extZeroHomNatIso_inv_app (A B : C) :
    (extZeroHomNatIso A).inv.app B = (extZeroHomIso A B).inv := rfl

/-- The degree-zero comparison also commutes with precomposition. -/
@[reassoc]
theorem extZeroHomIso_hom_precomp {A A' : C} (a : A' ⟶ A) (B : C) :
    ((extFunctor 0).map a.op).app B ≫ (extZeroHomIso A' B).hom =
      (extZeroHomIso A B).hom ≫ (preadditiveCoyoneda.map a.op).app B := by
  apply AddCommGrpCat.ext
  intro x
  obtain ⟨g, rfl⟩ := (Ext.addEquiv₀ (X := A) (Y := B)).symm.surjective x
  change (extZeroHomIso A' B).hom
      ((Ext.mk₀ a).comp (Ext.mk₀ g) (zero_add 0)) =
    a ≫ (extZeroHomIso A B).hom (Ext.mk₀ g)
  rw [Ext.mk₀_comp_mk₀, extZeroHomIso_hom_mk₀, extZeroHomIso_hom_mk₀]

/-- The genuine degree-zero Ext short complex is isomorphic to the Hom short complex. -/
def extZeroHomShortComplexIso (A : C) (S : ShortComplex C) :
    S.map (extFunctorObj A 0) ≅ S.map (preadditiveCoyoneda.obj (op A)) :=
  S.mapNatIso (extZeroHomNatIso A)

@[simp]
theorem extZeroHomShortComplexIso_hom_τ₂ (A : C) (S : ShortComplex C) :
    (extZeroHomShortComplexIso A S).hom.τ₂ = (extZeroHomIso A S.X₂).hom := rfl

@[simp]
theorem extZeroHomShortComplexIso_inv_τ₂ (A : C) (S : ShortComplex C) :
    (extZeroHomShortComplexIso A S).inv.τ₂ = (extZeroHomIso A S.X₂).inv := rfl

/-- The induced comparison of the actual cokernels of the first differential. -/
def extZeroHomOpcyclesIso (A : C) (S : ShortComplex C) :
    (S.map (extFunctorObj A 0)).opcycles ≅
      (S.map (preadditiveCoyoneda.obj (op A))).opcycles :=
  ShortComplex.opcyclesMapIso (extZeroHomShortComplexIso A S)

/-- The comparison of opcycles is induced by the degree-zero comparison on the middle term. -/
@[reassoc (attr := simp)]
theorem pOpcycles_extZeroHomOpcyclesIso_hom (A : C) (S : ShortComplex C) :
    (S.map (extFunctorObj A 0)).pOpcycles ≫ (extZeroHomOpcyclesIso A S).hom =
      (extZeroHomIso A S.X₂).hom ≫
        (S.map (preadditiveCoyoneda.obj (op A))).pOpcycles :=
  ShortComplex.p_opcyclesMap (extZeroHomShortComplexIso A S).hom

/-- The comparison of opcycles commutes with their canonical outgoing map. -/
@[reassoc (attr := simp)]
theorem extZeroHomOpcyclesIso_hom_fromOpcycles (A : C) (S : ShortComplex C) :
    (extZeroHomOpcyclesIso A S).hom ≫
        (S.map (preadditiveCoyoneda.obj (op A))).fromOpcycles =
      (S.map (extFunctorObj A 0)).fromOpcycles ≫ (extZeroHomIso A S.X₃).hom :=
  ShortComplex.fromOpcycles_naturality (extZeroHomShortComplexIso A S).hom

end Wikipedia.HopfProblem.SheafLerayLowDegrees.Abstract
