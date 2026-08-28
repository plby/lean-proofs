import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Applying a functor to an extended complex

The comparison here is degreewise: inside the embedded shape it is the identity,
and outside it is the canonical comparison between the image of a zero object
and a zero object.  In particular it does not use any exactness assumption.
-/

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open scoped ZeroObject
open HomologicalComplex

namespace Wikipedia.HopfProblem.SheafHigherDirectImage.ExtBridge

universe u₁ u₂ v₁ v₂

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C] [HasZeroObject C]
  {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D] [HasZeroObject D]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

/-- The object comparison before evaluating the partial inverse of an embedding. -/
noncomputable def mapExtendOptionIso (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : HomologicalComplex C c) (i : Option ι) :
    F.obj (extend.X K i) ≅ extend.X ((F.mapHomologicalComplex c).obj K) i :=
  match i with
  | some _ => Iso.refl _
  | none => F.mapZeroObject

lemma mapExtendOptionIso_hom_d (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : HomologicalComplex C c) (i j : Option ι) :
    (mapExtendOptionIso F K i).hom ≫
        extend.d ((F.mapHomologicalComplex c).obj K) i j =
      F.map (extend.d K i j) ≫ (mapExtendOptionIso F K j).hom := by
  cases i with
  | none =>
    cases j with
    | none =>
      change (0 : F.obj 0 ⟶ (0 : D)) ≫ (0 : (0 : D) ⟶ 0) =
        F.map (0 : (0 : C) ⟶ 0) ≫ (0 : F.obj 0 ⟶ (0 : D))
      simp
    | some j =>
      change (0 : F.obj 0 ⟶ (0 : D)) ≫ (0 : (0 : D) ⟶ F.obj (K.X j)) =
        F.map (0 : (0 : C) ⟶ K.X j) ≫ 𝟙 (F.obj (K.X j))
      simp
  | some i =>
    cases j with
    | none =>
      change 𝟙 (F.obj (K.X i)) ≫ (0 : F.obj (K.X i) ⟶ (0 : D)) =
        F.map (0 : K.X i ⟶ (0 : C)) ≫ (0 : F.obj 0 ⟶ (0 : D))
      simp
    | some j =>
      change 𝟙 (F.obj (K.X i)) ≫ F.map (K.d i j) =
        F.map (K.d i j) ≫ 𝟙 (F.obj (K.X j))
      simp

/-- A zero-preserving functor commutes with extension of homological complexes. -/
noncomputable def mapExtendIso (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : HomologicalComplex C c) (e : c.Embedding c') :
    (F.mapHomologicalComplex c').obj (K.extend e) ≅
      ((F.mapHomologicalComplex c).obj K).extend e :=
  Hom.isoOfComponents (fun i => mapExtendOptionIso F K (e.r i))
    (fun i j _ => mapExtendOptionIso_hom_d F K (e.r i) (e.r j))

lemma mapExtendOptionIso_hom_some (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : HomologicalComplex C c) {i : Option ι} {j : ι} (h : i = some j) :
    (mapExtendOptionIso F K i).hom =
      F.map (extend.XIso K h).hom ≫
        (extend.XIso ((F.mapHomologicalComplex c).obj K) h).inv := by
  subst h
  change 𝟙 (F.obj (K.X j)) = F.map (𝟙 (K.X j)) ≫ 𝟙 (F.obj (K.X j))
  simp

/-- At an embedded degree the comparison is the canonical object comparison. -/
lemma mapExtendIso_hom_f (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : HomologicalComplex C c) (e : c.Embedding c')
    {i : ι} {i' : ι'} (h : e.f i = i') :
    (mapExtendIso F K e).hom.f i' =
      F.map (K.extendXIso e h).hom ≫
        (((F.mapHomologicalComplex c).obj K).extendXIso e h).inv :=
  mapExtendOptionIso_hom_some F K (e.r_eq_some h)

/-- Naturality of the extension comparison in the complex. -/
@[reassoc]
lemma mapExtendIso_hom_naturality (F : C ⥤ D) [F.PreservesZeroMorphisms]
    {K L : HomologicalComplex C c} (φ : K ⟶ L) (e : c.Embedding c') :
    (F.mapHomologicalComplex c').map (extendMap φ e) ≫ (mapExtendIso F L e).hom =
      (mapExtendIso F K e).hom ≫ extendMap ((F.mapHomologicalComplex c).map φ) e := by
  ext i
  change F.map (extend.mapX φ (e.r i)) ≫ (mapExtendOptionIso F L (e.r i)).hom =
    (mapExtendOptionIso F K (e.r i)).hom ≫
      extend.mapX ((F.mapHomologicalComplex c).map φ) (e.r i)
  cases e.r i with
  | none =>
    change F.map (0 : (0 : C) ⟶ 0) ≫ (0 : F.obj 0 ⟶ (0 : D)) =
      (0 : F.obj 0 ⟶ (0 : D)) ≫ (0 : (0 : D) ⟶ 0)
    simp
  | some j =>
    change F.map (φ.f j) ≫ 𝟙 (F.obj (L.X j)) =
      𝟙 (F.obj (K.X j)) ≫ F.map (φ.f j)
    simp

/-- Naturality of the comparison in the applied functor. -/
@[reassoc]
lemma mapExtendIso_hom_natTrans {F G : C ⥤ D}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    (α : F ⟶ G) (K : HomologicalComplex C c) (e : c.Embedding c') :
    (NatTrans.mapHomologicalComplex α c').app (K.extend e) ≫
        (mapExtendIso G K e).hom =
      (mapExtendIso F K e).hom ≫
        extendMap ((NatTrans.mapHomologicalComplex α c).app K) e := by
  ext i
  change α.app (extend.X K (e.r i)) ≫ (mapExtendOptionIso G K (e.r i)).hom =
    (mapExtendOptionIso F K (e.r i)).hom ≫
      extend.mapX ((NatTrans.mapHomologicalComplex α c).app K) (e.r i)
  cases e.r i with
  | none =>
    change α.app 0 ≫ (0 : G.obj 0 ⟶ (0 : D)) =
      (0 : F.obj 0 ⟶ (0 : D)) ≫ (0 : (0 : D) ⟶ 0)
    simp
  | some j =>
    change α.app (K.X j) ≫ 𝟙 (G.obj (K.X j)) =
      𝟙 (F.obj (K.X j)) ≫ α.app (K.X j)
    simp

end Wikipedia.HopfProblem.SheafHigherDirectImage.ExtBridge
