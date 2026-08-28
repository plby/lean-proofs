import Wikipedia.HopfProblem.SheafHigherDirectImageExtExtendBasic

/-!
# Homology of a functor applied to an extended complex

These isomorphisms compare actual homology and cycles objects.  They combine the
degreewise comparison with the homology comparison for extension by zero.
-/

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open HomologicalComplex

namespace Wikipedia.HopfProblem.SheafHigherDirectImage.ExtBridge

universe u₁ u₂ v₁ v₂

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C] [HasZeroObject C]
  {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D] [HasZeroObject D]
  [CategoryWithHomology D]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

/-- The homology comparison at a degree in the image of the embedding. -/
noncomputable def mapExtendHomologyIso (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : HomologicalComplex C c) (e : c.Embedding c')
    {i : ι} {i' : ι'} (h : e.f i = i') :
    ((F.mapHomologicalComplex c').obj (K.extend e)).homology i' ≅
      ((F.mapHomologicalComplex c).obj K).homology i :=
  homologyMapIso (mapExtendIso F K e) i' ≪≫
    ((F.mapHomologicalComplex c).obj K).extendHomologyIso e h

/-- The cycles comparison underlying the homology comparison. -/
noncomputable def mapExtendCyclesIso (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : HomologicalComplex C c) (e : c.Embedding c')
    {i : ι} {i' : ι'} (h : e.f i = i') :
    ((F.mapHomologicalComplex c').obj (K.extend e)).cycles i' ≅
      ((F.mapHomologicalComplex c).obj K).cycles i :=
  cyclesMapIso (mapExtendIso F K e) i' ≪≫
    ((F.mapHomologicalComplex c).obj K).extendCyclesIso e h

/-- The cycles comparison is induced by the canonical comparison in degree `i`. -/
@[reassoc]
lemma mapExtendCyclesIso_hom_iCycles (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : HomologicalComplex C c) (e : c.Embedding c')
    {i : ι} {i' : ι'} (h : e.f i = i') :
    (mapExtendCyclesIso F K e h).hom ≫ ((F.mapHomologicalComplex c).obj K).iCycles i =
      ((F.mapHomologicalComplex c').obj (K.extend e)).iCycles i' ≫
        F.map (K.extendXIso e h).hom := by
  simp only [mapExtendCyclesIso, Iso.trans_hom, cyclesMapIso_hom, assoc,
    extendCyclesIso_hom_iCycles, cyclesMap_i_assoc, mapExtendIso_hom_f F K e h]
  dsimp only [Functor.mapHomologicalComplex]
  simp only [assoc, Iso.inv_hom_id, comp_id]

/-- The homology comparison sends the class of a cycle to the class of its image. -/
@[reassoc]
lemma homologyπ_mapExtendHomologyIso_hom (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : HomologicalComplex C c) (e : c.Embedding c')
    {i : ι} {i' : ι'} (h : e.f i = i') :
    ((F.mapHomologicalComplex c').obj (K.extend e)).homologyπ i' ≫
        (mapExtendHomologyIso F K e h).hom =
      (mapExtendCyclesIso F K e h).hom ≫
        ((F.mapHomologicalComplex c).obj K).homologyπ i := by
  simp only [mapExtendHomologyIso, mapExtendCyclesIso, Iso.trans_hom,
    homologyMapIso_hom, cyclesMapIso_hom, homologyπ_naturality_assoc, assoc,
    homologyπ_extendHomologyIso_hom]

/-- Naturality in a map between the applied functors. -/
@[reassoc]
lemma mapExtendHomologyIso_hom_natTrans {F G : C ⥤ D}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    (α : F ⟶ G) (K : HomologicalComplex C c) (e : c.Embedding c')
    {i : ι} {i' : ι'} (h : e.f i = i') :
    homologyMap ((NatTrans.mapHomologicalComplex α c').app (K.extend e)) i' ≫
        (mapExtendHomologyIso G K e h).hom =
      (mapExtendHomologyIso F K e h).hom ≫
        homologyMap ((NatTrans.mapHomologicalComplex α c).app K) i := by
  dsimp only [mapExtendHomologyIso, Iso.trans_hom, homologyMapIso]
  rw [← assoc, ← homologyMap_comp, mapExtendIso_hom_natTrans,
    homologyMap_comp, assoc, extendHomologyIso_hom_naturality, assoc]

/-- Naturality in a map of the original complexes. -/
@[reassoc]
lemma mapExtendHomologyIso_hom_naturality (F : C ⥤ D) [F.PreservesZeroMorphisms]
    {K L : HomologicalComplex C c} (φ : K ⟶ L) (e : c.Embedding c')
    {i : ι} {i' : ι'} (h : e.f i = i') :
    homologyMap ((F.mapHomologicalComplex c').map (extendMap φ e)) i' ≫
        (mapExtendHomologyIso F L e h).hom =
      (mapExtendHomologyIso F K e h).hom ≫
        homologyMap ((F.mapHomologicalComplex c).map φ) i := by
  dsimp only [mapExtendHomologyIso, Iso.trans_hom, homologyMapIso]
  rw [← assoc, ← homologyMap_comp, mapExtendIso_hom_naturality,
    homologyMap_comp, assoc, extendHomologyIso_hom_naturality, assoc]

end Wikipedia.HopfProblem.SheafHigherDirectImage.ExtBridge
