import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Actual maps of abelian short-complex kernel/range quotients

The middle component of an actual short-complex map preserves its
actual kernel and carries each actual incoming boundary to the original
target boundary. Quotient descent therefore gives the canonical
homology map, with its literal representative formula.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalMaps

universe u

variable {S T : ShortComplex AddCommGrpCat.{u}} (f : S ⟶ T)

/-- The actual middle component restricted to the original kernel. -/
def abCycleMap : S.g.hom.ker →+ T.g.hom.ker where
  toFun a := ⟨f.τ₂ a, by
    have ha : S.g (a : S.X₂) = 0 := a.property
    change T.g (f.τ₂ (a : S.X₂)) = 0
    rw [← AddCommGrpCat.comp_apply, f.comm₂₃, AddCommGrpCat.comp_apply, ha, map_zero]⟩
  map_zero' := Subtype.ext f.τ₂.hom.map_zero
  map_add' a b := Subtype.ext (f.τ₂.hom.map_add (a : S.X₂) (b : S.X₂))

@[simp] theorem abCycleMap_coe (a : S.g.hom.ker) :
    (abCycleMap f a : T.X₂) = f.τ₂ a := rfl

/-- Actual boundaries go to the boundary of the original first component. -/
theorem abCycleMap_boundary (a : S.X₁) :
    abCycleMap f (S.abToCycles a) = T.abToCycles (f.τ₁ a) :=
  Subtype.ext (ConcreteCategory.congr_hom f.comm₁₂ a).symm

/-- The actual kernel/range quotient map, obtained by true boundary descent. -/
def abQuotientMap : (S.g.hom.ker ⧸ S.abToCycles.range) →+
    (T.g.hom.ker ⧸ T.abToCycles.range) :=
  QuotientAddGroup.lift S.abToCycles.range
    ((QuotientAddGroup.mk' T.abToCycles.range).comp (abCycleMap f)) (by
      intro a ha
      obtain ⟨b, rfl⟩ := ha
      change QuotientAddGroup.mk' T.abToCycles.range (abCycleMap f (S.abToCycles b)) = 0
      rw [abCycleMap_boundary]
      exact (QuotientAddGroup.eq_zero_iff _).mpr ⟨f.τ₁ b, rfl⟩)

@[simp] theorem abQuotientMap_class (a : S.g.hom.ker) :
    abQuotientMap f (QuotientAddGroup.mk' S.abToCycles.range a) =
      QuotientAddGroup.mk' T.abToCycles.range (abCycleMap f a) := rfl

/-- The literal kernel and quotient maps are genuine homology-map data. -/
def abHomologyMapData :
    ShortComplex.LeftHomologyMapData f S.abLeftHomologyData T.abLeftHomologyData where
  φK := AddCommGrpCat.ofHom (abCycleMap f)
  φH := AddCommGrpCat.ofHom (abQuotientMap f)
  commi := by ext a; rfl
  commf' := by ext a; exact abCycleMap_boundary f a
  commπ := by ext a; exact abQuotientMap_class f a

/-- True boundary descent agrees with the canonical native homology map. -/
theorem abQuotientMap_homology :
    ShortComplex.homologyMap f ≫ T.abHomologyIso.hom =
      S.abHomologyIso.hom ≫ AddCommGrpCat.ofHom (abQuotientMap f) := by
  have hm : ShortComplex.leftHomologyMap' f S.abLeftHomologyData T.abLeftHomologyData =
      AddCommGrpCat.ofHom (abQuotientMap f) := (abHomologyMapData f).leftHomologyMap'_eq
  exact (ShortComplex.LeftHomologyData.leftHomologyIso_hom_naturality
    f S.abLeftHomologyData T.abLeftHomologyData).symm.trans
      (congrArg (fun k => S.abHomologyIso.hom ≫ k) hm)

/-- The same canonical square after an actual target short-complex comparison. -/
theorem abQuotientMap_homology_comp {U : ShortComplex AddCommGrpCat.{u}} (e : T ≅ U) :
    S.abHomologyIso.hom ≫ AddCommGrpCat.ofHom (abQuotientMap (f ≫ e.hom)) =
      ShortComplex.homologyMap f ≫ ShortComplex.homologyMap e.hom ≫ U.abHomologyIso.hom :=
  (abQuotientMap_homology (f ≫ e.hom)).symm.trans
    ((congrArg (fun k => k ≫ U.abHomologyIso.hom)
      (ShortComplex.homologyMap_comp f e.hom)).trans (Category.assoc _ _ _))

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalMaps
