import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageFibreNeighborhood

/-!
# Original neighborhood restrictions preserve fibre cohomology

The canonical maps from free open sheaves commute with genuine open
inclusions. Consequently the actual Ext comparisons commute with the
original cohomology-presheaf restriction maps. This is the compatibility
needed to pass from neighborhood classes to the genuine higher-direct-
image stalk; no fibre-comparison isomorphism for the source sheaf is assumed.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.FibreNeighborhood

open HolomorphicSheafCohomology.OpenRestriction
open CuspNormalization.SheafCohomologyFinitePushforward

universe u v u' v' w w'

private theorem comparison_precompose
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [HasExt.{w} C] [HasExt.{w'} D] {Z : C} {A A' : D}
    (η : A ⟶ R.obj Z) (η' : A' ⟶ R.obj Z) (r : A' ⟶ A) (hr : r ≫ η = η')
    (Y : C) (n : ℕ) (a : Ext.{w} Z Y n) :
    (Ext.mk₀ r).comp (ExtComparison.comparison R η Y n a) (zero_add n) =
      ExtComparison.comparison R η' Y n a := by
  subst η'
  exact Ext.mk₀_comp_mk₀_assoc r η (a.mapExactFunctor R)

variable {T X : TopCat.{0}} (i : T ⟶ X) {U V : Opens X} (r : U ⟶ V)
  (hU : ∀ t : T, i t ∈ U) (hV : ∀ t : T, i t ∈ V)

/-- Literal section restriction becomes identity on the entire original fibre. -/
theorem sectionsEquiv_restrict (G : AbelianSheaf T)
    (s : ((pushforward i).obj G).obj.obj (op V)) :
    sectionsEquiv i U hU G (((pushforward i).obj G).obj.map r.op s) =
      sectionsEquiv i V hV G s := by
  change G.obj.map (eqToHom (congrArg op (inverseImage_eq_top i U hU)))
      (G.obj.map ((Opens.map i).map r).op s) =
    G.obj.map (eqToHom (congrArg op (inverseImage_eq_top i V hV))) s
  have he : G.obj.map ((Opens.map i).map r).op ≫
      G.obj.map (eqToHom (congrArg op (inverseImage_eq_top i U hU))) =
        G.obj.map (eqToHom (congrArg op (inverseImage_eq_top i V hV))) :=
    (G.obj.map_comp _ _).symm.trans (congrArg G.obj.map (Subsingleton.elim _ _))
  exact ConcreteCategory.congr_hom he s

/-- The original free-open maps preserve the actual representing morphism. -/
theorem homEquiv_restrict (G : AbelianSheaf T) (a : integerSheaf T ⟶ G) :
    (SheafHigherDirectImage.Sections.freeOpenFunctor X).map r ≫ homEquiv i V hV G a =
      homEquiv i U hU G a := by
  apply (freeHomEquiv U ((pushforward i).obj G)).injective
  apply (sectionsEquiv i U hU G).injective
  rw [SheafHigherDirectImage.Sections.freeHomEquiv_naturality_open,
    sectionsEquiv_restrict i r hU hV, homEquiv_sections, homEquiv_sections]

/-- The genuine integer-unit maps agree after an actual open inclusion. -/
theorem integerUnit_restrict :
    (SheafHigherDirectImage.Sections.freeOpenFunctor X).map r ≫ integerUnit i V hV =
      integerUnit i U hU :=
  homEquiv_restrict i r hU hV (integerSheaf T) (𝟙 _)

variable [T2Space T] (hi : IsClosedMap i) (hfinite : ∀ x : X, (i ⁻¹' {x}).Finite)

/-- The actual forward Ext comparison intertwines the original neighborhood restriction. -/
theorem cohomologyForward_restrict (G : AbelianSheaf T) (n : ℕ)
    (a : CategoryTheory.Sheaf.H.{0} G n) :
    (CategoryTheory.Sheaf.cohomologyPresheaf ((pushforward i).obj G) n).map r.op
      (cohomologyForward i hi hfinite V hV G n a) =
        cohomologyForward i hi hfinite U hU G n a := by
  exact @comparison_precompose
    (AbelianSheaf T) _ _ (AbelianSheaf X) _ _
    (pushforward i) (pushforward_additive i)
    (pushforward_preservesFiniteLimitsAndColimits i hi hfinite).1
    (pushforward_preservesFiniteColimits i hi hfinite)
    (abelianSheaf_hasExt T) (abelianSheaf_hasExt X)
    (integerSheaf T) (freeOpen V) (freeOpen U)
    (integerUnit i V hV) (integerUnit i U hU)
    ((SheafHigherDirectImage.Sections.freeOpenFunctor X).map r)
    (integerUnit_restrict i r hU hV) G n a

/-- The genuine comparison to the fibre cohomology is independent of shrinking the neighborhood. -/
theorem cohomologyEquiv_restrict (G : AbelianSheaf T) (n : ℕ)
    (a : CategoryTheory.Sheaf.H'.{0} ((pushforward i).obj G) n V) :
    cohomologyEquiv i hi hfinite U hU G n
      ((CategoryTheory.Sheaf.cohomologyPresheaf ((pushforward i).obj G) n).map r.op a) =
        cohomologyEquiv i hi hfinite V hV G n a := by
  obtain ⟨b, rfl⟩ := (cohomologyForward_bijective i hi hfinite V hV G n).surjective a
  rw [cohomologyForward_restrict]
  exact (cohomologyEquiv i hi hfinite U hU G n).apply_symm_apply b |>.trans
    ((cohomologyEquiv i hi hfinite V hV G n).apply_symm_apply b).symm

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.FibreNeighborhood
