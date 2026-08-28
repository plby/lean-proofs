import Wikipedia.HopfProblem.SheafLerayCurveCyclesResolutionHomology
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# The actual cycles Leray sequence in every degree

For the original complex `K`, injectivity of `K.X n` gives the genuine
sequence
`0 → Ext¹(A,ZⁿK) → Hⁿ⁺¹(Hom(A,K)) → Hom(A,Hⁿ⁺¹K) → Ext²(A,ZⁿK)`.
The maps come from the native augmented cycles resolution and its two
actual Ext connecting maps. No tail, reindexing, or replacement
cohomology theory is used.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

namespace Wikipedia.HopfProblem.SheafLerayCurve.Abstract

open SheafLerayLowDegrees.Abstract

private theorem first_composite_zero {D : Type*} [Category D] [HasZeroMorphisms D]
    {X B B' H H' : D} (f : X ⟶ B) (g : B ⟶ H) (e : B ≅ B') (d : H ≅ H')
    (hfg : f ≫ g = 0) : (f ≫ e.hom) ≫ (e.inv ≫ g ≫ d.hom) = 0 := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc, reassoc_of% hfg, zero_comp]

private theorem second_composite_zero {D : Type*} [Category D] [HasZeroMorphisms D]
    {B B' H H' T : D} (f : B ⟶ H) (g : H ⟶ T) (e : B ≅ B') (d : H ≅ H')
    (hfg : f ≫ g = 0) : (e.inv ≫ f ≫ d.hom) ≫ (d.inv ≫ g) = 0 := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc, hfg, comp_zero]

private theorem iso_cancel_comp {D : Type*} [Category D] {B B' H H' : D}
    (f : B ⟶ H) (e : B ≅ B') (d : H ≅ H') :
    e.hom ≫ (e.inv ≫ f ≫ d.hom) = f ≫ d.hom := by
  simp only [Iso.hom_inv_id_assoc]

private theorem iso_cancel_comp_id {D : Type*} [Category D] {H H' T : D}
    (f : H ⟶ T) (d : H ≅ H') : d.hom ≫ (d.inv ≫ f) = f ≫ 𝟙 T := by
  simp only [Iso.hom_inv_id_assoc, Category.comp_id]

universe u

variable {C : Type u} [Category.{0} C] [Abelian C] [HasExt.{0} C]
  (A : C) (K : CochainComplex C ℕ) (n : ℕ)

/-- The actual edge map through the original degree-`n+1` homology quotient. -/
def cyclesEdgeMap : (homComplex A K).homology (n + 1) ⟶
    AddCommGrpCat.of (A ⟶ K.homology (n + 1)) :=
  (cyclesMiddleIso A K n).inv ≫ Core.edgeMap A (cyclesResolution K n) ≫
    (extZeroHomIso A (K.homology (n + 1))).hom

/-- The transgression is the composite of the two genuine Ext connecting maps. -/
def cyclesTransgression : AddCommGrpCat.of (A ⟶ K.homology (n + 1)) ⟶
    AddCommGrpCat.of (Ext A (K.cycles n) 2) :=
  (extZeroHomIso A (K.homology (n + 1))).inv ≫
    Core.transgression A (cyclesResolution K n)

theorem cyclesEdgeMap_transgression :
    cyclesEdgeMap A K n ≫ cyclesTransgression A K n = 0 :=
  second_composite_zero (Core.edgeMap A (cyclesResolution K n))
    (Core.transgression A (cyclesResolution K n)) (cyclesMiddleIso A K n)
    (extZeroHomIso A (K.homology (n + 1)))
    (Core.edgeMap_transgression A (cyclesResolution K n))

/-- The actual right three terms of the all-degree cycles sequence. -/
def cyclesSecondComplex : ShortComplex AddCommGrpCat :=
  ShortComplex.mk (cyclesEdgeMap A K n) (cyclesTransgression A K n)
    (cyclesEdgeMap_transgression A K n)

variable [Injective (K.X n)]

/-- The genuine Ext-degree-one injection, followed by the native middle comparison. -/
def cyclesFirstMap : AddCommGrpCat.of (Ext A (K.cycles n) 1) ⟶
    (homComplex A K).homology (n + 1) := by
  letI : Injective (cyclesResolution K n).complex.X₁ := inferInstanceAs (Injective (K.X n))
  exact Core.firstMap A (cyclesResolution K n) ≫ (cyclesMiddleIso A K n).hom

theorem cyclesFirstMap_edgeMap : cyclesFirstMap A K n ≫ cyclesEdgeMap A K n = 0 := by
  let : Injective (cyclesResolution K n).complex.X₁ := inferInstanceAs (Injective (K.X n))
  exact first_composite_zero (Core.firstMap A (cyclesResolution K n))
    (Core.edgeMap A (cyclesResolution K n)) (cyclesMiddleIso A K n)
    (extZeroHomIso A (K.homology (n + 1)))
    (Core.firstMap_edgeMap A (cyclesResolution K n))

/-- The actual first three terms of the all-degree cycles sequence. -/
def cyclesFirstComplex : ShortComplex AddCommGrpCat :=
  ShortComplex.mk (cyclesFirstMap A K n) (cyclesEdgeMap A K n)
    (cyclesFirstMap_edgeMap A K n)

theorem cyclesSecondComplex_f_eq_cyclesFirstComplex_g :
    (cyclesSecondComplex A K n).f = (cyclesFirstComplex A K n).g := rfl

instance cyclesFirstMap_mono : Mono (cyclesFirstMap A K n) := by
  let : Injective (cyclesResolution K n).complex.X₁ := inferInstanceAs (Injective (K.X n))
  let : Mono (Core.firstMap A (cyclesResolution K n)) :=
    Core.firstMap_mono A (cyclesResolution K n)
  change Mono (Core.firstMap A (cyclesResolution K n) ≫ (cyclesMiddleIso A K n).hom)
  infer_instance

/-- Exactness at the actual homology of the original Hom complex. -/
theorem cyclesFirstComplex_exact : (cyclesFirstComplex A K n).Exact := by
  let : Injective (cyclesResolution K n).complex.X₁ := inferInstanceAs (Injective (K.X n))
  let e : Core.firstComplex A (cyclesResolution K n) ≅ cyclesFirstComplex A K n :=
    ShortComplex.isoMk (Iso.refl _) (cyclesMiddleIso A K n)
      (extZeroHomIso A (K.homology (n + 1)))
      (Category.id_comp _)
      (iso_cancel_comp (Core.edgeMap A (cyclesResolution K n))
        (cyclesMiddleIso A K n) (extZeroHomIso A (K.homology (n + 1))))
  exact ShortComplex.exact_of_iso e (Core.firstComplex_exact A (cyclesResolution K n))

/-- Exactness at actual homology-valued morphisms. -/
theorem cyclesSecondComplex_exact : (cyclesSecondComplex A K n).Exact := by
  let : Injective (cyclesResolution K n).complex.X₁ := inferInstanceAs (Injective (K.X n))
  let e : Core.secondComplex A (cyclesResolution K n) ≅ cyclesSecondComplex A K n :=
    ShortComplex.isoMk (cyclesMiddleIso A K n) (extZeroHomIso A (K.homology (n + 1)))
      (Iso.refl _)
      (iso_cancel_comp (Core.edgeMap A (cyclesResolution K n))
        (cyclesMiddleIso A K n) (extZeroHomIso A (K.homology (n + 1))))
      (iso_cancel_comp_id (Core.transgression A (cyclesResolution K n))
        (extZeroHomIso A (K.homology (n + 1))))
  exact ShortComplex.exact_of_iso e (Core.secondComplex_exact A (cyclesResolution K n))

theorem cyclesFirstMap_injective : Function.Injective (cyclesFirstMap A K n) :=
  (AddCommGrpCat.mono_iff_injective (cyclesFirstMap A K n)).mp inferInstance

theorem cycles_exact_first_edge :
    Function.Exact (cyclesFirstMap A K n) (cyclesEdgeMap A K n) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp (cyclesFirstComplex_exact A K n)

theorem cycles_exact_edge_transgression :
    Function.Exact (cyclesEdgeMap A K n) (cyclesTransgression A K n) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp (cyclesSecondComplex_exact A K n)

/-- The complete native all-degree cycles sequence, including initial injectivity. -/
theorem cycles_lowDegree_exact :
    Function.Injective (cyclesFirstMap A K n) ∧
      Function.Exact (cyclesFirstMap A K n) (cyclesEdgeMap A K n) ∧
        Function.Exact (cyclesEdgeMap A K n) (cyclesTransgression A K n) :=
  ⟨cyclesFirstMap_injective A K n, cycles_exact_first_edge A K n,
    cycles_exact_edge_transgression A K n⟩

end Wikipedia.HopfProblem.SheafLerayCurve.Abstract
