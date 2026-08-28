import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalCategoryDifferential
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Exactness of the actual mapped categorical total complex

The canonical binary-biproduct comparisons identify actual cycles and
actual preimages with the literal signed group total complex. These
lemmas are used with the original stalk functors, where the diagram
chase has supplied the required exactness.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalCategory.Data

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {R00 R10 R01 R20 R11 R02 R30 R21 R12 R03 : C}
  (D : Data R00 R10 R01 R20 R11 R02 R30 R21 R12 R03)
  (F : C ⥤ AddCommGrpCat.{w}) [F.Additive]

/-- Exactness at the actual degree-zero term. -/
theorem map_initial_exact {A : C} (ι : A ⟶ R00) (hzero : ι ≫ D.d0 = 0)
    (h : Function.Exact (F.map ι).hom (D.mapData F).d0) :
    ((ShortComplex.mk ι D.d0 hzero).map F).Exact := by
  apply (ShortComplex.ab_exact_iff _).mpr
  intro s hs
  change F.map D.d0 s = 0 at hs
  have hclosed : (D.mapData F).d0 s = 0 := by
    rw [← D.oneEquiv_map_d0 F s, hs, map_zero]
  exact (h s).mp hclosed

/-- Exactness at the actual degree-one term. -/
theorem map_oneComplex_exact
    (h : Function.Exact (D.mapData F).d0 (D.mapData F).d1) :
    (D.oneComplex.map F).Exact := by
  apply (ShortComplex.ab_exact_iff _).mpr
  intro s hs
  change F.map D.d1 s = 0 at hs
  have hclosed : (D.mapData F).d1 (D.oneEquiv F s) = 0 := by
    rw [← D.twoEquiv_map_d1 F s, hs, map_zero]
  obtain ⟨t, ht⟩ := (h (D.oneEquiv F s)).mp hclosed
  refine ⟨t, (D.oneEquiv F).injective ?_⟩
  exact (D.oneEquiv_map_d0 F t).trans ht

/-- Exactness at the actual degree-two term. -/
theorem map_twoComplex_exact
    (h : Function.Exact (D.mapData F).d1 (D.mapData F).d2) :
    (D.twoComplex.map F).Exact := by
  apply (ShortComplex.ab_exact_iff _).mpr
  intro s hs
  change F.map D.d2 s = 0 at hs
  have hclosed : (D.mapData F).d2 (D.twoEquiv F s) = 0 := by
    rw [← D.threeEquiv_map_d2 F s, hs, map_zero]
  obtain ⟨t, ht⟩ := (h (D.twoEquiv F s)).mp hclosed
  refine ⟨(D.oneEquiv F).symm t, (D.twoEquiv F).injective ?_⟩
  change D.twoEquiv F (F.map D.d1 ((D.oneEquiv F).symm t)) = D.twoEquiv F s
  rw [D.twoEquiv_map_d1, AddEquiv.apply_symm_apply]
  exact ht

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalCategory.Data
