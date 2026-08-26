import ErdosProblems.Erdos1038.Definitions

/-!
# Elementary polynomial and measure-theoretic facts for Erdős problem 1038

This file extracts the consequences of `IsAdmissible` that are used throughout
the proof: all roots are accounted for, the polynomial splits, its evaluation
is the product of its linear factors, and its strict unit sublevel set has
finite Lebesgue measure.
-/

open scoped ENNReal Real
open MeasureTheory Set Polynomial

namespace Erdos1038

noncomputable section

namespace IsAdmissible

/-- An admissible polynomial is monic. -/
theorem monic {f : Polynomial ℝ} (hf : IsAdmissible f) : f.Monic :=
  hf.1

/-- An admissible polynomial is not the constant polynomial one. -/
theorem ne_one {f : Polynomial ℝ} (hf : IsAdmissible f) : f ≠ 1 :=
  hf.2.1

/-- The root multiset of an admissible polynomial has full cardinality. -/
theorem card_roots_eq_natDegree {f : Polynomial ℝ} (hf : IsAdmissible f) :
    f.roots.card = f.natDegree := by
  apply Nat.le_antisymm f.card_roots'
  rw [← hf.2.2]
  exact Multiset.card_le_card (Multiset.filter_le _ _)

/-- An admissible real polynomial splits over the reals. -/
theorem splits {f : Polynomial ℝ} (hf : IsAdmissible f) : f.Splits :=
  Polynomial.splits_iff_card_roots.mpr hf.card_roots_eq_natDegree

/-- Every root of an admissible polynomial belongs to `[-1, 1]`. -/
theorem root_mem_Icc {f : Polynomial ℝ} (hf : IsAdmissible f) {r : ℝ}
    (hr : r ∈ f.roots) : r ∈ Set.Icc (-1 : ℝ) 1 := by
  let p : ℝ → Prop := fun x ↦ x ∈ Set.Icc (-1 : ℝ) 1
  have hfilter : f.roots.filter p = f.roots := by
    apply Multiset.eq_of_le_of_card_le (Multiset.filter_le _ _)
    rw [hf.card_roots_eq_natDegree, hf.2.2]
  exact (Multiset.filter_eq_self.mp hfilter) r hr

/-- The exact monic root-product formula for an admissible polynomial. -/
theorem eval_eq_prod_roots {f : Polynomial ℝ} (hf : IsAdmissible f) (x : ℝ) :
    f.eval x = (f.roots.map fun r ↦ x - r).prod :=
  hf.splits.eval_eq_prod_roots_of_monic hf.monic x

/-- Taking absolute values in the exact root-product formula. -/
theorem abs_eval_eq_prod_abs_roots {f : Polynomial ℝ} (hf : IsAdmissible f) (x : ℝ) :
    |f.eval x| = (f.roots.map fun r ↦ |x - r|).prod := by
  rw [hf.eval_eq_prod_roots]
  induction f.roots using Multiset.induction_on with
  | empty => simp
  | cons r s ih => simp [ih, abs_mul]

end IsAdmissible

/-- The strict unit sublevel set of any real polynomial is open. -/
theorem isOpen_sublevelSet (f : Polynomial ℝ) : IsOpen (sublevelSet f) := by
  simpa only [sublevelSet] using! isOpen_lt f.continuous.abs continuous_const

/-- The strict unit sublevel set of any real polynomial is measurable. -/
theorem measurableSet_sublevelSet (f : Polynomial ℝ) : MeasurableSet (sublevelSet f) :=
  (isOpen_sublevelSet f).measurableSet

namespace IsAdmissible

/-- The strict unit sublevel set of an admissible polynomial is contained in
the fixed bounded interval `(-2, 2)`. -/
theorem sublevelSet_subset_Ioo {f : Polynomial ℝ} (hf : IsAdmissible f) :
    sublevelSet f ⊆ Set.Ioo (-2 : ℝ) 2 := by
  intro x hx
  change |f.eval x| < 1 at hx
  constructor
  · by_contra hleft
    have hxle : x ≤ -2 := le_of_not_gt hleft
    have hone : 1 ≤ |f.eval x| := by
      rw [hf.abs_eval_eq_prod_abs_roots]
      apply Multiset.one_le_prod
      intro y hy
      obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hy
      have hrIcc := hf.root_mem_Icc hr
      rw [abs_of_nonpos (by linarith [hrIcc.1])]
      linarith [hrIcc.1]
    exact (not_lt_of_ge hone) hx
  · by_contra hright
    have hxge : 2 ≤ x := le_of_not_gt hright
    have hone : 1 ≤ |f.eval x| := by
      rw [hf.abs_eval_eq_prod_abs_roots]
      apply Multiset.one_le_prod
      intro y hy
      obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hy
      have hrIcc := hf.root_mem_Icc hr
      rw [abs_of_nonneg (by linarith [hrIcc.2])]
      linarith [hrIcc.2]
    exact (not_lt_of_ge hone) hx

/-- The strict unit sublevel set of an admissible polynomial has finite
Lebesgue measure. -/
theorem sublevelVolume_lt_top {f : Polynomial ℝ} (hf : IsAdmissible f) :
    sublevelVolume f < ⊤ := by
  exact (measure_mono hf.sublevelSet_subset_Ioo).trans_lt measure_Ioo_lt_top

end IsAdmissible

end

end Erdos1038
