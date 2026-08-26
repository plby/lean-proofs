/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceGridGeometry

/-!
# Finite rectangular approximants of the variable Maynard candidate

Only cells whose upper corner lies in the unit simplex are retained.
They are pairwise disjoint, so the finite sum is bounded by one without
any factor equal to the number of cells.
-/

namespace Erdos4b

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

def sourceSimplexGrid (K n : ℕ) : Finset (Fin K → Fin (n + 1)) :=
  Finset.univ.filter (fun j ↦ (∑ i : Fin K, sourceGridUpper n (j i)) ≤ (1 : ℝ))

theorem mem_sourceSimplexGrid {K n : ℕ} {j : Fin K → Fin (n + 1)} :
    j ∈ sourceSimplexGrid K n ↔ (∑ i, sourceGridUpper n (j i)) ≤ (1 : ℝ) := by
  simp only [sourceSimplexGrid, Finset.mem_filter, Finset.mem_univ, true_and]

def sourceGridFactors (K : ℕ) (A : ℝ) (n : ℕ) :
    (Fin K → Fin (n + 1)) → Fin K → ℝ → ℝ :=
  sourceRectangleFactors (fun j i ↦ sourceGridLower n (j i))
    (fun j i ↦ sourceGridUpper n (j i))
    (fun j i ↦ VariableMaynard.factor A ((K : ℝ) * sourceGridUpper n (j i)))

def sourceGridTerm (K : ℕ) (A : ℝ) (n : ℕ) (j : Fin K → Fin (n + 1)) (t : Fin K → ℝ) : ℝ :=
  ∏ i, sourceGridFactors K A n j i (t i)

def sourceGridValue (K : ℕ) (A : ℝ) (n : ℕ) : (Fin K → ℝ) → ℝ :=
  sourceTensorValue (sourceSimplexGrid K n) (sourceGridFactors K A n)

theorem sourceGridTerm_nonzero_coordinates {K n : ℕ} {A : ℝ}
    {j : Fin K → Fin (n + 1)} {t : Fin K → ℝ} (hne : sourceGridTerm K A n j t ≠ 0) :
    ∀ i, t i ∈ Set.Ioo (sourceGridLower n (j i)) (sourceGridUpper n (j i)) := by
  intro i
  have hi := (Finset.prod_ne_zero_iff.mp hne) i (Finset.mem_univ i)
  by_contra ht
  apply hi
  simp only [sourceGridFactors, sourceRectangleFactors, sourceIntervalIndicator,
    Set.indicator_of_notMem ht, mul_zero]

theorem sourceGridTerm_nonzero_unique {K n : ℕ} {A : ℝ}
    {j k : Fin K → Fin (n + 1)} {t : Fin K → ℝ}
    (hj : sourceGridTerm K A n j t ≠ 0) (hk : sourceGridTerm K A n k t ≠ 0) : j = k := by
  funext i
  exact sourceGridCell_unique (sourceGridTerm_nonzero_coordinates hj i)
    (sourceGridTerm_nonzero_coordinates hk i)

theorem sourceGridValue_zero_or_term (K : ℕ) (A : ℝ) (n : ℕ) (t : Fin K → ℝ) :
    sourceGridValue K A n t = 0 ∨
      ∃ j ∈ sourceSimplexGrid K n, sourceGridValue K A n t = sourceGridTerm K A n j t := by
  classical
  by_cases hn : ∃ j ∈ sourceSimplexGrid K n, sourceGridTerm K A n j t ≠ 0
  · obtain ⟨j, hj, hjne⟩ := hn
    refine Or.inr ⟨j, hj, ?_⟩
    apply Finset.sum_eq_single j
    · intro k hk hkj
      by_contra hkne
      exact hkj (sourceGridTerm_nonzero_unique hkne hjne)
    · exact fun h ↦ (h hj).elim
  · left
    apply Finset.sum_eq_zero
    intro j hj
    exact not_ne_iff.mp (fun h ↦ hn ⟨j, hj, h⟩)

theorem sourceGridTerm_bounds {K n : ℕ} {A : ℝ} (hA : 0 < A)
    (j : Fin K → Fin (n + 1)) (t : Fin K → ℝ) :
    0 ≤ sourceGridTerm K A n j t ∧ sourceGridTerm K A n j t ≤ 1 := by
  have hfactor (i : Fin K) : 0 ≤ sourceGridFactors K A n j i (t i) ∧
      sourceGridFactors K A n j i (t i) ≤ 1 := by
    have hu : 0 ≤ (K : ℝ) * sourceGridUpper n (j i) :=
      mul_nonneg (Nat.cast_nonneg K)
        ((sourceGridLower_nonneg n (j i)).trans (sourceGridLower_lt_upper n (j i)).le)
    by_cases ht : t i ∈ Set.Ioo (sourceGridLower n (j i)) (sourceGridUpper n (j i))
    · simp only [sourceGridFactors, sourceRectangleFactors, sourceIntervalIndicator,
        Set.indicator_of_mem ht, mul_one]
      exact ⟨VariableMaynard.factor_nonneg hA hu, VariableMaynard.factor_le_one hA hu⟩
    · simp only [sourceGridFactors, sourceRectangleFactors, sourceIntervalIndicator,
        Set.indicator_of_notMem ht, mul_zero, le_refl, zero_le_one, and_self]
  exact ⟨Finset.prod_nonneg (fun i _ ↦ (hfactor i).1),
    Finset.prod_le_one (fun i _ ↦ (hfactor i).1) (fun i _ ↦ (hfactor i).2)⟩

theorem sourceGridValue_bounds {K n : ℕ} {A : ℝ} (hA : 0 < A) (t : Fin K → ℝ) :
    0 ≤ sourceGridValue K A n t ∧ sourceGridValue K A n t ≤ 1 := by
  rcases sourceGridValue_zero_or_term K A n t with hz | ⟨j, hj, heq⟩
  · rw [hz]
    norm_num
  · rw [heq]
    exact sourceGridTerm_bounds hA j t

theorem sourceGridValue_simplexSupported (K : ℕ) (A : ℝ) (n : ℕ) :
    BoundedGaps.Maynard.MaynardSimplexSupported K (sourceGridValue K A n) := by
  intro t ht
  apply Finset.sum_eq_zero
  intro j hj
  by_contra hne
  have hcell := sourceGridTerm_nonzero_coordinates (K := K) (A := A) (n := n) (j := j) hne
  apply ht
  constructor
  · intro i hi
    have hti := sourceGridCell_subset_unit n (j i) (hcell i)
    exact ⟨hti.1.le, hti.2.le⟩
  · exact (Finset.sum_le_sum (fun i _ ↦ (hcell i).2.le)).trans (mem_sourceSimplexGrid.mp hj)

theorem sourceGridTerm_eq_sample {K n : ℕ} {A : ℝ} {t : Fin K → ℝ}
    (ht : ∀ i, t i ∈ Set.Ioo (0 : ℝ) 1) (hregular : ∀ i, SourceGridRegular (t i)) :
    sourceGridTerm K A n (fun i ↦ sourceGridIndex n (ht i)) t =
      VariableMaynard.product K A (fun i ↦ sourceGridUpperSample n (t i)) := by
  apply Finset.prod_congr rfl
  intro i hi
  have hcell := mem_sourceGridIndex (ht i) (hregular i) n
  simp only [sourceGridFactors, sourceRectangleFactors, sourceIntervalIndicator,
    Set.indicator_of_mem hcell, mul_one]
  rfl

theorem sourceGridValue_eq_sample_of_selected {K n : ℕ} {A : ℝ} {t : Fin K → ℝ}
    (ht : ∀ i, t i ∈ Set.Ioo (0 : ℝ) 1) (hregular : ∀ i, SourceGridRegular (t i))
    (hselected : (fun i ↦ sourceGridIndex n (ht i)) ∈ sourceSimplexGrid K n) :
    sourceGridValue K A n t =
      VariableMaynard.product K A (fun i ↦ sourceGridUpperSample n (t i)) := by
  classical
  rw [← sourceGridTerm_eq_sample ht hregular]
  apply Finset.sum_eq_single (fun i ↦ sourceGridIndex n (ht i))
  · intro j hj hne
    by_contra hterm
    apply hne
    funext i
    exact sourceGridCell_unique (sourceGridTerm_nonzero_coordinates hterm i)
      (mem_sourceGridIndex (ht i) (hregular i) n)
  · exact fun h ↦ (h hselected).elim

theorem eventually_sourceGridIndex_selected {K : ℕ} {t : Fin K → ℝ}
    (ht : ∀ i, t i ∈ Set.Ioo (0 : ℝ) 1) (hsum : (∑ i, t i) < 1) :
    ∀ᶠ n in atTop, (fun i ↦ sourceGridIndex n (ht i)) ∈ sourceSimplexGrid K n := by
  have hl := tendsto_finsetSum (Finset.univ : Finset (Fin K))
    (fun i _ ↦ tendsto_sourceGridUpperSample (ht i).1.le)
  filter_upwards [hl.eventually (Iio_mem_nhds hsum)] with n hn
  apply mem_sourceSimplexGrid.mpr
  exact hn.le

end

end Erdos4b
