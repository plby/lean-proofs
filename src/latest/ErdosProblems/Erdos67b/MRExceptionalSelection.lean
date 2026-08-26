import ErdosProblems.Erdos67b.MRFrequencyClasses
import Mathlib.MeasureTheory.Integral.Average

/-!
# Selecting actual exceptional frequencies

The first moment method selects points inside positive-measure unit cells.
Choosing one parity of the cells gives a one-separated finite sample set,
without replacing the exceptional set by its closure.
-/

open scoped BigOperators Interval
open Finset MeasureTheory

namespace Erdos67b

noncomputable section

/-- A positive-measure set of volume at most one contains a point whose
nonnegative value dominates its integral. No maximum is assumed attained. -/
theorem mrExists_point_ge_setIntegral
    {C : Set ℝ} {g : ℝ → ℝ} (hC0 : volume C ≠ 0) (hC1 : volume C ≤ 1)
    (hint : IntegrableOn g C volume) (hg : ∀ x ∈ C, 0 ≤ g x) :
    ∃ x ∈ C, (∫ y in C, g y) ≤ g x := by
  have hCtop : volume C ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) hC1
  have hCpos : 0 < volume.real C := ENNReal.toReal_pos hC0 hCtop
  have hCreal : volume.real C ≤ 1 := by
    have hh := ENNReal.toReal_mono (by norm_num : (1 : ENNReal) ≠ ⊤) hC1
    simpa only [measureReal_def, ENNReal.toReal_one] using hh
  obtain ⟨x, hx, havg⟩ := exists_setAverage_le hC0 hCtop hint
  rw [setAverage_eq, smul_eq_mul] at havg
  have hh := mul_le_mul_of_nonneg_left havg hCpos.le
  rw [← mul_assoc, mul_inv_cancel₀ hCpos.ne', one_mul] at hh
  exact ⟨x, hx, hh.trans (by nlinarith [hg x hx])⟩

/-- One parity carries at least half of a finite real sum. -/
theorem mrExists_parity_half_sum (I : Finset ℕ) (w : ℕ → ℝ) :
    ∃ r < 2, (∑ j ∈ I, w j) ≤ 2 * ∑ j ∈ I.filter (fun j ↦ j % 2 = r), w j := by
  classical
  have hsets : I.filter (fun j ↦ ¬j % 2 = 0) = I.filter (fun j ↦ j % 2 = 1) := by
    ext j
    rcases Nat.mod_two_eq_zero_or_one j with hj | hj <;> simp [hj]
  have hsplit := Finset.sum_filter_add_sum_filter_not I (fun j ↦ j % 2 = 0) w
  rw [hsets] at hsplit
  rcases le_total (∑ j ∈ I.filter (fun j ↦ j % 2 = 0), w j)
      (∑ j ∈ I.filter (fun j ↦ j % 2 = 1), w j) with hh | hh
  · exact ⟨1, by omega, by linarith⟩
  · exact ⟨0, by omega, by linarith⟩

/-- Points chosen in unit cells of one parity are one-separated. -/
theorem mrUnitCell_same_parity_separated
    (a : ℝ) (x : ℕ → ℝ) {j k : ℕ}
    (hj : x j ∈ Set.Ioc (a + j) (a + j + 1))
    (hk : x k ∈ Set.Ioc (a + k) (a + k + 1))
    (hparity : j % 2 = k % 2) (hne : j ≠ k) :
    1 ≤ |x j - x k| := by
  have horder : j + 2 ≤ k ∨ k + 2 ≤ j := by omega
  rcases horder with horder | horder
  · have hr : (j : ℝ) + 2 ≤ k := by exact_mod_cast horder
    have hdiff : x j - x k ≤ -1 := by linarith [hj.2, hk.1]
    rw [abs_of_nonpos (by linarith : x j - x k ≤ 0)]
    linarith
  · have hr : (k : ℝ) + 2 ≤ j := by exact_mod_cast horder
    have hdiff : 1 ≤ x j - x k := by linarith [hk.2, hj.1]
    rw [abs_of_nonneg (by linarith : 0 ≤ x j - x k)]
    exact hdiff

/-- Finite unit-cell selection. Null cells contribute zero; every selected
point belongs to its actual cell. -/
theorem mrUnitCells_exists_separated_samples
    (I : Finset ℕ) (a : ℝ) (C : ℕ → Set ℝ) (g : ℝ → ℝ)
    (hcell : ∀ j ∈ I, C j ⊆ Set.Ioc (a + j) (a + j + 1))
    (hint : ∀ j ∈ I, IntegrableOn g (C j) volume)
    (hg : ∀ x, 0 ≤ g x) :
    ∃ S : Finset ℝ,
      (∀ t ∈ S, ∃ j ∈ I, t ∈ C j) ∧
      (∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ |s - t|) ∧
      (∑ j ∈ I, ∫ t in C j, g t) ≤ 2 * ∑ t ∈ S, g t := by
  classical
  let A : Finset ℕ := I.filter (fun j ↦ volume (C j) ≠ 0)
  have hactive (j : ℕ) (hj : j ∈ A) : j ∈ I ∧ volume (C j) ≠ 0 := Finset.mem_filter.mp hj
  have hchoices : ∀ j : ℕ, ∃ t : ℝ,
      j ∈ A → t ∈ C j ∧ (∫ u in C j, g u) ≤ g t := by
    intro j
    by_cases hj : j ∈ A
    · have hmeasure : volume (C j) ≤ 1 := by
        calc
          _ ≤ volume (Set.Ioc (a + j) (a + j + 1)) := measure_mono (hcell j (hactive j hj).1)
          _ = _ := by rw [Real.volume_Ioc]; simp only [add_sub_cancel_left, ENNReal.ofReal_one]
      obtain ⟨t, ht, hval⟩ := mrExists_point_ge_setIntegral (hactive j hj).2 hmeasure
        (hint j (hactive j hj).1) (fun t _ ↦ hg t)
      exact ⟨t, fun _ ↦ ⟨ht, hval⟩⟩
    · exact ⟨0, fun h ↦ (hj h).elim⟩
  choose x hx using hchoices
  obtain ⟨r, hr, hhalf⟩ := mrExists_parity_half_sum A (fun j ↦ g (x j))
  let J : Finset ℕ := A.filter (fun j ↦ j % 2 = r)
  let S : Finset ℝ := J.image x
  have hJ (j : ℕ) (hj : j ∈ J) : j ∈ A ∧ j % 2 = r := Finset.mem_filter.mp hj
  have hsep : ∀ j ∈ J, ∀ k ∈ J, j ≠ k → 1 ≤ |x j - x k| := by
    intro j hj k hk hne
    exact mrUnitCell_same_parity_separated a x
      (hcell j (hactive j (hJ j hj).1).1 (hx j (hJ j hj).1).1)
      (hcell k (hactive k (hJ k hk).1).1 (hx k (hJ k hk).1).1)
      ((hJ j hj).2.trans (hJ k hk).2.symm) hne
  have hinj : ∀ j ∈ J, ∀ k ∈ J, x j = x k → j = k := by
    intro j hj k hk heq
    by_contra hne
    have hh := hsep j hj k hk hne
    rw [heq, sub_self, abs_zero] at hh
    norm_num at hh
  have hsum : (∑ j ∈ I, ∫ t in C j, g t) = ∑ j ∈ A, ∫ t in C j, g t := by
    apply (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro j hj hnot
    have hzero : volume (C j) = 0 := by
      by_contra hne
      exact hnot (Finset.mem_filter.mpr ⟨hj, hne⟩)
    rw [Measure.restrict_eq_zero.mpr hzero, integral_zero_measure]
  refine ⟨S, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
    exact ⟨j, (hactive j (hJ j hj).1).1, (hx j (hJ j hj).1).1⟩
  · intro s hs t ht hne
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ht
    exact hsep j hj k hk (fun heq ↦ hne (congrArg x heq))
  · calc
      _ = ∑ j ∈ A, ∫ t in C j, g t := hsum
      _ ≤ ∑ j ∈ A, g (x j) := Finset.sum_le_sum (fun j hj ↦ (hx j hj).2)
      _ ≤ 2 * ∑ j ∈ J, g (x j) := hhalf
      _ = _ := by rw [Finset.sum_image hinj]

/-- The actual exceptional set, clipped to the time window and one unit cell. -/
def mrExceptionalUnitCell (E : Set ℝ) (T : ℝ) (j : ℕ) : Set ℝ :=
  (E ∩ Set.Ioc (-T) T) ∩ Set.Ioc (-T + j) (-T + j + 1)

theorem measurableSet_mrExceptionalUnitCell {E : Set ℝ} (hE : MeasurableSet E) (T : ℝ) (j : ℕ) :
    MeasurableSet (mrExceptionalUnitCell E T j) :=
  (hE.inter measurableSet_Ioc).inter measurableSet_Ioc

theorem mrExceptionalUnitCell_subset (E : Set ℝ) (T : ℝ) (j : ℕ) :
    mrExceptionalUnitCell E T j ⊆ Set.Ioc (-T + j) (-T + j + 1) := Set.inter_subset_right

theorem mrExceptionalUnitCell_window (E : Set ℝ) (T : ℝ) (j : ℕ) :
    mrExceptionalUnitCell E T j ⊆ E ∩ Set.Ioc (-T) T := Set.inter_subset_left

theorem mrExceptionalUnitCell_pairwise (E : Set ℝ) (T : ℝ) :
    Pairwise (fun j k ↦ Disjoint (mrExceptionalUnitCell E T j) (mrExceptionalUnitCell E T k)) := by
  intro j k hne
  rcases lt_or_gt_of_ne hne with hjk | hkj
  · have hreal : (j : ℝ) + 1 ≤ k := by exact_mod_cast hjk
    exact (Set.Ioc_disjoint_Ioc_of_le (show -T + j + 1 ≤ -T + k by linarith)).mono
      (mrExceptionalUnitCell_subset E T j) (mrExceptionalUnitCell_subset E T k)
  · have hreal : (k : ℝ) + 1 ≤ j := by exact_mod_cast hkj
    exact ((Set.Ioc_disjoint_Ioc_of_le (show -T + k + 1 ≤ -T + j by linarith)).mono
      (mrExceptionalUnitCell_subset E T k) (mrExceptionalUnitCell_subset E T j)).symm

/-- Exact finite coverage, with the ceiling-minus-one convention assigning
integer endpoints to the preceding half-open unit cell. -/
theorem mrExceptionalUnitCell_iUnion (E : Set ℝ) (T : ℝ) :
    (⋃ j ∈ Finset.range ⌈2 * T⌉₊, mrExceptionalUnitCell E T j) = E ∩ Set.Ioc (-T) T := by
  ext t
  constructor
  · intro ht
    obtain ⟨j, hj, ht⟩ := Set.mem_iUnion₂.mp ht
    exact mrExceptionalUnitCell_window E T j ht
  · intro ht
    have hy0 : 0 < t + T := by linarith [ht.2.1]
    have hymax : t + T ≤ 2 * T := by linarith [ht.2.2]
    let q : ℕ := ⌈t + T⌉₊
    have hq : 0 < q := Nat.ceil_pos.mpr hy0
    have hqmax : q ≤ ⌈2 * T⌉₊ := Nat.ceil_mono hymax
    have hqcast : ((q - 1 : ℕ) : ℝ) + 1 = q := by exact_mod_cast Nat.sub_add_cancel hq
    have hlo : ((q - 1 : ℕ) : ℝ) < t + T := by
      have hh : (q : ℝ) < t + T + 1 := Nat.ceil_lt_add_one hy0.le
      linarith
    have hhi : t + T ≤ (q - 1 : ℕ) + (1 : ℝ) := by
      have hh : t + T ≤ (q : ℝ) := Nat.le_ceil _
      linarith
    apply Set.mem_iUnion₂.mpr
    refine ⟨q - 1, Finset.mem_range.mpr (by omega), ?_⟩
    exact ⟨ht, ⟨by linarith, by linarith⟩⟩

theorem mrExceptional_integral_eq_sum_cells
    {E : Set ℝ} (hE : MeasurableSet E) {g : ℝ → ℝ} (hg : Continuous g)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, E.indicator g t) =
      ∑ j ∈ Finset.range ⌈2 * T⌉₊, ∫ t in mrExceptionalUnitCell E T j, g t := by
  have hint (j : ℕ) : IntegrableOn g (mrExceptionalUnitCell E T j) volume :=
    ((hg.intervalIntegrable (-T) T).1).mono_set
      (fun t ht ↦ (mrExceptionalUnitCell_window E T j ht).2)
  calc
    _ = ∫ t in Set.Ioc (-T) T ∩ E, g t := by
      rw [intervalIntegral.integral_of_le (by linarith), setIntegral_indicator hE]
    _ = ∫ t in E ∩ Set.Ioc (-T) T, g t := by rw [Set.inter_comm]
    _ = ∫ t in ⋃ j ∈ Finset.range ⌈2 * T⌉₊, mrExceptionalUnitCell E T j, g t := by
      rw [mrExceptionalUnitCell_iUnion]
    _ = _ := integral_biUnion_finset (Finset.range ⌈2 * T⌉₊)
      (fun j _ ↦ measurableSet_mrExceptionalUnitCell hE T j)
      (fun j _ k _ hne ↦ mrExceptionalUnitCell_pairwise E T hne) (fun j _ ↦ hint j)

/-- Select actual exceptional frequencies with the source's factor two.
This includes the empty window and null exceptional sets. -/
theorem mrExists_separated_samples_ge_integral
    {E : Set ℝ} (hE : MeasurableSet E) {g : ℝ → ℝ} (hg : Continuous g)
    (hg0 : ∀ t, 0 ≤ g t) {T : ℝ} (hT : 0 ≤ T) :
    ∃ S : Finset ℝ,
      (∀ t ∈ S, t ∈ E ∧ |t| ≤ T) ∧
      (∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ |s - t|) ∧
      (∫ t in -T..T, E.indicator g t) ≤ 2 * ∑ t ∈ S, g t := by
  have hint (j : ℕ) : IntegrableOn g (mrExceptionalUnitCell E T j) volume :=
    ((hg.intervalIntegrable (-T) T).1).mono_set
      (fun t ht ↦ (mrExceptionalUnitCell_window E T j ht).2)
  obtain ⟨S, hS, hsep, hsum⟩ := mrUnitCells_exists_separated_samples
    (Finset.range ⌈2 * T⌉₊) (-T) (mrExceptionalUnitCell E T) g
    (fun j _ ↦ mrExceptionalUnitCell_subset E T j) (fun j _ ↦ hint j) hg0
  refine ⟨S, ?_, hsep, ?_⟩
  · intro t ht
    obtain ⟨j, hj, htj⟩ := hS t ht
    have hh := mrExceptionalUnitCell_window E T j htj
    exact ⟨hh.1, abs_le.mpr ⟨hh.2.1.le, hh.2.2⟩⟩
  · rw [mrExceptional_integral_eq_sum_cells hE hg hT]
    exact hsum

end

end Erdos67b
