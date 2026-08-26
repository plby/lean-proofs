import ErdosProblems.Erdos547.RegularityManyTypical

/-!
# Removing the few rows with too many exceptional pairs
-/

namespace Erdos547

open Finset
open scoped BigOperators

open scoped Classical in
theorem card_large_rows_of_sum_le {I : Type*} (F : Finset I) (f : I → ℕ)
    (t b : ℝ) (ht : 0 < t) (hsum : (∑ i ∈ F, (f i : ℝ)) ≤ b * t) :
    ((F.filter (fun i ↦ t < (f i : ℝ))).card : ℝ) ≤ b := by
  classical
  let B := F.filter (fun i ↦ t < (f i : ℝ))
  have hlow : (B.card : ℝ) * t ≤ ∑ i ∈ F, (f i : ℝ) := by
    calc
      _ = ∑ _i ∈ B, t := by simp
      _ ≤ ∑ i ∈ B, (f i : ℝ) := Finset.sum_le_sum (fun i hi ↦ (Finset.mem_filter.mp hi).2.le)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ ↦ Nat.cast_nonneg _)
  exact (mul_le_mul_iff_of_pos_right ht).mp (hlow.trans hsum)

open scoped Classical in
theorem exists_row_clean_subfamily {I : Type*} [DecidableEq I]
    (F : Finset I) (R : I → I → Prop) [DecidableRel R]
    (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (hsum : (∑ i ∈ F, ((F.filter (R i)).card : ℝ)) ≤ δ ^ 2 * (F.card : ℝ) ^ 2) :
    ∃ J ⊆ F, ((F \ J).card : ℝ) ≤ δ * F.card ∧ (F.card : ℝ) ≤ 2 * J.card ∧
      ∀ i ∈ J, ((J.filter (R i)).card : ℝ) ≤ 2 * δ * J.card := by
  classical
  by_cases hF : F.Nonempty
  · let B := F.filter (fun i ↦ δ * F.card < ((F.filter (R i)).card : ℝ))
    let J := F \ B
    have hFpos : (0 : ℝ) < F.card := by exact_mod_cast hF.card_pos
    have hB : (B.card : ℝ) ≤ δ * F.card := by
      apply card_large_rows_of_sum_le F (fun i ↦ (F.filter (R i)).card)
        (δ * F.card) (δ * F.card) (mul_pos hδ hFpos)
      nlinarith only [hsum]
    have hBF : B ⊆ F := Finset.filter_subset _ _
    have hcard : (J.card : ℝ) + B.card = F.card := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card hBF
    have hhalf : (F.card : ℝ) ≤ 2 * J.card := by
      have hh := mul_le_mul_of_nonneg_right hδhalf hFpos.le
      linarith only [hB, hcard, hh]
    refine ⟨J, Finset.sdiff_subset, ?_, hhalf, ?_⟩
    · have he : F \ J = B := by
        ext i
        simp only [J, Finset.mem_sdiff]
        constructor
        · intro hh
          by_contra hn
          exact hh.2 ⟨hh.1, hn⟩
        · intro hi
          exact ⟨hBF hi, fun hh ↦ hh.2 hi⟩
      rw [he]
      exact hB
    · intro i hi
      obtain ⟨hiF, hiB⟩ := Finset.mem_sdiff.mp hi
      have hrow : ((F.filter (R i)).card : ℝ) ≤ δ * F.card := by
        by_contra hn
        exact hiB (Finset.mem_filter.mpr ⟨hiF, lt_of_not_ge hn⟩)
      have hmono : ((J.filter (R i)).card : ℝ) ≤ (F.filter (R i)).card := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset)
      have hh := mul_le_mul_of_nonneg_left hhalf hδ.le
      nlinarith only [hmono, hrow, hh]
  · have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    subst F
    exact ⟨∅, Finset.Subset.refl _, by simp, by simp, by simp⟩

end Erdos547

#print axioms Erdos547.exists_row_clean_subfamily
