import ErdosProblems.Erdos547.WeightedBinAllocation

/-!
# Weight remaining after small weights and exceptional bins are excluded
-/

namespace Erdos547

open Finset
open scoped BigOperators

variable {I Z : Type*} [DecidableEq I]

theorem sum_weight_sdiff_lower (J E : Finset I) (w : I → ℝ) (hw : ∀ i, w i ≤ 1) :
    (∑ i ∈ J, w i) - E.card ≤ ∑ i ∈ J \ E, w i := by
  have hdis : Disjoint (J \ E) (J ∩ E) := by
    apply Finset.disjoint_left.mpr
    intro i hi hi'
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_inter.mp hi').2
  have hsplit := Finset.sum_union (f := w) hdis
  rw [Finset.sdiff_union_inter] at hsplit
  have hbound : (∑ i ∈ J ∩ E, w i) ≤ E.card := by
    calc
      _ ≤ ∑ _i ∈ J ∩ E, (1 : ℝ) := Finset.sum_le_sum fun i _ ↦ hw i
      _ = ((J ∩ E).card : ℝ) := by simp
      _ ≤ E.card := by exact_mod_cast Finset.card_le_card Finset.inter_subset_right
  linarith only [hsplit, hbound]

open scoped Classical in
theorem allowed_weight_lower (J E : Finset I) (w : I → ℝ) (hw : ∀ i, w i ≤ 1)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    (∑ i ∈ J, w i) - θ * J.card - E.card ≤
      ∑ i ∈ (J.filter (fun i ↦ θ ≤ w i)) \ E, w i := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not J (fun i ↦ θ ≤ w i) w
  have hlow : (∑ i ∈ J.filter (fun i ↦ ¬ θ ≤ w i), w i) ≤ θ * J.card := by
    calc
      _ ≤ ∑ _i ∈ J.filter (fun i ↦ ¬ θ ≤ w i), θ :=
        Finset.sum_le_sum fun i hi ↦ (lt_of_not_ge (Finset.mem_filter.mp hi).2).le
      _ = θ * ((J.filter (fun i ↦ ¬ θ ≤ w i)).card : ℝ) := by simp [mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by exact_mod_cast Finset.card_filter_le J (fun i ↦ ¬ θ ≤ w i)) hθ
  have hdrop := sum_weight_sdiff_lower (J.filter (fun i ↦ θ ≤ w i)) E w hw
  linarith only [hsplit, hlow, hdrop]

theorem card_exceptions_for_two_attachments (Z₀ : Finset Z) (hZ : Z₀.card ≤ 2)
    (B Q : Z → Finset I) (E : Finset I) (b : ℝ) (hb : 0 ≤ b)
    (hB : ∀ z ∈ Z₀, ((B z).card : ℝ) ≤ b)
    (hQ : ∀ z ∈ Z₀, ((Q z).card : ℝ) ≤ b) :
    ((E ∪ Z₀.biUnion (fun z ↦ B z ∪ Q z)).card : ℝ) ≤ E.card + 4 * b := by
  classical
  have hparts : (∑ z ∈ Z₀, ((B z ∪ Q z).card : ℝ)) ≤ 4 * b := by
    calc
      _ ≤ ∑ _z ∈ Z₀, 2 * b := by
        apply Finset.sum_le_sum
        intro z hz
        have hh : ((B z ∪ Q z).card : ℝ) ≤ (B z).card + (Q z).card := by
          exact_mod_cast Finset.card_union_le (B z) (Q z)
        linarith only [hh, hB z hz, hQ z hz]
      _ = (Z₀.card : ℝ) * (2 * b) := by simp
      _ ≤ 4 * b := by
        have hc : (Z₀.card : ℝ) ≤ 2 := by exact_mod_cast hZ
        nlinarith only [hc, hb]
  have hbi : ((Z₀.biUnion (fun z ↦ B z ∪ Q z)).card : ℝ) ≤
      ∑ z ∈ Z₀, ((B z ∪ Q z).card : ℝ) := by
    exact_mod_cast (Finset.card_biUnion_le (s := Z₀) (t := fun z ↦ B z ∪ Q z))
  have hfinal : ((E ∪ Z₀.biUnion (fun z ↦ B z ∪ Q z)).card : ℝ) ≤
      E.card + ((Z₀.biUnion (fun z ↦ B z ∪ Q z)).card : ℝ) := by
    exact_mod_cast Finset.card_union_le E (Z₀.biUnion (fun z ↦ B z ∪ Q z))
  linarith only [hparts, hbi, hfinal]

end Erdos547

#print axioms Erdos547.allowed_weight_lower
#print axioms Erdos547.card_exceptions_for_two_attachments
