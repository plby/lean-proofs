import ErdosProblems.Erdos747.ConditionalThinning

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Splitting global failures into missing and present exceptions -/

/-- An upper-bad triple is either a missing upper-bad triple, or a present
edge that violates the corresponding present-edge upper bound. -/
lemma globalUpperBad_subset_nonedges_union_presentExceptions
    {n : ℕ} (H : Finset (Edge n)) (L delta : ℝ)
    (hL : 1 + delta ≤ L) :
    (allEdges n).filter (fun Z ↦
        ¬ CompletionWeightUpperBound H L Z) ⊆
      coarseUpperBadNonedges n H L ∪
        presentUpperWeightExceptions H delta := by
  intro Z hZ
  rcases Finset.mem_filter.mp hZ with ⟨hZall, hbad⟩
  by_cases hZH : Z ∈ H
  · apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    refine ⟨hZH, ?_⟩
    unfold CompletionWeightUpperBound at hbad
    have htarget : 0 ≤ matchingWeightTarget n H := by
      unfold matchingWeightTarget
      positivity
    exact (mul_le_mul_of_nonneg_right hL htarget).trans_lt
      (lt_of_not_ge hbad)
  · apply Finset.mem_union_left
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_sdiff.mpr ⟨hZall, hZH⟩, hbad⟩

/-- The cardinal form of the preceding splitting lemma. -/
lemma globalUpperBad_card_le_nonedge_add_presentExceptions
    {n : ℕ} (H : Finset (Edge n)) (L delta : ℝ)
    (hL : 1 + delta ≤ L) :
    ((allEdges n).filter (fun Z ↦
        ¬ CompletionWeightUpperBound H L Z)).card ≤
      (coarseUpperBadNonedges n H L).card +
        (presentUpperWeightExceptions H delta).card := by
  exact (Finset.card_le_card
    (globalUpperBad_subset_nonedges_union_presentExceptions H L delta hL)).trans
      (Finset.card_union_le _ _)

/-- A failed global upper-spread conclusion, after charging the genuinely
exceptional present edges, leaves more than `2*d` upper-bad nonedges. -/
lemma coarseUpperBadNonedges_card_gt_two_mul_of_not_global
    {n d : ℕ} {H : Finset (Edge n)} {L delta eta : ℝ}
    (hL : 1 + delta ≤ L)
    (hbudget : ((2 * d : ℕ) : ℝ) +
        (presentUpperWeightExceptions H delta).card ≤
      eta * (allEdges n).card)
    (hfail : ¬ GlobalUpperWeightSpread n H L eta) :
    2 * d < (coarseUpperBadNonedges n H L).card := by
  have hbad : eta * (allEdges n).card <
      (((allEdges n).filter fun Z ↦
        ¬ CompletionWeightUpperBound H L Z).card : ℝ) := by
    unfold GlobalUpperWeightSpread at hfail
    exact lt_of_not_ge hfail
  have hcard := globalUpperBad_card_le_nonedge_add_presentExceptions
    H L delta hL
  have hcardR :
      (((allEdges n).filter fun Z ↦
          ¬ CompletionWeightUpperBound H L Z).card : ℝ) ≤
        (coarseUpperBadNonedges n H L).card +
          (presentUpperWeightExceptions H delta).card := by
    exact_mod_cast hcard
  have hdR : ((2 * d : ℕ) : ℝ) <
      (coarseUpperBadNonedges n H L).card := by
    linarith
  exact_mod_cast hdR

/-- Present-edge spreading supplies the present-exception charge in the
upper split. -/
lemma coarseUpperBadNonedges_card_gt_two_mul_of_not_global_of_spread
    {n d : ℕ} {H : Finset (Edge n)}
    {L delta etaPresent etaGlobal : ℝ}
    (hL : 1 + delta ≤ L)
    (hspread : PresentWeightSpread H delta etaPresent)
    (hbudget : ((2 * d : ℕ) : ℝ) + etaPresent * H.card ≤
      etaGlobal * (allEdges n).card)
    (hfail : ¬ GlobalUpperWeightSpread n H L etaGlobal) :
    2 * d < (coarseUpperBadNonedges n H L).card := by
  apply coarseUpperBadNonedges_card_gt_two_mul_of_not_global
    hL _ hfail
  exact (add_le_add le_rfl
    (presentUpperWeightExceptions_card_le_of_spread
      H delta etaPresent hspread)).trans hbudget

/-- A lower-bad triple is either a missing lower-bad triple, or a present
edge that violates the corresponding present-edge lower bound. -/
lemma globalLowerBad_subset_nonedges_union_presentExceptions
    {n : ℕ} (H : Finset (Edge n)) (L delta : ℝ)
    (hL : L ≤ 1 - delta) :
    (allEdges n).filter (fun Z ↦
        ¬ CompletionWeightLowerBound H L Z) ⊆
      predicateLowerBadNonedges H L ∪
        presentLowerWeightExceptions H delta := by
  intro Z hZ
  rcases Finset.mem_filter.mp hZ with ⟨hZall, hbad⟩
  by_cases hZH : Z ∈ H
  · apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    refine ⟨hZH, ?_⟩
    unfold CompletionWeightLowerBound at hbad
    have htarget : 0 ≤ matchingWeightTarget n H := by
      unfold matchingWeightTarget
      positivity
    exact (lt_of_not_ge hbad).trans_le
      (mul_le_mul_of_nonneg_right hL htarget)
  · apply Finset.mem_union_left
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_sdiff.mpr ⟨hZall, hZH⟩, hbad⟩

/-- The cardinal form of the lower splitting lemma. -/
lemma globalLowerBad_card_le_nonedge_add_presentExceptions
    {n : ℕ} (H : Finset (Edge n)) (L delta : ℝ)
    (hL : L ≤ 1 - delta) :
    ((allEdges n).filter (fun Z ↦
        ¬ CompletionWeightLowerBound H L Z)).card ≤
      (predicateLowerBadNonedges H L).card +
        (presentLowerWeightExceptions H delta).card := by
  exact (Finset.card_le_card
    (globalLowerBad_subset_nonedges_union_presentExceptions H L delta hL)).trans
      (Finset.card_union_le _ _)

/-- A failed global lower-spread conclusion, after charging the present
lower exceptions, leaves more than `2*d` lower-bad nonedges. -/
lemma predicateLowerBadNonedges_card_gt_two_mul_of_not_global
    {n d : ℕ} {H : Finset (Edge n)} {L delta eta : ℝ}
    (hL : L ≤ 1 - delta)
    (hbudget : ((2 * d : ℕ) : ℝ) +
        (presentLowerWeightExceptions H delta).card ≤
      eta * (allEdges n).card)
    (hfail : ¬ GlobalLowerWeightSpread n H L eta) :
    2 * d < (predicateLowerBadNonedges H L).card := by
  have hbad : eta * (allEdges n).card <
      (((allEdges n).filter fun Z ↦
        ¬ CompletionWeightLowerBound H L Z).card : ℝ) := by
    unfold GlobalLowerWeightSpread at hfail
    exact lt_of_not_ge hfail
  have hcard := globalLowerBad_card_le_nonedge_add_presentExceptions
    H L delta hL
  have hcardR :
      (((allEdges n).filter fun Z ↦
          ¬ CompletionWeightLowerBound H L Z).card : ℝ) ≤
        (predicateLowerBadNonedges H L).card +
          (presentLowerWeightExceptions H delta).card := by
    exact_mod_cast hcard
  have hdR : ((2 * d : ℕ) : ℝ) <
      (predicateLowerBadNonedges H L).card := by
    linarith
  exact_mod_cast hdR

/-- Present-edge spreading supplies the present-exception charge in the
lower split. -/
lemma predicateLowerBadNonedges_card_gt_two_mul_of_not_global_of_spread
    {n d : ℕ} {H : Finset (Edge n)}
    {L delta etaPresent etaGlobal : ℝ}
    (hL : L ≤ 1 - delta)
    (hspread : PresentWeightSpread H delta etaPresent)
    (hbudget : ((2 * d : ℕ) : ℝ) + etaPresent * H.card ≤
      etaGlobal * (allEdges n).card)
    (hfail : ¬ GlobalLowerWeightSpread n H L etaGlobal) :
    2 * d < (predicateLowerBadNonedges H L).card := by
  apply predicateLowerBadNonedges_card_gt_two_mul_of_not_global
    hL _ hfail
  exact (add_le_add le_rfl
    (presentLowerWeightExceptions_card_le_of_spread
      H delta etaPresent hspread)).trans hbudget

end

end Erdos747
