import ErdosProblems.Erdos747.ThinningTop

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Deterministic and hypergeometric consequences used by thinning -/

lemma completionWeight_mono {n : ℕ} {H G : Finset (Edge n)}
    (hHG : H ⊆ G) (Z : Edge n) :
    completionWeight H Z ≤ completionWeight G Z := by
  unfold completionWeight matchingWeight
  apply Finset.card_le_card
  intro F hF
  rcases Finset.mem_filter.mp hF with ⟨hFpm, hZF⟩
  apply Finset.mem_filter.mpr
  refine ⟨?_, hZF⟩
  rcases mem_perfectMatchings.mp hFpm with ⟨hFsub, hcard, hmatch⟩
  apply mem_perfectMatchings.mpr
  refine ⟨?_, hcard, hmatch⟩
  intro A hAF
  rcases Finset.mem_insert.mp (hFsub hAF) with hAZ | hAH
  · simpa [hAZ] using Finset.mem_insert_self A G
  · exact Finset.mem_insert_of_mem (hHG hAH)

def presentUpperWeightExceptions {n : ℕ} (H : Finset (Edge n))
    (delta : ℝ) : Finset (Edge n) :=
  H.filter fun Z ↦
    (1 + delta) * matchingWeightTarget n H <
      (completionWeight H Z : ℝ)

def presentLowerWeightExceptions {n : ℕ} (H : Finset (Edge n))
    (delta : ℝ) : Finset (Edge n) :=
  H.filter fun Z ↦
    (completionWeight H Z : ℝ) <
      (1 - delta) * matchingWeightTarget n H

lemma presentUpperWeightExceptions_card_le_of_spread
    {n : ℕ} (H : Finset (Edge n)) (delta eta : ℝ)
    (hspread : PresentWeightSpread H delta eta) :
    ((presentUpperWeightExceptions H delta).card : ℝ) ≤
      eta * H.card := by
  have hsub : presentUpperWeightExceptions H delta ⊆
      H.filter fun Z ↦ ¬ CompletionWeightClose H delta Z := by
    intro Z hZ
    rcases Finset.mem_filter.mp hZ with ⟨hZH, hhigh⟩
    apply Finset.mem_filter.mpr
    refine ⟨hZH, ?_⟩
    intro hclose
    unfold CompletionWeightClose at hclose
    have habs := le_abs_self
      ((completionWeight H Z : ℝ) - matchingWeightTarget n H)
    linarith
  have hcard := Finset.card_le_card hsub
  exact (by exact_mod_cast hcard :
    ((presentUpperWeightExceptions H delta).card : ℝ) ≤
      ((H.filter fun Z ↦ ¬ CompletionWeightClose H delta Z).card : ℝ)) |>.trans
        hspread

lemma presentLowerWeightExceptions_card_le_of_spread
    {n : ℕ} (H : Finset (Edge n)) (delta eta : ℝ)
    (hspread : PresentWeightSpread H delta eta) :
    ((presentLowerWeightExceptions H delta).card : ℝ) ≤
      eta * H.card := by
  have hsub : presentLowerWeightExceptions H delta ⊆
      H.filter fun Z ↦ ¬ CompletionWeightClose H delta Z := by
    intro Z hZ
    rcases Finset.mem_filter.mp hZ with ⟨hZH, hlow⟩
    apply Finset.mem_filter.mpr
    refine ⟨hZH, ?_⟩
    intro hclose
    unfold CompletionWeightClose at hclose
    have habs := neg_le_abs
      ((completionWeight H Z : ℝ) - matchingWeightTarget n H)
    linarith
  have hcard := Finset.card_le_card hsub
  exact (by exact_mod_cast hcard :
    ((presentLowerWeightExceptions H delta).card : ℝ) ≤
      ((H.filter fun Z ↦ ¬ CompletionWeightClose H delta Z).card : ℝ)) |>.trans
        hspread

lemma powersetCard_exception_probability_le
    {n t e : ℕ} (H E : Finset (Edge n))
    (hEH : E ⊆ H) (htH : t ≤ H.card) (hH : H.Nonempty)
    (hcollision : 2 * t * t ≤ H.card)
    (hthreshold : (5 / 4 : ℝ) * (t : ℝ) *
      ((E.card : ℝ) / H.card) ≤ (e + 1 : ℕ)) :
    finsetProbability (H.powersetCard t)
        (fun T ↦ e + 1 ≤ (T.filter fun Z ↦ Z ∈ E).card) ≤
      2 * Real.exp
        (-((t : ℝ) * ((E.card : ℝ) / H.card)) / 64) := by
  calc
    finsetProbability (H.powersetCard t)
        (fun T ↦ e + 1 ≤ (T.filter fun Z ↦ Z ∈ E).card) ≤
      finsetProbability (H.powersetCard t)
        (fun T ↦ (5 / 4 : ℝ) * (t : ℝ) *
            ((E.card : ℝ) / H.card) ≤
          ((T.filter fun Z ↦ Z ∈ E).card : ℝ)) := by
        apply finsetProbability_mono_event
        intro T hT hlarge
        have hlargeR : ((e + 1 : ℕ) : ℝ) ≤
            ((T.filter fun Z ↦ Z ∈ E).card : ℝ) := by
          exact_mod_cast hlarge
        exact hthreshold.trans hlargeR
    _ ≤ _ := powersetCard_hitCount_five_quarters_le_mean
      H E hEH htH hH hcollision

lemma presentUpperWeightException_probability_le
    {n t e : ℕ} (H : Finset (Edge n)) (delta : ℝ)
    (htH : t ≤ H.card) (hH : H.Nonempty)
    (hcollision : 2 * t * t ≤ H.card)
    (hthreshold : (5 / 4 : ℝ) * (t : ℝ) *
      (((presentUpperWeightExceptions H delta).card : ℝ) / H.card) ≤
        (e + 1 : ℕ)) :
    finsetProbability (H.powersetCard t)
        (fun T ↦ e + 1 ≤
          (T.filter fun Z ↦
            (1 + delta) * matchingWeightTarget n H <
              (completionWeight (H \ T) Z : ℝ)).card) ≤
      2 * Real.exp
        (-((t : ℝ) *
          (((presentUpperWeightExceptions H delta).card : ℝ) / H.card)) /
            64) := by
  let E := presentUpperWeightExceptions H delta
  have hEH : E ⊆ H := Finset.filter_subset _ _
  have htail := powersetCard_exception_probability_le
    H E hEH htH hH hcollision (by simpa only [E] using hthreshold)
  apply le_trans (finsetProbability_mono_event
    (s := H.powersetCard t)
    (P := fun T ↦ e + 1 ≤
      (T.filter fun Z ↦
        (1 + delta) * matchingWeightTarget n H <
          (completionWeight (H \ T) Z : ℝ)).card)
    (Q := fun T ↦ e + 1 ≤ (T.filter fun Z ↦ Z ∈ E).card) ?_) htail
  intro T hT hlarge
  apply Nat.le_trans hlarge
  apply Finset.card_le_card
  intro Z hZ
  rcases Finset.mem_filter.mp hZ with ⟨hZT, hhigh⟩
  apply Finset.mem_filter.mpr
  refine ⟨hZT, ?_⟩
  unfold E presentUpperWeightExceptions
  apply Finset.mem_filter.mpr
  refine ⟨(Finset.mem_powersetCard.mp hT).1 hZT, ?_⟩
  exact hhigh.trans_le (by
    exact_mod_cast completionWeight_mono (Finset.sdiff_subset : H \ T ⊆ H) Z)

/-- A relative lower-survival estimate for an upper-bad nonedge implies the
absolute survival estimate used by the top weight-block diagnostic. -/
lemma upperBad_absolute_failure_probability_le_of_relative
    {n t : ℕ} (H : Finset (Edge n)) {Z : Edge n}
    (L a r p : ℝ)
    (hZ : Z ∈ coarseUpperBadNonedges n H L)
    (hr : 0 < r) (ha : a ≤ r * (L * matchingWeightTarget n H))
    (hrelative :
      finsetProbability (H.powersetCard t)
          (fun T ↦ (completionWeight (H \ T) Z : ℝ) <
            r * (completionWeight H Z : ℝ)) ≤ p) :
    finsetProbability (H.powersetCard t)
        (fun T ↦ ¬ a < (completionWeight (H \ T) Z : ℝ)) ≤ p := by
  apply (finsetProbability_mono_event
    (s := H.powersetCard t)
    (P := fun T ↦ ¬ a < (completionWeight (H \ T) Z : ℝ))
    (Q := fun T ↦ (completionWeight (H \ T) Z : ℝ) <
      r * (completionWeight H Z : ℝ)) ?_).trans hrelative
  intro T hT hfail
  have hbad : L * matchingWeightTarget n H <
      (completionWeight H Z : ℝ) := by
    rcases Finset.mem_filter.mp hZ with ⟨hZdiff, hnot⟩
    unfold CompletionWeightUpperBound at hnot
    exact lt_of_not_ge hnot
  have hscale : r * (L * matchingWeightTarget n H) <
      r * (completionWeight H Z : ℝ) :=
    mul_lt_mul_of_pos_left hbad hr
  exact (le_of_not_gt hfail).trans_lt (ha.trans_lt hscale)

lemma coarseUpperBadNonedges_card_gt_of_not_global
    {n d : ℕ} {H : Finset (Edge n)} {L eta : ℝ}
    (hbudget : ((d + H.card : ℕ) : ℝ) ≤ eta * (allEdges n).card)
    (hfail : ¬ GlobalUpperWeightSpread n H L eta) :
    d < (coarseUpperBadNonedges n H L).card := by
  have hbad : eta * (allEdges n).card <
      (((allEdges n).filter fun Z ↦
        ¬ CompletionWeightUpperBound H L Z).card : ℝ) := by
    unfold GlobalUpperWeightSpread at hfail
    exact lt_of_not_ge hfail
  have hcard := globalUpperBad_card_le_nonedge_add_card H L
  have hcardR :
      (((allEdges n).filter fun Z ↦
          ¬ CompletionWeightUpperBound H L Z).card : ℝ) ≤
        (coarseUpperBadNonedges n H L).card + H.card := by
    exact_mod_cast hcard
  have hdR : (d : ℝ) < (coarseUpperBadNonedges n H L).card := by
    norm_num only [Nat.cast_add] at hbudget
    linarith
  exact_mod_cast hdR

lemma predicateLowerBadNonedges_card_gt_of_not_global
    {n d : ℕ} {H : Finset (Edge n)} {L eta : ℝ}
    (hbudget : ((d + H.card : ℕ) : ℝ) ≤ eta * (allEdges n).card)
    (hfail : ¬ GlobalLowerWeightSpread n H L eta) :
    d < (predicateLowerBadNonedges H L).card := by
  have hbad : eta * (allEdges n).card <
      (((allEdges n).filter fun Z ↦
        ¬ CompletionWeightLowerBound H L Z).card : ℝ) := by
    unfold GlobalLowerWeightSpread at hfail
    exact lt_of_not_ge hfail
  have hcard := globalLowerBad_card_le_nonedge_add_card H L
  have hcardR :
      (((allEdges n).filter fun Z ↦
          ¬ CompletionWeightLowerBound H L Z).card : ℝ) ≤
        (predicateLowerBadNonedges H L).card + H.card := by
    exact_mod_cast hcard
  have hdR : (d : ℝ) < (predicateLowerBadNonedges H L).card := by
    norm_num only [Nat.cast_add] at hbudget
    linarith
  exact_mod_cast hdR

end

end Erdos747
