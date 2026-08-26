import ErdosProblems.Erdos747.CompletionSurvivalFull

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Reindexing completion-edge influences to residual matching weights -/

lemma completionEdgeWeight_eq_matchingWeight_reindexAway
    {n : ℕ} (H : Finset (Edge n)) {Z A : Edge n}
    (hZ : Z ∈ allEdges n) (hAZ : Disjoint A Z) :
    completionEdgeWeight H Z A =
      matchingWeight (reindexGraphAway H Z hZ)
        (reindexEdgeAway Z hZ A) := by
  unfold completionEdgeWeight matchingWeight
  apply Finset.card_bij
    (s := (completionMatchings n H Z).filter fun F ↦ A ∈ F)
    (t := (perfectMatchings (n - 1) (reindexGraphAway H Z hZ)).filter
      fun K ↦ reindexEdgeAway Z hZ A ∈ K)
    (fun F _ ↦ reindexFamilyAway Z hZ F) 
  · intro F hF
    rcases Finset.mem_filter.mp hF with ⟨hFC, hAF⟩
    apply Finset.mem_filter.mpr
    refine ⟨(completionPerfectMatchingEquiv H Z hZ ⟨F, hFC⟩).2, ?_⟩
    exact (reindexEdgeAway_mem_reindexFamilyAway hZ hAZ).mpr hAF
  · intro F hF G hG hEq
    have hFaway := (mem_completionMatchings.mp
      (Finset.mem_filter.mp hF).1).2.2.2
    have hGaway := (mem_completionMatchings.mp
      (Finset.mem_filter.mp hG).1).2.2.2
    simpa only [unreindex_reindexFamilyAway hZ hFaway,
      unreindex_reindexFamilyAway hZ hGaway] using
        congrArg (unreindexFamilyAway Z hZ) hEq
  · intro K hK
    rcases Finset.mem_filter.mp hK with ⟨hKP, hAK⟩
    let F := unreindexFamilyAway Z hZ K
    have hFC : F ∈ completionMatchings n H Z :=
      (completionPerfectMatchingEquiv H Z hZ).symm ⟨K, hKP⟩ |>.2
    have hAF : A ∈ F := by
      apply (mem_unreindexFamilyAway hZ A).mpr
      exact ⟨reindexEdgeAway Z hZ A, hAK,
        unreindex_reindexEdgeAway hZ hAZ⟩
    refine ⟨F, Finset.mem_filter.mpr ⟨hFC, hAF⟩, ?_⟩
    exact reindex_unreindexFamilyAway hZ K

lemma completionEdgeWeight_eq_zero_of_not_disjoint
    {n : ℕ} (H : Finset (Edge n)) (Z A : Edge n)
    (hAZ : ¬ Disjoint A Z) :
    completionEdgeWeight H Z A = 0 := by
  unfold completionEdgeWeight
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro F hF
  rcases Finset.mem_filter.mp hF with ⟨hFC, hAF⟩
  exact hAZ ((mem_completionMatchings.mp hFC).2.2.2 A hAF)

lemma completionEdgeWeight_le_completionMatchings_card
    {n : ℕ} (H : Finset (Edge n)) (Z A : Edge n) :
    completionEdgeWeight H Z A ≤ (completionMatchings n H Z).card := by
  unfold completionEdgeWeight
  exact Finset.card_le_card (Finset.filter_subset _ _)

lemma completionHeavyEdges_disjoint {n : ℕ}
    (H : Finset (Edge n)) (Z : Edge n) (b : ℝ) (hb : 0 ≤ b) :
    ∀ A ∈ completionHeavyEdges H Z b, Disjoint A Z := by
  intro A hA
  rcases mem_completionHeavyEdges.mp hA with ⟨hAH, hheavy⟩
  by_contra hdisj
  rw [completionEdgeWeight_eq_zero_of_not_disjoint H Z A hdisj] at hheavy
  norm_num at hheavy
  exact (not_lt_of_ge hb) hheavy

lemma completionHeavyEdges_card_le_residual_presentBad
    {n : ℕ} (H : Finset (Edge n)) {Z : Edge n}
    (hZ : Z ∈ allEdges n) (delta : ℝ) (hdelta : 0 ≤ delta) :
    (completionHeavyEdges H Z
        ((1 + delta) * matchingWeightTarget (n - 1)
          (reindexGraphAway H Z hZ))).card ≤
      ((reindexGraphAway H Z hZ).filter fun W ↦
        ¬ CompletionWeightClose (reindexGraphAway H Z hZ) delta W).card := by
  let J := reindexGraphAway H Z hZ
  let b := (1 + delta) * matchingWeightTarget (n - 1) J
  let f : Edge n → Edge (n - 1) := reindexEdgeAway Z hZ
  have hb0 : 0 ≤ b := by
    dsimp only [b]
    apply mul_nonneg
    · linarith
    · unfold matchingWeightTarget
      positivity
  apply Finset.card_le_card_of_injOn f
  · intro A hA
    have hAZ := completionHeavyEdges_disjoint H Z b hb0 A hA
    have hAH := (mem_completionHeavyEdges.mp hA).1
    have hWJ : f A ∈ J := by
      rw [mem_reindexGraphAway]
      simpa only [f, unreindex_reindexEdgeAway hZ hAZ] using hAH
    apply Finset.mem_filter.mpr
    refine ⟨hWJ, ?_⟩
    intro hclose
    have hupper :
        (completionWeight J (f A) : ℝ) ≤
          (1 + delta) * matchingWeightTarget (n - 1) J := by
      have habs := le_abs_self
        ((completionWeight J (f A) : ℝ) -
          matchingWeightTarget (n - 1) J)
      unfold CompletionWeightClose at hclose
      linarith
    have hweight : completionWeight J (f A) =
        completionEdgeWeight H Z A := by
      rw [completionWeight_eq_matchingWeight_of_mem J hWJ]
      exact (completionEdgeWeight_eq_matchingWeight_reindexAway
        H hZ hAZ).symm
    have hheavy := (mem_completionHeavyEdges.mp hA).2
    rw [hweight] at hupper
    exact (not_lt_of_ge hupper) hheavy
  · intro A hA B hB hEq
    have hAZ := completionHeavyEdges_disjoint H Z b hb0 A hA
    have hBZ := completionHeavyEdges_disjoint H Z b hb0 B hB
    have h := congrArg (unreindexEdgeAway Z hZ) hEq
    simpa only [f, unreindex_reindexEdgeAway hZ hAZ,
      unreindex_reindexEdgeAway hZ hBZ] using h

lemma completionHeavyEdges_card_le_of_residual_presentSpread
    {n : ℕ} (H : Finset (Edge n)) {Z : Edge n}
    (hZ : Z ∈ allEdges n) (delta eta : ℝ) (hdelta : 0 ≤ delta)
    (hspread : PresentWeightSpread (reindexGraphAway H Z hZ) delta eta) :
    ((completionHeavyEdges H Z
        ((1 + delta) * matchingWeightTarget (n - 1)
          (reindexGraphAway H Z hZ))).card : ℝ) ≤
      eta * (reindexGraphAway H Z hZ).card := by
  have hcard := completionHeavyEdges_card_le_residual_presentBad
    H hZ delta hdelta
  have hcardR :
      ((completionHeavyEdges H Z
          ((1 + delta) * matchingWeightTarget (n - 1)
            (reindexGraphAway H Z hZ))).card : ℝ) ≤
        (((reindexGraphAway H Z hZ).filter fun W ↦
          ¬ CompletionWeightClose (reindexGraphAway H Z hZ) delta W).card : ℝ) := by
    exact_mod_cast hcard
  exact hcardR.trans hspread

lemma sum_completionHeavyEdges_le_card_mul_completionWeight
    {n : ℕ} (H : Finset (Edge n)) (Z : Edge n) (b : ℝ) :
    ∑ A ∈ completionHeavyEdges H Z b,
        (completionEdgeWeight H Z A : ℝ) ≤
      ((completionHeavyEdges H Z b).card : ℝ) *
        (completionMatchings n H Z).card := by
  calc
    ∑ A ∈ completionHeavyEdges H Z b,
        (completionEdgeWeight H Z A : ℝ) ≤
      ∑ _A ∈ completionHeavyEdges H Z b,
        ((completionMatchings n H Z).card : ℝ) := by
      apply Finset.sum_le_sum
      intro A hA
      exact_mod_cast completionEdgeWeight_le_completionMatchings_card H Z A
    _ = ((completionHeavyEdges H Z b).card : ℝ) *
        (completionMatchings n H Z).card := by simp

end

end Erdos747
