import ErdosProblems.Erdos747.HeavyWeightMass
import ErdosProblems.Erdos747.ResidualWeights

open scoped BigOperators

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Adjustable heavy cutoffs in a residual graph -/

lemma completionEdgeWeight_eq_completionWeight_reindexAway
    {n : ℕ} (H : Finset (Edge n)) {Z A : Edge n}
    (hZ : Z ∈ allEdges n) (hA : A ∈ H) (hAZ : Disjoint A Z) :
    completionEdgeWeight H Z A =
      completionWeight (reindexGraphAway H Z hZ) (reindexEdgeAway Z hZ A) := by
  rw [completionWeight_eq_matchingWeight_of_mem
    (reindexGraphAway H Z hZ)
    ((reindexEdgeAway_mem_reindexGraphAway hZ hAZ).mpr hA)]
  exact completionEdgeWeight_eq_matchingWeight_reindexAway H hZ hAZ

lemma reindexEdgeAway_injectiveOn_completionHeavyEdges
    {n : ℕ} (H : Finset (Edge n)) {Z : Edge n}
    (hZ : Z ∈ allEdges n) (b : ℝ) (hb : 0 ≤ b) :
    Set.InjOn (reindexEdgeAway Z hZ) (completionHeavyEdges H Z b) := by
  intro A hA B hB hEq
  have hAZ := completionHeavyEdges_disjoint H Z b hb A hA
  have hBZ := completionHeavyEdges_disjoint H Z b hb B hB
  have h := congrArg (unreindexEdgeAway Z hZ) hEq
  simpa only [unreindex_reindexEdgeAway hZ hAZ,
    unreindex_reindexEdgeAway hZ hBZ] using h

lemma completionHeavyEdges_image_reindex
    {n : ℕ} (H : Finset (Edge n)) {Z : Edge n}
    (hZ : Z ∈ allEdges n) (b : ℝ) (hb : 0 ≤ b) :
    (completionHeavyEdges H Z b).image (reindexEdgeAway Z hZ) =
      (reindexGraphAway H Z hZ).filter
        (fun A ↦ b < (completionWeight (reindexGraphAway H Z hZ) A : ℝ)) := by
  ext W
  constructor
  · intro hW
    rcases Finset.mem_image.mp hW with ⟨A, hA, rfl⟩
    have hAZ := completionHeavyEdges_disjoint H Z b hb A hA
    have hAH := (mem_completionHeavyEdges.mp hA).1
    apply Finset.mem_filter.mpr
    refine ⟨(reindexEdgeAway_mem_reindexGraphAway hZ hAZ).mpr hAH, ?_⟩
    rw [← completionEdgeWeight_eq_completionWeight_reindexAway H hZ hAH hAZ]
    exact (mem_completionHeavyEdges.mp hA).2
  · intro hW
    rcases Finset.mem_filter.mp hW with ⟨hWJ, hWheavy⟩
    let A := unreindexEdgeAway Z hZ W
    have hAH : A ∈ H := (mem_reindexGraphAway hZ W).mp hWJ
    have hAZ : Disjoint A Z := unreindexEdgeAway_disjoint hZ W
    have hindex : reindexEdgeAway Z hZ A = W := reindex_unreindexEdgeAway hZ W
    have hweight : completionEdgeWeight H Z A =
        completionWeight (reindexGraphAway H Z hZ) W := by
      rw [completionEdgeWeight_eq_completionWeight_reindexAway H hZ hAH hAZ,
        hindex]
    apply Finset.mem_image.mpr
    refine ⟨A, mem_completionHeavyEdges.mpr ⟨hAH, ?_⟩, hindex⟩
    simpa only [hweight] using hWheavy

lemma sum_completionHeavyEdges_reindex
    {n : ℕ} (H : Finset (Edge n)) {Z : Edge n}
    (hZ : Z ∈ allEdges n) (b : ℝ) (hb : 0 ≤ b) :
    ∑ A ∈ completionHeavyEdges H Z b, (completionEdgeWeight H Z A : ℝ) =
      ∑ A ∈ (reindexGraphAway H Z hZ).filter
          (fun A ↦ b < (completionWeight (reindexGraphAway H Z hZ) A : ℝ)),
        (completionWeight (reindexGraphAway H Z hZ) A : ℝ) := by
  rw [← completionHeavyEdges_image_reindex H hZ b hb,
    Finset.sum_image (reindexEdgeAway_injectiveOn_completionHeavyEdges H hZ b hb)]
  apply Finset.sum_congr rfl
  intro A hA
  rw [completionEdgeWeight_eq_completionWeight_reindexAway H hZ
    (mem_completionHeavyEdges.mp hA).1
    (completionHeavyEdges_disjoint H Z b hb A hA)]

lemma completionHeavyEdges_mass_le_of_residual_presentSpread
    {n : ℕ} (H : Finset (Edge n)) {Z : Edge n}
    (hn : 0 < n) (hZ : Z ∈ allEdges n) (delta eta h : ℝ)
    (hdelta : 0 ≤ delta) (hh : 1 + delta ≤ h)
    (hspread : PresentWeightSpread (reindexGraphAway H Z hZ) delta eta) :
    ∑ A ∈ completionHeavyEdges H Z
        (h * matchingWeightTarget (n - 1) (reindexGraphAway H Z hZ)),
        (completionEdgeWeight H Z A : ℝ) ≤
      (delta + eta) * ((n - 1 : ℕ) : ℝ) * (completionWeight H Z : ℝ) := by
  let J := reindexGraphAway H Z hZ
  have hw : 0 ≤ matchingWeightTarget (n - 1) J := by
    unfold matchingWeightTarget
    positivity
  have hh0 : 0 ≤ h := by linarith
  rw [sum_completionHeavyEdges_reindex H hZ
    (h * matchingWeightTarget (n - 1) J) (mul_nonneg hh0 hw)]
  have hmass := finset_heavy_weight_sum_le J
    (fun A ↦ (completionWeight J A : ℝ))
    (matchingWeightTarget (n - 1) J) delta eta h hw hdelta
    (fun A hA ↦ by positivity) (sum_completionWeight_eq_card_mul_target J)
    hspread hh
  calc
    _ ≤ (delta + eta) * J.card * matchingWeightTarget (n - 1) J := hmass
    _ = (delta + eta) * ((n - 1 : ℕ) : ℝ) *
        (completionWeight H Z : ℝ) := by
      rw [mul_assoc, card_mul_matchingWeightTarget_eq]
      dsimp only [J]
      rw [card_perfectMatchings_reindexGraphAway hn H hZ]
      ring

lemma completionHeavyEdges_card_mul_le_of_residual_presentSpread
    {n : ℕ} (H : Finset (Edge n)) {Z : Edge n}
    (hZ : Z ∈ allEdges n) (delta eta h : ℝ)
    (hdelta : 0 ≤ delta) (hh : 1 + delta ≤ h)
    (hw : 0 < matchingWeightTarget (n - 1) (reindexGraphAway H Z hZ))
    (hspread : PresentWeightSpread (reindexGraphAway H Z hZ) delta eta) :
    ((completionHeavyEdges H Z
        (h * matchingWeightTarget (n - 1) (reindexGraphAway H Z hZ))).card : ℝ) * h ≤
      (delta + eta) * (reindexGraphAway H Z hZ).card := by
  let J := reindexGraphAway H Z hZ
  let b := h * matchingWeightTarget (n - 1) J
  have hb : 0 ≤ b := mul_nonneg (by linarith) hw.le
  have hcard : (completionHeavyEdges H Z b).card =
      (J.filter fun A ↦ b < (completionWeight J A : ℝ)).card := by
    rw [← completionHeavyEdges_image_reindex H hZ b hb]
    exact (Finset.card_image_iff.mpr
      (reindexEdgeAway_injectiveOn_completionHeavyEdges H hZ b hb)).symm
  change ((completionHeavyEdges H Z b).card : ℝ) * h ≤ _
  rw [hcard]
  exact finset_heavy_card_mul_le J (fun A ↦ (completionWeight J A : ℝ))
    (matchingWeightTarget (n - 1) J) delta eta h hw hdelta
    (fun A hA ↦ by positivity) (sum_completionWeight_eq_card_mul_target J)
    hspread hh

lemma card_reindexGraphAway_le_card {n : ℕ}
    (H : Finset (Edge n)) {Z : Edge n} (hZ : Z ∈ allEdges n) :
    (reindexGraphAway H Z hZ).card ≤ H.card := by
  rw [card_reindexGraphAway]
  exact Finset.card_le_card (Finset.filter_subset _ _)

lemma completionHeavyEdges_hit_bound_of_residual_presentSpread
    {n : ℕ} (H : Finset (Edge n)) {Z : Edge n}
    (hZ : Z ∈ allEdges n) (t : ℕ) (delta eta h : ℝ)
    (hH : H.Nonempty) (hdelta : 0 ≤ delta) (heta : 0 ≤ eta)
    (hh : 1 + delta ≤ h)
    (hw : 0 < matchingWeightTarget (n - 1) (reindexGraphAway H Z hZ))
    (hspread : PresentWeightSpread (reindexGraphAway H Z hZ) delta eta) :
    (t : ℝ) * ((completionHeavyEdges H Z
        (h * matchingWeightTarget (n - 1) (reindexGraphAway H Z hZ))).card : ℝ) /
        H.card ≤ (t : ℝ) * (delta + eta) / h := by
  let B := completionHeavyEdges H Z
    (h * matchingWeightTarget (n - 1) (reindexGraphAway H Z hZ))
  have hHpos : (0 : ℝ) < H.card := by
    exact_mod_cast Finset.card_pos.mpr hH
  have hhpos : 0 < h := by linarith
  have hcard := completionHeavyEdges_card_mul_le_of_residual_presentSpread
    H hZ delta eta h hdelta hh hw hspread
  have hJcard : ((reindexGraphAway H Z hZ).card : ℝ) ≤ H.card := by
    exact_mod_cast card_reindexGraphAway_le_card H hZ
  have hbound : (B.card : ℝ) * h ≤ (delta + eta) * H.card :=
    hcard.trans (mul_le_mul_of_nonneg_left hJcard (by positivity))
  have hratio : (B.card : ℝ) / H.card ≤ (delta + eta) / h :=
    (div_le_div_iff₀ hHpos hhpos).mpr hbound
  change (t : ℝ) * B.card / H.card ≤ _
  calc
    (t : ℝ) * B.card / H.card = (t : ℝ) * ((B.card : ℝ) / H.card) := by ring
    _ ≤ (t : ℝ) * ((delta + eta) / h) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = (t : ℝ) * (delta + eta) / h := by ring

lemma iidCompletionThinning_mean_bounds_of_adjustableCutoff
    {n t : ℕ} (H : Finset (Edge n)) {Z : Edge n}
    (hn : 2 ≤ n) (hZ : Z ∈ allEdges n) (delta eta h : ℝ)
    (hdelta : 0 ≤ delta) (hh : 1 + delta ≤ h)
    (hspread : PresentWeightSpread (reindexGraphAway H Z hZ) delta eta)
    (hs : (H \ completionHeavyEdges H Z
      (h * matchingWeightTarget (n - 1) (reindexGraphAway H Z hZ))).Nonempty)
    (hm : ((n - 1 : ℕ) : ℝ) <
      (H \ completionHeavyEdges H Z
        (h * matchingWeightTarget (n - 1) (reindexGraphAway H Z hZ))).card) :
    let b := h * matchingWeightTarget (n - 1) (reindexGraphAway H Z hZ)
    let s := H \ completionHeavyEdges H Z b
    let w := (completionWeight H Z : ℝ)
    w * (1 - ((n - 1 : ℕ) : ℝ) / s.card)^t ≤
        finsetAverage (Finset.univ : Finset (IidSample s t))
          (iidFamilySurvivalCount (completionMatchings n H Z) t) ∧
      finsetAverage (Finset.univ : Finset (IidSample s t))
          (iidFamilySurvivalCount (completionMatchings n H Z) t) ≤
        w * Real.exp (-((t : ℝ) * ((n - 1 : ℕ) : ℝ) / s.card)) +
          (delta + eta) * w := by
  let b := h * matchingWeightTarget (n - 1) (reindexGraphAway H Z hZ)
  let E := (delta + eta) * ((n - 1 : ℕ) : ℝ) * (completionWeight H Z : ℝ)
  have hheavy : ∑ A ∈ completionHeavyEdges H Z b,
      (completionEdgeWeight H Z A : ℝ) ≤ E :=
    completionHeavyEdges_mass_le_of_residual_presentSpread
      H (by omega) hZ delta eta h hdelta hh hspread
  have hmean := iidCompletionThinning_mean_bounds (t := t) H Z b E hs hn hheavy hm
  have hcount : ((completionMatchings n H Z).card : ℝ) =
      (completionWeight H Z : ℝ) := by
    exact_mod_cast (completionWeight_eq_card_completionMatchings
      H Z (by omega) hZ).symm
  have hk : (((n - 1 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (show n - 1 ≠ 0 by omega)
  have herror : E / ((n - 1 : ℕ) : ℝ) =
      (delta + eta) * (completionWeight H Z : ℝ) := by
    dsimp only [E]
    field_simp
  simpa only [hcount, herror, b] using hmean

end

end Erdos747
