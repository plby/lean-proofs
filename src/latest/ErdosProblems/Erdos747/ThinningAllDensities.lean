import ErdosProblems.Erdos747.AggregateThinningTop

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

lemma finsetProbability_eq_zero_of_forall_not {α : Type*} (s : Finset α) (P : α → Prop)
    [DecidablePred P] (h : ∀ x ∈ s, ¬ P x) : finsetProbability s P = 0 := by
  have he : s.filter P = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact h x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2
  simp only [finsetProbability, he, Finset.card_empty, Nat.cast_zero, zero_div]

lemma thinning_bottom_parameters (K M t d : ℕ)
    (htM : t ≤ M) (hMK : M ≤ K) (ht : 0 < t) (htsq : t * t ≤ d) (hgap : 2 * d < K - M) :
    d ≤ K - (M - t) ∧ t ≤ K - (M - t) ∧ 0 < K - (M - t) ∧
      2 * t * t ≤ K - (M - t) := by
  have hsub : K - M ≤ K - (M - t) := by omega
  have htwosq : 2 * t * t ≤ 2 * d := by nlinarith only [htsq]
  exact ⟨by omega, by omega, by omega, htwosq.trans (by omega)⟩

lemma thinning_bottom_tail_le_exp (K S t : ℕ) (zeta : ℝ)
    (hzeta : 0 ≤ zeta) (hlarge : 16 ≤ zeta * K) (hS : 0 < S) (hSK : S ≤ K) :
    4 * Real.exp (-((t : ℝ) * ((thinningBlockSize K zeta : ℝ) / S)) / 64) ≤
      4 * Real.exp (-((t : ℝ) * zeta) / 1024) := by
  have hSR : (0 : ℝ) < S := by exact_mod_cast hS
  have hd := (thinningBlockSize_bounds K zeta hzeta hlarge).1
  have hSKR : (S : ℝ) ≤ K := by exact_mod_cast hSK
  have hratio : zeta / 16 ≤ (thinningBlockSize K zeta : ℝ) / S := by
    apply (le_div_iff₀ hSR).mpr
    have h := mul_le_mul_of_nonneg_left hSKR hzeta
    linarith only [h, hd]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg t)
  nlinarith only [h]

lemma conditionalGlobalUpper_failure_probability_le_all_densities
    {n M t : ℕ} (Good : Finset (Edge n) → Prop) (alpha zeta T E : ℝ)
    (halpha0 : 0 ≤ alpha) (halphaHalf : alpha ≤ 1 / 2) (hzeta : 0 < zeta)
    (halphaZeta : alpha ≤ zeta / 2) (hT : 0 ≤ T)
    (hlarge : 16 ≤ zeta * (allEdges n).card)
    (htM : t ≤ M) (hMtop : M ≤ (allEdges n).card) (ht : 0 < t)
    (htsq : t * t ≤ thinningBlockSize (allEdges n).card zeta)
    (hE0 : 0 ≤ E) (hEhalf : E ≤ 1 / 2)
    (hspread : ∀ H ∈ sample n M, Good H → PresentWeightSpread H alpha alpha)
    (htop : ∀ H ∈ sample n M, Good H → ¬ GlobalUpperWeightSpread n H (coarseUpperFactor T) zeta →
      finsetProbability (H.powersetCard t)
          (fun U ↦ ¬ UpperWeightBlockDiagnostic n (thinningBlockSize (allEdges n).card zeta) t ⟨H, U⟩) ≤ E) :
    finsetProbability (sample n M)
        (fun H ↦ Good H ∧ ¬ GlobalUpperWeightSpread n H (coarseUpperFactor T) zeta) ≤
      4 * Real.exp (-((t : ℝ) * zeta) / 1024) := by
  let d := thinningBlockSize (allEdges n).card zeta
  by_cases hgap : 2 * d < (allEdges n).card - M
  · obtain ⟨hd, htB, hpos, hcollision⟩ := thinning_bottom_parameters (allEdges n).card M t d
      htM hMtop ht htsq hgap
    have hraw := conditionalGlobalUpper_failure_probability_le_of_thinning_sharp
      (d := d) Good htM hMtop hE0 hEhalf hd htB hpos hcollision htop
    exact hraw.trans (thinning_bottom_tail_le_exp (allEdges n).card
      ((allEdges n).card - (M - t)) t zeta hzeta.le hlarge hpos (Nat.sub_le _ _))
  · have hz : finsetProbability (sample n M)
        (fun H ↦ Good H ∧ ¬ GlobalUpperWeightSpread n H (coarseUpperFactor T) zeta) = 0 := by
      apply finsetProbability_eq_zero_of_forall_not
      intro H hHs hbad
      have hpres := hspread H hHs hbad.1
      have hfactor := coarseUpperFactor_ge_two T hT
      have hbudget := thinning_global_budget (allEdges n).card H.card zeta alpha hzeta.le hlarge
        (Finset.card_le_card (mem_sample.mp hHs).1) halpha0 halphaZeta
      have hbig := coarseUpperBadNonedges_card_gt_two_mul_of_not_global_of_spread
        (d := d) (show 1 + alpha ≤ coarseUpperFactor T by linarith only [hfactor, halphaHalf])
        hpres hbudget hbad.2
      have hsmall : (coarseUpperBadNonedges n H (coarseUpperFactor T)).card ≤ (allEdges n).card - M := by
        have h := Finset.card_le_card (Finset.filter_subset
          (fun Z ↦ ¬ CompletionWeightUpperBound H (coarseUpperFactor T) Z) (allEdges n \ H))
        rw [Finset.card_sdiff_of_subset (mem_sample.mp hHs).1, (mem_sample.mp hHs).2] at h
        exact h
      omega
    rw [hz]
    positivity

lemma conditionalGlobalLower_failure_probability_le_all_densities
    {n M t : ℕ} (Good : Finset (Edge n) → Prop) (alpha zeta T E : ℝ)
    (halpha0 : 0 ≤ alpha) (halphaHalf : alpha ≤ 1 / 2) (hzeta : 0 < zeta)
    (halphaZeta : alpha ≤ zeta / 2) (hT : 0 ≤ T)
    (hlarge : 16 ≤ zeta * (allEdges n).card)
    (htM : t ≤ M) (hMtop : M ≤ (allEdges n).card) (ht : 0 < t)
    (htsq : t * t ≤ thinningBlockSize (allEdges n).card zeta)
    (hE0 : 0 ≤ E) (hEhalf : E ≤ 1 / 2)
    (hspread : ∀ H ∈ sample n M, Good H → PresentWeightSpread H alpha alpha)
    (htop : ∀ H ∈ sample n M, Good H → ¬ GlobalLowerWeightSpread n H (coarseLowerFactor T) zeta →
      finsetProbability (H.powersetCard t)
          (fun U ↦ ¬ LowerWeightBlockDiagnostic n (thinningBlockSize (allEdges n).card zeta) t ⟨H, U⟩) ≤ E) :
    finsetProbability (sample n M)
        (fun H ↦ Good H ∧ ¬ GlobalLowerWeightSpread n H (coarseLowerFactor T) zeta) ≤
      4 * Real.exp (-((t : ℝ) * zeta) / 1024) := by
  let d := thinningBlockSize (allEdges n).card zeta
  by_cases hgap : 2 * d < (allEdges n).card - M
  · obtain ⟨hd, htB, hpos, hcollision⟩ := thinning_bottom_parameters (allEdges n).card M t d
      htM hMtop ht htsq hgap
    have hraw := conditionalGlobalLower_failure_probability_le_of_thinning_sharp
      (d := d) Good htM hMtop hE0 hEhalf hd htB hpos hcollision htop
    exact hraw.trans (thinning_bottom_tail_le_exp (allEdges n).card
      ((allEdges n).card - (M - t)) t zeta hzeta.le hlarge hpos (Nat.sub_le _ _))
  · have hz : finsetProbability (sample n M)
        (fun H ↦ Good H ∧ ¬ GlobalLowerWeightSpread n H (coarseLowerFactor T) zeta) = 0 := by
      apply finsetProbability_eq_zero_of_forall_not
      intro H hHs hbad
      have hpres := hspread H hHs hbad.1
      have hr1 := coarseSurvivalFraction_le_one T hT
      have hfactor : coarseLowerFactor T ≤ 1 - alpha := by
        unfold coarseLowerFactor
        linarith only [hr1, halphaHalf]
      have hbudget := thinning_global_budget (allEdges n).card H.card zeta alpha hzeta.le hlarge
        (Finset.card_le_card (mem_sample.mp hHs).1) halpha0 halphaZeta
      have hbig := predicateLowerBadNonedges_card_gt_two_mul_of_not_global_of_spread
        (d := d) hfactor hpres hbudget hbad.2
      have hsmall : (predicateLowerBadNonedges H (coarseLowerFactor T)).card ≤ (allEdges n).card - M := by
        have h := Finset.card_le_card (Finset.filter_subset
          (fun Z ↦ ¬ CompletionWeightLowerBound H (coarseLowerFactor T) Z) (allEdges n \ H))
        rw [Finset.card_sdiff_of_subset (mem_sample.mp hHs).1, (mem_sample.mp hHs).2] at h
        exact h
      omega
    rw [hz]
    positivity

end

end Erdos747
