import ErdosProblems.Erdos747.KahnAggregateGood

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

lemma kahnAggregateInsertion_globalLower_failure_probability_le
    {n M codegCap : ℕ}
    {C₀ sigma E delta etaSpread etaGlobal r q etaDeg Bdeg S : ℝ}
    (hn : 3 ≤ n) (hM : 0 < M)
    (hMtop : M < (allEdges n).card)
    (hC0 : 0 ≤ C₀ + 1) (hsigma : 0 < sigma)
    (hratio :
      1 < ((3 * (M + 1) : ℕ) : ℝ) * sigma /
        ((18 * n * (codegCap + 1) : ℕ) : ℝ))
    (hE :
      (3 * n : ℝ) * Real.sqrt sigma +
          (3 * n : ℝ) * (C₀ + 1 + 14 + Real.log 2) /
            Real.log (((3 * (M + 1) : ℕ) : ℝ) * sigma /
              ((18 * n * (codegCap + 1) : ℕ) : ℝ)) ≤ E)
    (hq0 : 0 ≤ q) (hBdeg0 : 0 ≤ Bdeg) (hS0 : 0 ≤ S)
    (hdelta0 : 0 ≤ delta) (hdeltaPos : 0 < delta)
    (hdelta1 : delta ≤ 1) (hetaSpread : 0 ≤ etaSpread)
    (hlocalBudget :
      (3 * n : ℝ) *
          (4 * (3 * (C₀ + 1) * (n : ℝ) + 12 * Real.sqrt n +
            10 * (Real.sqrt (Real.sqrt E * Real.sqrt (3 * n : ℝ)) *
              Real.sqrt (3 * n : ℝ)))) ≤ S ^ 2)
    (hspreadBudget :
      S + (3 * n : ℝ) *
          ((q + 2 * (n : ℝ) / M) +
            (etaDeg + 1 / (n : ℝ)) *
              (1 + (Bdeg + (n : ℝ) / M))) ≤
        3 * etaSpread * delta * (n : ℝ))
    (hr : 0 < r)
    (hglobalBudget : r + (M : ℝ) ≤
      etaGlobal * (allEdges n).card) :
    finsetProbability (sample n M)
        (fun H ↦ KahnAggregateInsertionGood n M codegCap C₀
            q etaDeg Bdeg H ∧
          ¬ GlobalLowerWeightSpread n H
            ((1 - delta) * (M : ℝ) / (M + 1)) etaGlobal) ≤
      etaSpread * (((allEdges n).card - M : ℕ) : ℝ) / r := by
  apply good_globalLower_failure_probability_le
    hM hMtop hdelta0 hdelta1 hetaSpread hr hglobalBudget
  · intro H hGood
    exact kahnAggregateInsertionGood_hasPerfectMatching hGood
  · intro H hHs hGood Z hZ
    exact kahnAggregateInsertionGood_presentWeightSpread
      hn hM hC0 hsigma hratio hE hq0 hBdeg0 hS0 hdeltaPos hetaSpread
      hlocalBudget hspreadBudget hGood hZ

def KahnAggregateInsertionLowerFailure (n codegCap : ℕ)
    (C₀ q etaDeg Bdeg L eta : ℝ)
    (H : Finset (Edge n)) : Prop :=
  KahnAggregateInsertionGood n H.card codegCap C₀ q etaDeg Bdeg H ∧
    ¬ GlobalLowerWeightSpread n H L eta

lemma kahnAggregateInsertion_globalLower_fixed_failure_probability_le
    {n M codegCap : ℕ}
    {C₀ sigma E delta etaSpread etaGlobal r q etaDeg Bdeg S L : ℝ}
    (hn : 3 ≤ n) (hM : 0 < M)
    (hMtop : M < (allEdges n).card)
    (hC0 : 0 ≤ C₀ + 1) (hsigma : 0 < sigma)
    (hratio :
      1 < ((3 * (M + 1) : ℕ) : ℝ) * sigma /
        ((18 * n * (codegCap + 1) : ℕ) : ℝ))
    (hE :
      (3 * n : ℝ) * Real.sqrt sigma +
          (3 * n : ℝ) * (C₀ + 1 + 14 + Real.log 2) /
            Real.log (((3 * (M + 1) : ℕ) : ℝ) * sigma /
              ((18 * n * (codegCap + 1) : ℕ) : ℝ)) ≤ E)
    (hq0 : 0 ≤ q) (hBdeg0 : 0 ≤ Bdeg) (hS0 : 0 ≤ S)
    (hdelta0 : 0 ≤ delta) (hdeltaPos : 0 < delta)
    (hdelta1 : delta ≤ 1) (hetaSpread : 0 ≤ etaSpread)
    (hlocalBudget :
      (3 * n : ℝ) *
          (4 * (3 * (C₀ + 1) * (n : ℝ) + 12 * Real.sqrt n +
            10 * (Real.sqrt (Real.sqrt E * Real.sqrt (3 * n : ℝ)) *
              Real.sqrt (3 * n : ℝ)))) ≤ S ^ 2)
    (hspreadBudget :
      S + (3 * n : ℝ) *
          ((q + 2 * (n : ℝ) / M) +
            (etaDeg + 1 / (n : ℝ)) *
              (1 + (Bdeg + (n : ℝ) / M))) ≤
        3 * etaSpread * delta * (n : ℝ))
    (hr : 0 < r)
    (hglobalBudget : r + (M : ℝ) ≤
      etaGlobal * (allEdges n).card)
    (hL : L ≤ (1 - delta) * (M : ℝ) / (M + 1)) :
    finsetProbability (sample n M)
        (KahnAggregateInsertionLowerFailure n codegCap C₀
          q etaDeg Bdeg L etaGlobal) ≤
      etaSpread * (((allEdges n).card - M : ℕ) : ℝ) / r := by
  have hbase := kahnAggregateInsertion_globalLower_failure_probability_le
    hn hM hMtop hC0 hsigma hratio hE hq0 hBdeg0 hS0 hdelta0
    hdeltaPos hdelta1 hetaSpread hlocalBudget hspreadBudget hr hglobalBudget
  calc
    finsetProbability (sample n M)
        (KahnAggregateInsertionLowerFailure n codegCap C₀
          q etaDeg Bdeg L etaGlobal) ≤
      finsetProbability (sample n M)
        (fun H ↦ KahnAggregateInsertionGood n M codegCap C₀
            q etaDeg Bdeg H ∧
          ¬ GlobalLowerWeightSpread n H
            ((1 - delta) * (M : ℝ) / (M + 1)) etaGlobal) := by
      apply finsetProbability_mono_event
      intro H hHs hfail
      have hcard := (mem_sample.mp hHs).2
      refine ⟨?_, ?_⟩
      · simpa only [KahnAggregateInsertionLowerFailure, hcard] using hfail.1
      · intro hstrong
        exact hfail.2 (globalLowerWeightSpread_mono H hL hstrong)
    _ ≤ etaSpread * (((allEdges n).card - M : ℕ) : ℝ) / r := hbase

end

end Erdos747
