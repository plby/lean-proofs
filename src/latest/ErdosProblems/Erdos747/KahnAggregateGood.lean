import ErdosProblems.Erdos747.Core

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Count, codegree, and aggregate-degree hypotheses actually used by the
one-edge entropy argument.  Unlike `RefinedInsertionGood`, this predicate
does not impose a uniform positive minimum degree. -/
def KahnAggregateInsertionGood (n M codegCap : ℕ)
    (C₀ q etaDeg Bdeg : ℝ) (H : Finset (Edge n)) : Prop :=
  H ∈ sample n M ∧
    HasPerfectMatching n H ∧
    KahnCountLower H C₀ ∧
    (∀ u v : Vertex n, u ≠ v →
      vertexCodegree H u v ≤ codegCap) ∧
    DegreeAggregateRegular n M q etaDeg Bdeg H

lemma kahnAggregateInsertionGood_to_refined {n M codegCap : ℕ}
    {C₀ q etaDeg Bdeg : ℝ} {H : Finset (Edge n)}
    (h : KahnAggregateInsertionGood n M codegCap C₀
      q etaDeg Bdeg H) :
    RefinedAggregateInsertionGood n M 0 Bdeg codegCap C₀
      q etaDeg Bdeg H := by
  rcases h with ⟨hsample, hpm, hcount, hcodeg, haggregate⟩
  refine ⟨⟨⟨hsample, hpm, ?_⟩, hcount, hcodeg⟩, haggregate⟩
  intro v
  constructor
  · norm_num
  · exact haggregate.2 v

lemma kahnAggregateInsertionGood_hasPerfectMatching {n M codegCap : ℕ}
    {C₀ q etaDeg Bdeg : ℝ} {H : Finset (Edge n)}
    (h : KahnAggregateInsertionGood n M codegCap C₀
      q etaDeg Bdeg H) :
    HasPerfectMatching n H := h.2.1

lemma kahnAggregateInsertionGood_presentWeightSpread
    {n M codegCap : ℕ}
    {C₀ sigma E delta etaSpread q etaDeg Bdeg S : ℝ}
    (hn : 3 ≤ n) (hM : 0 < M)
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
    (hdelta : 0 < delta) (hetaSpread : 0 ≤ etaSpread)
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
    {H : Finset (Edge n)}
    (hGood : KahnAggregateInsertionGood n M codegCap C₀
      q etaDeg Bdeg H)
    {Z : Edge n} (hZ : Z ∈ allEdges n \ H) :
    PresentWeightSpread (insert Z H) delta etaSpread := by
  exact refinedInsertionGood_presentWeightSpread_aggregate
    hn hM hC0 hsigma hratio hE hq0 hBdeg0 hS0 hdelta hetaSpread
    hlocalBudget hspreadBudget
    (kahnAggregateInsertionGood_to_refined hGood) hZ

lemma kahnAggregateInsertion_globalUpper_failure_probability_le
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
    (hdelta : 0 < delta) (hetaSpread : 0 ≤ etaSpread)
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
    (hu : (1 + delta) * ((n : ℝ) / (M + 1)) ≤ 1 / 2)
    (hr : 0 < r)
    (hglobalBudget : r + (M : ℝ) ≤
      etaGlobal * (allEdges n).card) :
    finsetProbability (sample n M)
        (fun H ↦ KahnAggregateInsertionGood n M codegCap C₀
            q etaDeg Bdeg H ∧
          ¬ GlobalUpperWeightSpread n H (2 * (1 + delta)) etaGlobal) ≤
      etaSpread * (((allEdges n).card - M : ℕ) : ℝ) / r := by
  apply good_globalUpper_failure_probability_le
    (show 0 < n by omega) hM hMtop hdelta.le hetaSpread hr hu hglobalBudget
  · intro H hGood
    exact kahnAggregateInsertionGood_hasPerfectMatching hGood
  · intro H hHs hGood Z hZ
    exact kahnAggregateInsertionGood_presentWeightSpread
      hn hM hC0 hsigma hratio hE hq0 hBdeg0 hS0 hdelta hetaSpread
      hlocalBudget hspreadBudget hGood hZ

end

end Erdos747
