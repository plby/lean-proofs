import ErdosProblems.Erdos747.AggregatePresentSpread

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Pointwise survival from residual aggregate inheritance -/

/-- Residual aggregate inheritance supplies the present-edge spreading of a
high-weight triple's reindexed residual graph. -/
lemma residualAggregateInheritance_presentWeightSpread
    {n M d D codegCap : ℕ}
    {c C₀ C₁ q₁ etaDeg₁ Bdeg₁ : ℝ}
    {H : Finset (Edge n)} {Z : Edge n}
    (hn : 4 ≤ n) (hM : 0 < M) (hH : H ∈ sample n M)
    (hZ : Z ∈ allEdges n) (hc : 0 < c)
    (hgood : ResidualAggregateInheritanceGood
      n M d D codegCap c C₀ C₁ q₁ etaDeg₁ Bdeg₁ H)
    (hweight : c^2 * matchingWeightTarget n H ≤ completionWeight H Z)
    (hcap : 0 < codegCap) (hC1 : 0 ≤ C₁)
    {sigma E delta eta S : ℝ}
    (hsigma : 0 < sigma)
    (hratio :
      1 < ((3 * (reindexGraphAway H Z hZ).card : ℕ) : ℝ) * sigma /
        ((18 * (n - 1) * codegCap : ℕ) : ℝ))
    (hE :
      (3 * (n - 1 : ℕ) : ℝ) * Real.sqrt sigma +
          (3 * (n - 1 : ℕ) : ℝ) * (C₁ + 14 + Real.log 2) /
            Real.log
              (((3 * (reindexGraphAway H Z hZ).card : ℕ) : ℝ) * sigma /
                ((18 * (n - 1) * codegCap : ℕ) : ℝ)) ≤ E)
    (hq0 : 0 ≤ q₁) (hBdeg0 : 0 ≤ Bdeg₁) (hS0 : 0 ≤ S)
    (hdelta : 0 < delta) (heta : 0 ≤ eta)
    (hlocalBudget :
      (3 * (n - 1 : ℕ) : ℝ) *
          (4 * (3 * C₁ * ((n - 1 : ℕ) : ℝ) +
            12 * Real.sqrt (n - 1 : ℕ) +
            10 * (Real.sqrt
              (Real.sqrt E * Real.sqrt (3 * (n - 1 : ℕ) : ℝ)) *
                Real.sqrt (3 * (n - 1 : ℕ) : ℝ)))) ≤ S ^ 2)
    (hspreadBudget :
      S + (3 * (n - 1 : ℕ) : ℝ) *
          (q₁ + etaDeg₁ * (1 + Bdeg₁)) ≤
        3 * eta * delta * ((n - 1 : ℕ) : ℝ)) :
    PresentWeightSpread (reindexGraphAway H Z hZ) delta eta := by
  have haggregate := reindexGraphAway_kahnAggregateInsertionGood
    (show 2 ≤ n by omega) hM hH hZ hc hgood hweight
  have hJpos : 0 < (reindexGraphAway H Z hZ).card := by
    rcases haggregate.2.1 with ⟨F, hFsub, hFcard, hFmatching⟩
    calc
      0 < n - 1 := by omega
      _ = F.card := hFcard.symm
      _ ≤ (reindexGraphAway H Z hZ).card := Finset.card_le_card hFsub
  exact kahnAggregateInsertionGood_presentWeightSpread_self
    (show 3 ≤ n - 1 by omega) hJpos hcap hC1 hsigma hratio hE
      hq0 hBdeg0 hS0 hdelta heta hlocalBudget hspreadBudget haggregate

/-- The aggregate residual package specializes the generic completion
martingale bound to every triple above the residual weight cutoff. -/
lemma completionThinning_relative_lower_failure_probability_le_of_residualAggregate
    {n M d D codegCap t : ℕ}
    {c C₀ C₁ q₁ etaDeg₁ Bdeg₁ : ℝ}
    {H : Finset (Edge n)} {Z : Edge n}
    (hn : 4 ≤ n) (hM : 0 < M) (hH : H ∈ sample n M)
    (hZ : Z ∈ allEdges n) (hc : 0 < c)
    (hgood : ResidualAggregateInheritanceGood
      n M d D codegCap c C₀ C₁ q₁ etaDeg₁ Bdeg₁ H)
    (hweight : c^2 * matchingWeightTarget n H ≤ completionWeight H Z)
    (hcap : 0 < codegCap) (hC1 : 0 ≤ C₁)
    (sigma E delta eta S r theta u : ℝ)
    (hsigma : 0 < sigma)
    (hratio :
      1 < ((3 * (reindexGraphAway H Z hZ).card : ℕ) : ℝ) * sigma /
        ((18 * (n - 1) * codegCap : ℕ) : ℝ))
    (hE :
      (3 * (n - 1 : ℕ) : ℝ) * Real.sqrt sigma +
          (3 * (n - 1 : ℕ) : ℝ) * (C₁ + 14 + Real.log 2) /
            Real.log
              (((3 * (reindexGraphAway H Z hZ).card : ℕ) : ℝ) * sigma /
                ((18 * (n - 1) * codegCap : ℕ) : ℝ)) ≤ E)
    (hq0 : 0 ≤ q₁) (hBdeg0 : 0 ≤ Bdeg₁) (hS0 : 0 ≤ S)
    (hdelta : 0 ≤ delta) (hdeltaPos : 0 < delta) (heta : 0 ≤ eta)
    (hlocalBudget :
      (3 * (n - 1 : ℕ) : ℝ) *
          (4 * (3 * C₁ * ((n - 1 : ℕ) : ℝ) +
            12 * Real.sqrt (n - 1 : ℕ) +
            10 * (Real.sqrt
              (Real.sqrt E * Real.sqrt (3 * (n - 1 : ℕ) : ℝ)) *
                Real.sqrt (3 * (n - 1 : ℕ) : ℝ)))) ≤ S ^ 2)
    (hspreadBudget :
      S + (3 * (n - 1 : ℕ) : ℝ) *
          (q₁ + etaDeg₁ * (1 + Bdeg₁)) ≤
        3 * eta * delta * ((n - 1 : ℕ) : ℝ))
    (hHne : H.Nonempty)
    (hs : (H \ completionHeavyEdges H Z
      ((1 + delta) * matchingWeightTarget (n - 1)
        (reindexGraphAway H Z hZ))).Nonempty)
    (hb : 0 < (1 + delta) * matchingWeightTarget (n - 1)
      (reindexGraphAway H Z hZ))
    (hm : ((n - 1 : ℕ) : ℝ) <
      ((H \ completionHeavyEdges H Z
        ((1 + delta) * matchingWeightTarget (n - 1)
          (reindexGraphAway H Z hZ))).card : ℝ))
    (htheta0 : 0 ≤ theta)
    (htheta : |theta *
      ((1 + delta) * matchingWeightTarget (n - 1)
        (reindexGraphAway H Z hZ))| ≤ 1 / 2)
    (htCard : t ≤ (H \ completionHeavyEdges H Z
      ((1 + delta) * matchingWeightTarget (n - 1)
        (reindexGraphAway H Z hZ))).card)
    (hcollision : 2 * t * t ≤
      (H \ completionHeavyEdges H Z
        ((1 + delta) * matchingWeightTarget (n - 1)
          (reindexGraphAway H Z hZ))).card)
    (hbudget :
      r * (completionWeight H Z : ℝ) + u ≤
        (completionWeight H Z : ℝ) *
          (1 - ((n - 1 : ℕ) : ℝ) /
            (H \ completionHeavyEdges H Z
              ((1 + delta) * matchingWeightTarget (n - 1)
                (reindexGraphAway H Z hZ))).card)^t) :
    finsetProbability (H.powersetCard t)
        (fun T ↦ (completionWeight (H \ T) Z : ℝ) <
          r * (completionWeight H Z : ℝ)) ≤
      (t : ℝ) *
          ((completionHeavyEdges H Z
            ((1 + delta) * matchingWeightTarget (n - 1)
              (reindexGraphAway H Z hZ))).card : ℝ) / H.card +
        2 * Real.exp
          (theta^2 * ((t : ℝ) *
            ((completionWeight H Z : ℝ) *
              ((n - 1 : ℕ) : ℝ) /
                (H \ completionHeavyEdges H Z
                  ((1 + delta) * matchingWeightTarget (n - 1)
                    (reindexGraphAway H Z hZ))).card)) *
              ((1 + delta) * matchingWeightTarget (n - 1)
                (reindexGraphAway H Z hZ)) - theta * u) := by
  have hspread : PresentWeightSpread
      (reindexGraphAway H Z hZ) delta eta :=
    residualAggregateInheritance_presentWeightSpread
      hn hM hH hZ hc hgood hweight hcap hC1 hsigma hratio hE
        hq0 hBdeg0 hS0 hdeltaPos heta hlocalBudget hspreadBudget
  exact completionThinning_relative_lower_failure_probability_le_weight
    H hZ delta eta r theta u (show 2 ≤ n by omega) hdelta heta hHne
      hspread hs hb hm htheta0 htheta htCard hcollision hbudget

end

end Erdos747
