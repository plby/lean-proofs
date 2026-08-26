import ErdosProblems.Erdos747.ThinningExceptions

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Residual present spreading and pointwise completion survival -/

lemma refinedInsertionGood_presentWeightSpread_self
    {n M codegCap : ℕ}
    {a B C₀ sigma E delta eta : ℝ}
    (hn : 3 ≤ n) (hM : 0 < M) (hcap : 0 < codegCap)
    (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hC0 : 0 ≤ C₀) (hsigma : 0 < sigma)
    (hratio :
      1 < ((3 * M : ℕ) : ℝ) * sigma /
        ((18 * n * codegCap : ℕ) : ℝ))
    (hE :
      (3 * n : ℝ) * Real.sqrt sigma +
          (3 * n : ℝ) * (C₀ + 14 + Real.log 2) /
            Real.log (((3 * M : ℕ) : ℝ) * sigma /
              ((18 * n * codegCap : ℕ) : ℝ)) ≤ E)
    (heta : 0 ≤ eta) (hgap : 1 / a < delta)
    (hbudget :
      (3 * n : ℝ) *
          (4 * (3 * C₀ * (n : ℝ) + 12 * Real.sqrt n +
            10 * (Real.sqrt (Real.sqrt E * Real.sqrt (3 * n : ℝ)) *
              Real.sqrt (3 * n : ℝ)))) ≤
        (eta * (delta - 1 / a) * (n : ℝ))^2)
    {H : Finset (Edge n)}
    (hGood : RefinedInsertionGood n M a B codegCap C₀ H) :
    PresentWeightSpread H delta eta := by
  rcases hGood with ⟨hcoarse, hcount, hcodeg⟩
  rcases hcoarse with ⟨hHs, hpm, hdegree⟩
  rcases mem_sample.mp hHs with ⟨hHall, hHcard⟩
  have hPhi : (perfectMatchings n H).card ≠ 0 := by
    exact Finset.card_ne_zero.mpr
      (hasPerfectMatching_iff_perfectMatchings_nonempty.mp hpm)
  have hincident : (matchingIncidentPairs H).card = 3 * M := by
    rw [card_matchingIncidentPairs H hHall, hHcard]
  have herrorRaw := matchingEntropyGenericityError_le_of_countLower
    hn hcap hHall hPhi hcodeg C₀ sigma hC0 hsigma hcount
    (by simpa only [hincident] using hratio)
  have herror : matchingEntropyGenericityError H ≤ E :=
    herrorRaw.trans (by simpa only [hincident] using hE)
  have hreg : InverseDegreeRegular H (1 / a) := by
    apply inverseDegreeRegular_of_lower_bound H a (by omega) (by omega)
      ha0 ha1
    intro v
    simpa only [hHcard] using (hdegree v).1
  exact presentWeightSpread_of_countLower_and_errorBound
    hn hHall hPhi C₀ E (1 / a) delta eta hcount herror
      heta hgap hreg hbudget

lemma completionThinning_relative_lower_failure_probability_le_weight
    {n t : ℕ} (H : Finset (Edge n)) {Z : Edge n}
    (hZ : Z ∈ allEdges n) (delta eta r theta u : ℝ)
    (hn : 2 ≤ n) (hdelta : 0 ≤ delta) (heta : 0 ≤ eta)
    (hH : H.Nonempty)
    (hspread : PresentWeightSpread
      (reindexGraphAway H Z hZ) delta eta)
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
  have hcount : ((completionMatchings n H Z).card : ℝ) =
      completionWeight H Z := by
    exact_mod_cast (completionWeight_eq_card_completionMatchings
      H Z (by omega) hZ).symm
  have hbudget' :
      r * ((completionMatchings n H Z).card : ℝ) + u ≤
        ((completionMatchings n H Z).card : ℝ) *
          (1 - ((n - 1 : ℕ) : ℝ) /
            (H \ completionHeavyEdges H Z
              ((1 + delta) * matchingWeightTarget (n - 1)
                (reindexGraphAway H Z hZ))).card)^t := by
    simpa only [hcount] using hbudget
  simpa only [hcount] using
    completionThinning_relative_lower_failure_probability_le
      H hZ delta eta r theta u hn hdelta heta hH hspread hs hb hm
        htheta0 htheta htCard hcollision hbudget'

lemma residualRefinedInheritance_presentWeightSpread
    {n M d D codegCap : ℕ} {a B c C₀ C₁ : ℝ}
    {H : Finset (Edge n)} {Z : Edge n}
    (hn : 4 ≤ n) (hM : 0 < M) (hH : H ∈ sample n M)
    (hZ : Z ∈ allEdges n)
    (ha0 : 0 < a) (ha1 : a ≤ 1) (hB0 : 0 ≤ B) (hc : 0 < c)
    (ha : a * ((M : ℝ) / ((n - 1 : ℕ) : ℝ)) ≤ d)
    (hB : (D : ℝ) ≤ B *
      (((M - 3 * D : ℕ) : ℝ) / ((n - 1 : ℕ) : ℝ)))
    (hgood : ResidualRefinedInheritanceGood
      n M d D codegCap a B c C₀ C₁ H)
    (hweight : c^2 * matchingWeightTarget n H ≤ completionWeight H Z)
    (hcap : 0 < codegCap) (hC1 : 0 ≤ C₁) {sigma E delta eta : ℝ}
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
    (heta : 0 ≤ eta) (hgap : 1 / a < delta)
    (hbudget :
      (3 * (n - 1 : ℕ) : ℝ) *
          (4 * (3 * C₁ * ((n - 1 : ℕ) : ℝ) +
            12 * Real.sqrt (n - 1 : ℕ) +
            10 * (Real.sqrt
              (Real.sqrt E * Real.sqrt (3 * (n - 1 : ℕ) : ℝ)) *
                Real.sqrt (3 * (n - 1 : ℕ) : ℝ)))) ≤
        (eta * (delta - 1 / a) * ((n - 1 : ℕ) : ℝ))^2) :
    PresentWeightSpread (reindexGraphAway H Z hZ) delta eta := by
  rcases hgood with
    ⟨hPhi, hcount, hdegreeLower, hdegreeUpper, hcodeg, hcountBudget⟩
  have hrefined : RefinedInsertionGood (n - 1)
      (reindexGraphAway H Z hZ).card a B codegCap C₁
      (reindexGraphAway H Z hZ) := by
    exact reindexGraphAway_refinedInsertionGood_of_weightLower
      (show 2 ≤ n by omega) hM hH hZ ha0.le hB0 hc hPhi hcount hweight
        hdegreeLower hdegreeUpper hcodeg ha hB (hcountBudget Z hZ hweight)
  have hJpos : 0 < (reindexGraphAway H Z hZ).card := by
    rcases hrefined.1.2.1 with ⟨F, hFsub, hFcard, hFmatching⟩
    calc
      0 < n - 1 := by omega
      _ = F.card := hFcard.symm
      _ ≤ (reindexGraphAway H Z hZ).card := Finset.card_le_card hFsub
  exact refinedInsertionGood_presentWeightSpread_self
    (show 3 ≤ n - 1 by omega) hJpos hcap ha0 ha1 hC1 hsigma
      hratio hE heta hgap hbudget hrefined

/-- The residual-inheritance package supplies exactly the spreading input
needed by the completion-weight deletion martingale.  Keeping this
specialization separate makes the later thinning argument depend only on the
fixed-edge structural package and explicit numerical inequalities. -/
lemma completionThinning_relative_lower_failure_probability_le_of_residualInheritance
    {n M d D codegCap t : ℕ} {a B c C₀ C₁ : ℝ}
    {H : Finset (Edge n)} {Z : Edge n}
    (hn : 4 ≤ n) (hM : 0 < M) (hH : H ∈ sample n M)
    (hZ : Z ∈ allEdges n)
    (ha0 : 0 < a) (ha1 : a ≤ 1) (hB0 : 0 ≤ B) (hc : 0 < c)
    (ha : a * ((M : ℝ) / ((n - 1 : ℕ) : ℝ)) ≤ d)
    (hB : (D : ℝ) ≤ B *
      (((M - 3 * D : ℕ) : ℝ) / ((n - 1 : ℕ) : ℝ)))
    (hgood : ResidualRefinedInheritanceGood
      n M d D codegCap a B c C₀ C₁ H)
    (hweight : c^2 * matchingWeightTarget n H ≤ completionWeight H Z)
    (hcap : 0 < codegCap) (hC1 : 0 ≤ C₁)
    (sigma E delta eta r theta u : ℝ)
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
    (hdelta : 0 ≤ delta) (heta : 0 ≤ eta)
    (hgap : 1 / a < delta)
    (hspreadBudget :
      (3 * (n - 1 : ℕ) : ℝ) *
          (4 * (3 * C₁ * ((n - 1 : ℕ) : ℝ) +
            12 * Real.sqrt (n - 1 : ℕ) +
            10 * (Real.sqrt
              (Real.sqrt E * Real.sqrt (3 * (n - 1 : ℕ) : ℝ)) *
                Real.sqrt (3 * (n - 1 : ℕ) : ℝ)))) ≤
        (eta * (delta - 1 / a) * ((n - 1 : ℕ) : ℝ))^2)
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
    residualRefinedInheritance_presentWeightSpread
      hn hM hH hZ ha0 ha1 hB0 hc ha hB hgood hweight hcap hC1
        hsigma hratio hE heta hgap hspreadBudget
  exact completionThinning_relative_lower_failure_probability_le_weight
    H hZ delta eta r theta u (show 2 ≤ n by omega) hdelta heta hHne
      hspread hs hb hm htheta0 htheta htCard hcollision hbudget

end

end Erdos747
