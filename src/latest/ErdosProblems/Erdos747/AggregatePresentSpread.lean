import ErdosProblems.Erdos747.PresentBadSplit

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Present-edge spreading inside an aggregate-good predecessor -/

/-- The aggregate-good certificate controls the present edges of the
predecessor itself.  This is the no-insertion counterpart of
`kahnAggregateInsertionGood_presentWeightSpread`; it keeps the unshifted
count constant, codegree cap, and aggregate-degree parameters. -/
lemma kahnAggregateInsertionGood_presentWeightSpread_self
    {n M codegCap : ℕ}
    {C₀ sigma E delta etaSpread q etaDeg Bdeg S : ℝ}
    (hn : 3 ≤ n) (hM : 0 < M) (hcap : 0 < codegCap)
    (hC0 : 0 ≤ C₀) (hsigma : 0 < sigma)
    (hratio :
      1 < ((3 * M : ℕ) : ℝ) * sigma /
        ((18 * n * codegCap : ℕ) : ℝ))
    (hE :
      (3 * n : ℝ) * Real.sqrt sigma +
          (3 * n : ℝ) * (C₀ + 14 + Real.log 2) /
            Real.log (((3 * M : ℕ) : ℝ) * sigma /
              ((18 * n * codegCap : ℕ) : ℝ)) ≤ E)
    (hq0 : 0 ≤ q) (hBdeg0 : 0 ≤ Bdeg) (hS0 : 0 ≤ S)
    (hdelta : 0 < delta) (hetaSpread : 0 ≤ etaSpread)
    (hlocalBudget :
      (3 * n : ℝ) *
          (4 * (3 * C₀ * (n : ℝ) + 12 * Real.sqrt n +
            10 * (Real.sqrt (Real.sqrt E * Real.sqrt (3 * n : ℝ)) *
              Real.sqrt (3 * n : ℝ)))) ≤ S ^ 2)
    (hspreadBudget :
      S + (3 * n : ℝ) * (q + etaDeg * (1 + Bdeg)) ≤
        3 * etaSpread * delta * (n : ℝ))
    {H : Finset (Edge n)}
    (hGood : KahnAggregateInsertionGood n M codegCap C₀
      q etaDeg Bdeg H) :
    PresentWeightSpread H delta etaSpread := by
  rcases hGood with ⟨hHs, hpm, hcount, hcodeg, haggregate⟩
  rcases mem_sample.mp hHs with ⟨hHall, hHcard⟩
  have hPhi : (perfectMatchings n H).card ≠ 0 := by
    exact Finset.card_ne_zero.mpr
      (hasPerfectMatching_iff_perfectMatchings_nonempty.mp hpm)
  have hincident : (matchingIncidentPairs H).card = 3 * M := by
    rw [card_matchingIncidentPairs H hHall, hHcard]
  have herrorRaw := matchingEntropyGenericityError_le_of_countLower
    hn hcap hHall hPhi hcodeg C₀ sigma hC0 hsigma hcount
    (by simpa only [hincident] using hratio)
  have herror : matchingEntropyGenericityError H ≤ E := by
    exact herrorRaw.trans (by simpa only [hincident] using hE)
  exact presentWeightSpread_of_countLower_error_aggregate
    hn hM hHall hHcard hPhi C₀ E q etaDeg Bdeg S delta etaSpread
      hcount herror hq0 hBdeg0 haggregate hS0 hdelta hetaSpread
      hlocalBudget hspreadBudget

end

end Erdos747
