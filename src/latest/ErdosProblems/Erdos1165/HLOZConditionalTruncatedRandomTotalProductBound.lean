/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZConditionalRandomTotalProductBound

/-!
# Conditional random-total tails with truncated adjacent windows

An accepted stopped creation fibre restricts every away total to a broad
coordinate window.  Near the creation threshold, a canonical adjacent
failure window need not be contained in that broad window.  The conditional
product law only sees its intersection with the broad window, however.  This
file records that exact finite algebra so callers need not assert the false
whole-window containment.
-/

open scoped BigOperators

namespace Erdos1165.HLOZConditionalTruncatedRandomTotalProductBound

open FiniteDominoProductLaw HeterogeneousProductTail
open HLOZAllSixBandProductClosure
open HLOZConditionalRandomTotalProductBound
open NearFavoriteThresholded
open TilingConditionalCappedMarginalization

noncomputable section

variable {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
variable {State : Coordinate → Type*} [∀ c, Fintype (State c)]

omit [DecidableEq Coordinate] [∀ c, Fintype (State c)] in
/-- On a vector already lying in the coordinatewise base window, intersecting
the two adjacent windows with that base does not change either their support
or their upper count. -/
theorem randomTotalThresholdedUpperTail_inter_base_iff
    (base upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (base c)] [∀ c, DecidablePred (upper c)]
    [∀ c, DecidablePred (lower c)]
    (threshold : ℕ → ℕ) (G j bound : ℕ) (ℓ : ∀ c, State c)
    (hbase : ∀ c, base c (ℓ c)) :
    randomTotalThresholdedUpperTail
        (fun c v ↦ upper c v ∧ base c v)
        (fun c v ↦ lower c v ∧ base c v)
        threshold G j bound ℓ ↔
      randomTotalThresholdedUpperTail upper lower threshold G j bound ℓ := by
  have hsupport :
      pairSupport (fun c v ↦ upper c v ∧ base c v)
          (fun c v ↦ lower c v ∧ base c v) ℓ =
        pairSupport upper lower ℓ := by
    ext c
    simp only [pairSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    simp [hbase c]
  have hupper :
      upperCount (fun c v ↦ upper c v ∧ base c v) ℓ =
        upperCount upper ℓ := by
    unfold upperCount
    apply Finset.sum_congr rfl
    intro c _hc
    simp [hbase c]
  unfold randomTotalThresholdedUpperTail
  rw [hsupport, hupper]

/-- Aggregate conditional product bound using the actually available pieces
of the adjacent windows.  The ratio premise is stated on `upper ∩ base`
and `lower ∩ base`; no whole-window inclusion in the accepted creation
screen is required. -/
theorem conditionalScreenMass_randomTotalThresholdedUpperTail_inter_base_le_of_iff
    (pointMass : Coordinate → ℕ → ℝ) (upperBound : Coordinate → ℕ)
    (base upper lower : ∀ c, Fin (upperBound c) → Prop)
    [∀ c, DecidablePred (base c)] [∀ c, DecidablePred (upper c)]
    [∀ c, DecidablePred (lower c)]
    (threshold : ℕ → ℕ) (G j bound : ℕ)
    {rawBase rawScreen : TruncatedTotals upperBound → Prop}
    [DecidablePred rawBase] [DecidablePred rawScreen]
    (hrawBase : ∀ ell, rawBase ell ↔ ∀ c, base c (ell c))
    (hrawScreen : ∀ ell, rawScreen ell ↔
      (∀ c, base c (ell c)) ∧
        randomTotalThresholdedUpperTail upper lower threshold G j bound ell)
    (hweight : ∀ c (v : Fin (upperBound c)),
      0 ≤ coordinateMass pointMass upperBound c v)
    (hbase : ∀ c, 0 < ∑ v : Fin (upperBound c),
      if base c v then coordinateMass pointMass upperBound c v else 0)
    (hdisjoint : ∀ c v, ¬ (upper c v ∧ lower c v))
    {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hratio : ∀ c,
      (∑ v, if upper c v ∧ base c v then
          coordinateMass pointMass upperBound c v else 0) ≤
        C * ∑ v, if lower c v ∧ base c v then
          coordinateMass pointMass upperBound c v else 0)
    (henvelope : ∀ total < bound + 1,
      (1 + C / (1 + C)) ^ total /
          (2 : ℝ) ^ thresholdedGrowthCut threshold G j total ≤ K) :
    conditionalScreenMass pointMass upperBound rawBase rawScreen ≤ K := by
  classical
  let upperBase := fun c (v : Fin (upperBound c)) ↦ upper c v ∧ base c v
  let lowerBase := fun c (v : Fin (upperBound c)) ↦ lower c v ∧ base c v
  apply conditionalScreenMass_randomTotalThresholdedUpperTail_le_of_iff
    pointMass upperBound base upperBase lowerBase threshold G j bound
      hrawBase
  · intro ell
    rw [hrawScreen]
    constructor
    · rintro ⟨hbaseEll, htail⟩
      exact ⟨hbaseEll,
        (randomTotalThresholdedUpperTail_inter_base_iff
          base upper lower threshold G j bound ell hbaseEll).mpr htail⟩
    · rintro ⟨hbaseEll, htail⟩
      exact ⟨hbaseEll,
        (randomTotalThresholdedUpperTail_inter_base_iff
          base upper lower threshold G j bound ell hbaseEll).mp htail⟩
  · exact hweight
  · exact hbase
  · intro c v hv
    exact hv.2
  · intro c v hv
    exact hv.2
  · intro c v hv
    exact hdisjoint c v ⟨hv.1.1, hv.2.1⟩
  · exact hC
  · exact hK
  · simpa only [upperBase, lowerBase] using hratio
  · exact henvelope

end

end Erdos1165.HLOZConditionalTruncatedRandomTotalProductBound
