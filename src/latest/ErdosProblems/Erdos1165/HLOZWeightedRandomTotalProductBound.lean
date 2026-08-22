/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZAllSixBandProductClosure
import ErdosProblems.Erdos1165.HLOZSharpProductNumerics

/-!
# Total-weighted heterogeneous random-tail products

Actual-rank replacement screens split a stopped product according to the
number of threshold-relevant coordinates.  Their rank multiplicity is thus
a function of the realized adjacent-pair total.  This file carries an
arbitrary nonnegative total weight through the exact-total product
partition.  It is purely finite algebra and contains no path-space or
probability premise.
-/

open scoped BigOperators

namespace Erdos1165.HLOZWeightedRandomTotalProductBound

open FiniteDominoProductLaw HeterogeneousProductTail
open HLOZAllSixBandProductClosure NearFavoriteThresholded
open HLOZProposition48Candidates
open HLOZSharpProductNumerics

noncomputable section

variable {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
variable {State : Coordinate → Type*} [∀ c, Fintype (State c)]

/-- Partition a random-total upper tail by its exact pair total while
retaining a scalar weight depending on that total. -/
theorem sum_weightedRandomTotalThresholdedUpperTail_eq_sum_fixedTotal
    (weight : ∀ c, State c → ℝ)
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (threshold : ℕ → ℕ) (G j bound : ℕ) (totalWeight : ℕ → ℝ) :
    (∑ ell : ∀ c, State c,
        if randomTotalThresholdedUpperTail upper lower threshold G j bound ell
        then totalWeight (pairSupport upper lower ell).card *
          productPointMass weight ell
        else 0) =
      ∑ total ∈ Finset.range (bound + 1),
        ∑ ell : ∀ c, State c,
          if fixedTotalUpperTail upper lower total
              (thresholdedGrowthCut threshold G j total) ell
          then totalWeight total * productPointMass weight ell
          else 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ell _
  by_cases hbound : (pairSupport upper lower ell).card < bound + 1
  · have hmem : (pairSupport upper lower ell).card ∈
        Finset.range (bound + 1) := Finset.mem_range.mpr hbound
    rw [Finset.sum_eq_single (pairSupport upper lower ell).card]
    · by_cases hcut :
          thresholdedGrowthCut threshold G j
              (pairSupport upper lower ell).card ≤ upperCount upper ell <;>
        simp [randomTotalThresholdedUpperTail, hbound, hcut,
          fixedTotalUpperTail]
    · intro total htotal hne
      have hcard : (pairSupport upper lower ell).card ≠ total := Ne.symm hne
      simp [fixedTotalUpperTail, hcard]
    · exact fun hnot ↦ (hnot hmem).elim
  · have hout : (pairSupport upper lower ell).card ∉
        Finset.range (bound + 1) := by simpa using hbound
    rw [Finset.sum_eq_zero]
    · simp [randomTotalThresholdedUpperTail, hbound]
    · intro total htotal
      have hne : (pairSupport upper lower ell).card ≠ total := by
        intro heq
        apply hout
        simpa [heq] using htotal
      simp [fixedTotalUpperTail, hne]

/-- The heterogeneous random-total bound with an arbitrary nonnegative
multiplicity attached to the realized pair total.  The multiplicity is
absorbed pointwise in the displayed envelope before the exact-total masses
are summed, so no factor equal to the number of possible totals is lost. -/
theorem weightedRandomTotalThresholdedUpperTail_product_bound
    (weight : ∀ c, State c → ℝ)
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (threshold : ℕ → ℕ) (G j bound : ℕ) (totalWeight : ℕ → ℝ)
    (hweight : ∀ c v, 0 ≤ weight c v)
    (hnorm : ∀ c, (∑ v, weight c v) ≤ 1)
    (hdisjoint : ∀ c v, ¬ (upper c v ∧ lower c v))
    {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (htotalWeight : ∀ total, 0 ≤ totalWeight total)
    (hratio : ∀ c,
      (∑ v, if upper c v then weight c v else 0) ≤
        C * ∑ v, if lower c v then weight c v else 0)
    (henvelope : ∀ total < bound + 1,
      totalWeight total *
        ((1 + C / (1 + C)) ^ total /
          (2 : ℝ) ^ thresholdedGrowthCut threshold G j total) ≤ K) :
    (∑ ell : ∀ c, State c,
        if randomTotalThresholdedUpperTail upper lower threshold G j bound ell
        then totalWeight (pairSupport upper lower ell).card *
          productPointMass weight ell
        else 0) ≤ K := by
  rw [sum_weightedRandomTotalThresholdedUpperTail_eq_sum_fixedTotal]
  calc
    (∑ total ∈ Finset.range (bound + 1),
      ∑ ell : ∀ c, State c,
        if fixedTotalUpperTail upper lower total
            (thresholdedGrowthCut threshold G j total) ell
        then totalWeight total * productPointMass weight ell
        else 0) ≤
        ∑ total ∈ Finset.range (bound + 1),
          exactPairTotalMass weight upper lower total *
            (totalWeight total *
              ((1 + C / (1 + C)) ^ total /
                (2 : ℝ) ^ thresholdedGrowthCut threshold G j total)) := by
      apply Finset.sum_le_sum
      intro total _
      have hfixed := fixedTotalUpperTail_product_bound weight upper lower
        hweight hdisjoint hC hratio total
          (thresholdedGrowthCut threshold G j total)
      have hfixed' :
          (∑ ell : ∀ c, State c,
            if fixedTotalUpperTail upper lower total
                (thresholdedGrowthCut threshold G j total) ell
            then productPointMass weight ell else 0) ≤
              exactPairTotalMass weight upper lower total *
                ((1 + C / (1 + C)) ^ total /
                  (2 : ℝ) ^ thresholdedGrowthCut threshold G j total) := by
        simpa only [mul_div_assoc] using hfixed
      calc
        (∑ ell : ∀ c, State c,
          if fixedTotalUpperTail upper lower total
              (thresholdedGrowthCut threshold G j total) ell
          then totalWeight total * productPointMass weight ell
          else 0) =
            totalWeight total *
              ∑ ell : ∀ c, State c,
                if fixedTotalUpperTail upper lower total
                    (thresholdedGrowthCut threshold G j total) ell
                then productPointMass weight ell else 0 := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro ell _
              by_cases htail : fixedTotalUpperTail upper lower total
                  (thresholdedGrowthCut threshold G j total) ell <;>
                simp [htail]
        _ ≤ totalWeight total *
            (exactPairTotalMass weight upper lower total *
              ((1 + C / (1 + C)) ^ total /
                (2 : ℝ) ^ thresholdedGrowthCut threshold G j total)) :=
          mul_le_mul_of_nonneg_left hfixed' (htotalWeight total)
        _ = exactPairTotalMass weight upper lower total *
            (totalWeight total *
              ((1 + C / (1 + C)) ^ total /
                (2 : ℝ) ^ thresholdedGrowthCut threshold G j total)) := by
          ring
    _ ≤ K := sum_exactPairTotalMass_mul_cost_le weight upper lower hweight
      hnorm bound
      (fun total ↦ totalWeight total *
        ((1 + C / (1 + C)) ^ total /
          (2 : ℝ) ^ thresholdedGrowthCut threshold G j total))
      hK henvelope

/-- The actual endpoint-rank multiplicity is at most `2 * total + 1` on an
exact pair-total piece.  At the canonical `4/3` coordinate ratio it is
absorbed without counting the possible totals; only the deterministic
maximum pair total remains in front of the sharp interface cost. -/
theorem rankMultiplicityWeightedRandomTotal_product_bound_four_thirds
    (weight : ∀ c, State c → ℝ)
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (threshold : ℕ → ℕ) (j bound : ℕ)
    (hweight : ∀ c v, 0 ≤ weight c v)
    (hnorm : ∀ c, (∑ v, weight c v) ≤ 1)
    (hdisjoint : ∀ c v, ¬ (upper c v ∧ lower c v))
    (hratio : ∀ c,
      (∑ v, if upper c v then weight c v else 0) ≤
        (4 / 3 : ℝ) * ∑ v, if lower c v then weight c v else 0) :
    (∑ ell : ∀ c, State c,
        if randomTotalThresholdedUpperTail upper lower threshold shellGrowth48 j bound ell
        then ((2 * (pairSupport upper lower ell).card + 1 : ℕ) : ℝ) *
          productPointMass weight ell
        else 0) ≤
      ((2 * bound + 1 : ℕ) : ℝ) * sharpInterfaceCost threshold j := by
  apply weightedRandomTotalThresholdedUpperTail_product_bound weight upper
    lower threshold shellGrowth48 j bound
      (fun total ↦ ((2 * total + 1 : ℕ) : ℝ))
      hweight hnorm hdisjoint (C := (4 / 3 : ℝ))
      (K := ((2 * bound + 1 : ℕ) : ℝ) * sharpInterfaceCost threshold j)
  · norm_num
  · exact mul_nonneg (Nat.cast_nonneg _) (sharpInterfaceCost_nonneg _ _)
  · intro total
    positivity
  · exact hratio
  · intro total htotal
    have htotalBound : total ≤ bound := by omega
    have hmult : ((2 * total + 1 : ℕ) : ℝ) ≤
        ((2 * bound + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.add_le_add_right (Nat.mul_le_mul_left 2 htotalBound) 1)
    have henvelope := thresholdedProductEnvelope_le_sharpInterfaceCost
      (4 / 3 : ℝ) (by norm_num)
        four_thirds_le_positiveInterfaceRatioConstant threshold j total
    exact mul_le_mul hmult henvelope (by positivity) (Nat.cast_nonneg _)

/-- A strict version of the moment slack used by the sharp product bound.
The spare half-copy of `log 2` per hundred pair coordinates absorbs the
linear actual-rank multiplicity. -/
lemma twoHundred_mul_log_elevenSevenths_le_oneThirtyOne_mul_log_two :
    200 * Real.log (11 / 7 : ℝ) ≤ 131 * Real.log 2 := by
  have hpow : ((11 / 7 : ℝ) ^ 200) ≤ (2 : ℝ) ^ 131 := by
    norm_num
  have hlog := Real.log_le_log
    (by positivity : (0 : ℝ) < (11 / 7 : ℝ) ^ 200) hpow
  rw [Real.log_pow, Real.log_pow] at hlog
  norm_num at hlog
  exact hlog

/-- The strict moment slack pays the actual-rank multiplicity uniformly in
the realized pair total.  In particular, no deterministic upper bound on
that total appears in front of the sharp interface cost. -/
lemma rankMultiplicity_mul_thresholdedProductEnvelope_le_sharp
    (threshold : ℕ → ℕ) (j total : ℕ) :
    ((2 * total + 1 : ℕ) : ℝ) *
        ((1 + (4 / 3 : ℝ) / (1 + (4 / 3 : ℝ))) ^ total /
          (2 : ℝ) ^
            thresholdedGrowthCut threshold shellGrowth48 j total) ≤
      sharpRankConstant * sharpInterfaceCost threshold j := by
  exact _root_.Erdos1165.HLOZSharpProductNumerics.rankMultiplicity_mul_thresholdedProductEnvelope_le_sharp
      (4 / 3 : ℝ) (by norm_num)
      four_thirds_le_positiveInterfaceRatioConstant threshold j total

/-- The weighted random-total product bound with actual endpoint-rank
multiplicity.  Its constant is uniform in the deterministic total cutoff,
so it retains the summable sharp interface rate. -/
theorem rankMultiplicityWeightedRandomTotal_product_bound_sharp
    (weight : ∀ c, State c → ℝ)
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (threshold : ℕ → ℕ) (j bound : ℕ)
    (hweight : ∀ c v, 0 ≤ weight c v)
    (hnorm : ∀ c, (∑ v, weight c v) ≤ 1)
    (hdisjoint : ∀ c v, ¬ (upper c v ∧ lower c v))
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : C ≤ positiveInterfaceRatioConstant)
    (hratio : ∀ c,
      (∑ v, if upper c v then weight c v else 0) ≤
        C * ∑ v, if lower c v then weight c v else 0) :
    (∑ ell : ∀ c, State c,
        if randomTotalThresholdedUpperTail upper lower threshold shellGrowth48 j bound ell
        then ((2 * (pairSupport upper lower ell).card + 1 : ℕ) : ℝ) *
          productPointMass weight ell
        else 0) ≤ sharpRankConstant * sharpInterfaceCost threshold j := by
  apply weightedRandomTotalThresholdedUpperTail_product_bound weight upper
    lower threshold shellGrowth48 j bound
      (fun total ↦ ((2 * total + 1 : ℕ) : ℝ))
      hweight hnorm hdisjoint (C := C)
      (K := sharpRankConstant * sharpInterfaceCost threshold j)
  · exact hC0
  · exact mul_nonneg sharpRankConstant_pos.le
      (sharpInterfaceCost_nonneg _ _)
  · intro total
    positivity
  · exact hratio
  · intro total _
    exact _root_.Erdos1165.HLOZSharpProductNumerics.rankMultiplicity_mul_thresholdedProductEnvelope_le_sharp
        C hC0 hC threshold j total

end

end Erdos1165.HLOZWeightedRandomTotalProductBound
