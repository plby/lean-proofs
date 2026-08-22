/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/

import ErdosProblems.Erdos1165.NearFavoriteShells

/-!
# Thresholded adjacent-shell propagation

The unthresholded event `G * occupancy j < occupancy (j+1)` need not be rare:
if the adjacent pair contains one candidate, it can have probability bounded
away from zero.  The shell induction never needs that event.  It only needs
to rule out crossing the prescribed threshold in shell `j+1`, after shell
`j` has already been bounded.

This module records the corrected event and, crucially for the stopped
product law, decomposes it over the *actual* adjacent-pair total rather than
postulating one globally fixed binomial sample size.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.NearFavoriteThresholded

open NearFavoriteShells

variable {Omega : Type*}

/-- A growth comparison fails in a way which can actually break the shell
threshold induction. -/
def thresholdedGrowthFailure (occupancy : Omega → ℕ → ℕ)
    (threshold : ℕ → ℕ) (G j : ℕ) : Set Omega :=
  {omega | threshold (j + 1) < occupancy omega (j + 1) ∧
    G * occupancy omega j < occupancy omega (j + 1)}

/-- Either balancedness is unavailable or the threshold-relevant adjacent
growth comparison fails. -/
def thresholdedInterfaceBad (balanced : ℕ → Set Omega)
    (occupancy : Omega → ℕ → ℕ) (threshold : ℕ → ℕ)
    (G j : ℕ) : Set Omega :=
  (balanced j)ᶜ ∪ thresholdedGrowthFailure occupancy threshold G j

/-- Some displayed thresholded interface is bad. -/
def someThresholdedInterfaceBad (balanced : ℕ → Set Omega)
    (occupancy : Omega → ℕ → ℕ) (threshold : ℕ → ℕ)
    (G shellCount : ℕ) : Set Omega :=
  ⋃ j ∈ Finset.range (shellCount - 1),
    thresholdedInterfaceBad balanced occupancy threshold G j

/-- Initial-shell overflow or one threshold-relevant interface failure. -/
def thresholdedGlobalBad (balanced : ℕ → Set Omega)
    (occupancy : Omega → ℕ → ℕ) (threshold : ℕ → ℕ)
    (G shellCount : ℕ) : Set Omega :=
  shellOverflow occupancy threshold 0 ∪
    someThresholdedInterfaceBad balanced occupancy threshold G shellCount

lemma mem_someThresholdedInterfaceBad_iff
    {balanced : ℕ → Set Omega} {occupancy : Omega → ℕ → ℕ}
    {threshold : ℕ → ℕ} {G shellCount : ℕ} {omega : Omega} :
    omega ∈ someThresholdedInterfaceBad balanced occupancy threshold G shellCount ↔
      ∃ j < shellCount - 1,
        omega ∈ thresholdedInterfaceBad balanced occupancy threshold G j := by
  simp [someThresholdedInterfaceBad]

/-- Outside the corrected bad event, all displayed occupancies satisfy their
geometrically compatible thresholds. -/
theorem occupancy_le_threshold_of_notMem_thresholdedGlobalBad
    (balanced : ℕ → Set Omega) (occupancy : Omega → ℕ → ℕ)
    (threshold : ℕ → ℕ) (G shellCount : ℕ)
    (hstep : ∀ j, j + 1 < shellCount →
      G * threshold j ≤ threshold (j + 1))
    {omega : Omega}
    (hgood : omega ∉
      thresholdedGlobalBad balanced occupancy threshold G shellCount) :
    ∀ j < shellCount, occupancy omega j ≤ threshold j := by
  intro j hj
  induction j with
  | zero =>
      by_contra hnot
      apply hgood
      exact Or.inl (Nat.lt_of_not_ge hnot)
  | succ j ih =>
      have hjlt : j < shellCount := by omega
      have hprev : occupancy omega j ≤ threshold j := ih hjlt
      by_contra hnot
      have hupper : threshold (j + 1) < occupancy omega (j + 1) :=
        Nat.lt_of_not_ge hnot
      have hratio : G * occupancy omega j < occupancy omega (j + 1) :=
        (Nat.mul_le_mul_left G hprev).trans_lt
          ((hstep j hj).trans_lt hupper)
      apply hgood
      apply Or.inr
      rw [mem_someThresholdedInterfaceBad_iff]
      exact ⟨j, by omega, Or.inr ⟨hupper, hratio⟩⟩

/-- Excess total occupancy is contained in the corrected finite bad union. -/
theorem totalOverflow_subset_thresholdedGlobalBad
    (balanced : ℕ → Set Omega) (occupancy : Omega → ℕ → ℕ)
    (threshold : ℕ → ℕ) (G shellCount : ℕ)
    (hstep : ∀ j, j + 1 < shellCount →
      G * threshold j ≤ threshold (j + 1)) :
    totalOverflow occupancy threshold shellCount ⊆
      thresholdedGlobalBad balanced occupancy threshold G shellCount := by
  intro omega hoverflow
  by_contra hgood
  have hpoint := occupancy_le_threshold_of_notMem_thresholdedGlobalBad
    balanced occupancy threshold G shellCount hstep hgood
  exact (Nat.not_lt_of_ge (Finset.sum_le_sum fun j hj ↦
    hpoint j (Finset.mem_range.mp hj))) hoverflow

/-- Measure form of the corrected finite shell recurrence. -/
theorem measureReal_totalOverflow_le [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (balanced : ℕ → Set Omega) (occupancy : Omega → ℕ → ℕ)
    (threshold : ℕ → ℕ) (G shellCount : ℕ)
    (hstep : ∀ j, j + 1 < shellCount →
      G * threshold j ≤ threshold (j + 1)) :
    mu.real (totalOverflow occupancy threshold shellCount) ≤
      mu.real (shellOverflow occupancy threshold 0) +
        ∑ j ∈ Finset.range (shellCount - 1),
          mu.real (thresholdedInterfaceBad balanced occupancy threshold G j) := by
  calc
    mu.real (totalOverflow occupancy threshold shellCount) ≤
        mu.real (thresholdedGlobalBad balanced occupancy threshold G shellCount) :=
      measureReal_mono (totalOverflow_subset_thresholdedGlobalBad
        balanced occupancy threshold G shellCount hstep)
    _ ≤ mu.real (shellOverflow occupancy threshold 0) +
        mu.real (someThresholdedInterfaceBad balanced occupancy threshold
          G shellCount) := measureReal_union_le _ _
    _ ≤ mu.real (shellOverflow occupancy threshold 0) +
        ∑ j ∈ Finset.range (shellCount - 1),
          mu.real (thresholdedInterfaceBad balanced occupancy threshold G j) := by
      gcongr
      exact measureReal_biUnion_finset_le (Finset.range (shellCount - 1)) _

/-! ## Decomposition over the random adjacent-pair total -/

/-- The actual total number of candidates in two adjacent shells. -/
def pairTotalLevel (occupancy : Omega → ℕ → ℕ) (j total : ℕ) : Set Omega :=
  {omega | occupancy omega j + occupancy omega (j + 1) = total}

/-- A thresholded interface failure with a fixed adjacent-pair total. -/
def fixedTotalThresholdedFailure (balanced : ℕ → Set Omega)
    (occupancy : Omega → ℕ → ℕ) (threshold : ℕ → ℕ)
    (G j total : ℕ) : Set Omega :=
  balanced j ∩ thresholdedGrowthFailure occupancy threshold G j ∩
    pairTotalLevel occupancy j total

/-- The exact upper-tail cut on a fixed adjacent-pair-total fibre.  Both the
threshold crossing and the adjacent growth ratio are retained. -/
def thresholdedGrowthCut (threshold : ℕ → ℕ) (G j total : ℕ) : ℕ :=
  max (threshold (j + 1) + 1) (growthCut G total)

/-- Finite weighted Markov inequality at the elementary moment parameter
`log 2`.  This version applies directly to a finite product mass: it requires
only nonnegative point weights and a pointwise lower bound on the counted
statistic throughout the screen event. -/
theorem finiteWeight_upperTail_two_pow
    {Sample : Type*} [Fintype Sample]
    (weight : Sample → ℝ) (statistic : Sample → ℕ)
    (event : Sample → Prop) [DecidablePred event] (cut : ℕ)
    (hweight : ∀ x, 0 ≤ weight x)
    (hcut : ∀ x, event x → cut ≤ statistic x) :
    (∑ x, if event x then weight x else 0) ≤
      (∑ x, weight x * (2 : ℝ) ^ statistic x) / (2 : ℝ) ^ cut := by
  apply (le_div_iff₀' (by positivity : (0 : ℝ) < (2 : ℝ) ^ cut)).2
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x hx
  by_cases hevent : event x
  · rw [if_pos hevent]
    rw [mul_comm ((2 : ℝ) ^ cut) (weight x)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (hcut x hevent)) (hweight x)
  · simp [hevent, hweight x]

/-- A fixed-total thresholded failure forces the upper-shell occupancy past
the corrected cut. -/
theorem thresholdedGrowthCut_le_of_fixedTotalFailure
    {balanced : ℕ → Set Omega} {occupancy : Omega → ℕ → ℕ}
    {threshold : ℕ → ℕ} {G j total : ℕ} {omega : Omega}
    (h : omega ∈ fixedTotalThresholdedFailure balanced occupancy threshold
      G j total) :
    thresholdedGrowthCut threshold G j total ≤ occupancy omega (j + 1) := by
  simp only [fixedTotalThresholdedFailure, thresholdedGrowthFailure,
    pairTotalLevel, mem_inter_iff, mem_ofPred_eq] at h
  have hfailure := h.1.2
  have htotal := h.2
  apply max_le
  · omega
  · apply growthCut_le_of_ratio
    · omega
    · have hsub : total - occupancy omega (j + 1) = occupancy omega j := by
        omega
      rw [hsub]
      exact hfailure.2

/-- If the adjacent pair total is bounded on the thresholded failure event,
that event is exhausted by finitely many exact-total fibres. -/
theorem balanced_thresholdedGrowthFailure_subset_fixedTotals
    (balanced : ℕ → Set Omega) (occupancy : Omega → ℕ → ℕ)
    (threshold : ℕ → ℕ) (G j totalBound : ℕ)
    (hbound : ∀ omega,
      omega ∈ balanced j ∩ thresholdedGrowthFailure occupancy threshold G j →
        occupancy omega j + occupancy omega (j + 1) ≤ totalBound) :
    balanced j ∩ thresholdedGrowthFailure occupancy threshold G j ⊆
      ⋃ total ∈ Finset.range (totalBound + 1),
        fixedTotalThresholdedFailure balanced occupancy threshold G j total := by
  intro omega homega
  have htotal := hbound omega homega
  simp only [Set.mem_iUnion, Finset.mem_range]
  refine ⟨occupancy omega j + occupancy omega (j + 1), ?_, ?_⟩
  · omega
  · exact ⟨⟨homega.1, homega.2⟩, rfl⟩

/-- Sum exact conditional/product estimates over the genuinely random
adjacent-pair total.  This is the valid replacement for a single globally
fixed `pairTotal`. -/
theorem measureReal_balanced_thresholdedGrowthFailure_le_fixedTotalSum
    [MeasurableSpace Omega] (mu : Measure Omega) [IsFiniteMeasure mu]
    (balanced : ℕ → Set Omega) (occupancy : Omega → ℕ → ℕ)
    (threshold : ℕ → ℕ) (G j totalBound : ℕ)
    (hbound : ∀ omega,
      omega ∈ balanced j ∩ thresholdedGrowthFailure occupancy threshold G j →
        occupancy omega j + occupancy omega (j + 1) ≤ totalBound) :
    mu.real (balanced j ∩ thresholdedGrowthFailure occupancy threshold G j) ≤
      ∑ total ∈ Finset.range (totalBound + 1),
        mu.real (fixedTotalThresholdedFailure balanced occupancy threshold
          G j total) := by
  exact (measureReal_mono
    (balanced_thresholdedGrowthFailure_subset_fixedTotals balanced occupancy
      threshold G j totalBound hbound) (measure_ne_top _ _)).trans
    (measureReal_biUnion_finset_le (Finset.range (totalBound + 1)) _)

/-- Split a corrected interface cost into balancedness failure and the
thresholded product-law growth failure. -/
theorem measureReal_thresholdedInterfaceBad_le [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu] (balanced : ℕ → Set Omega)
    (occupancy : Omega → ℕ → ℕ) (threshold : ℕ → ℕ) (G j : ℕ) :
    mu.real (thresholdedInterfaceBad balanced occupancy threshold G j) ≤
      mu.real (balanced j)ᶜ +
        mu.real (balanced j ∩
          thresholdedGrowthFailure occupancy threshold G j) := by
  have hsubset : thresholdedInterfaceBad balanced occupancy threshold G j ⊆
      (balanced j)ᶜ ∪
        (balanced j ∩ thresholdedGrowthFailure occupancy threshold G j) := by
    intro omega homega
    rcases homega with hnot | hfail
    · exact Or.inl hnot
    · by_cases hbal : omega ∈ balanced j
      · exact Or.inr ⟨hbal, hfail⟩
      · exact Or.inl hbal
  exact (measureReal_mono hsubset).trans (measureReal_union_le _ _)

/-- Correct shell propagation with a genuinely random adjacent-pair total.

The `fixedCost j total` terms are estimates on the exact-total fibres.  Thus
this theorem never compares the whole interface event with a binomial law of
one postulated sample size.  In a capped stopped-product fibre `totalBound`
is supplied by the finite coordinate cutoffs, and `hfixed` is obtained by
conditioning on the displayed value of the adjacent-pair total. -/
theorem measureReal_totalOverflow_le_of_fixedTotalDecomposition
    [MeasurableSpace Omega] (mu : Measure Omega) [IsFiniteMeasure mu]
    (balanced : ℕ → Set Omega) (occupancy : Omega → ℕ → ℕ)
    (threshold : ℕ → ℕ) (G shellCount : ℕ)
    (totalBound : ℕ → ℕ)
    (hstep : ∀ j, j + 1 < shellCount →
      G * threshold j ≤ threshold (j + 1))
    (hpairBound : ∀ j < shellCount - 1, ∀ omega,
      omega ∈ balanced j ∩
          thresholdedGrowthFailure occupancy threshold G j →
        occupancy omega j + occupancy omega (j + 1) ≤ totalBound j)
    {baseCost : ℝ} {balanceCost : ℕ → ℝ}
    {fixedCost : ℕ → ℕ → ℝ}
    (hbase : mu.real (shellOverflow occupancy threshold 0) ≤ baseCost)
    (hbalance : ∀ j < shellCount - 1,
      mu.real (balanced j)ᶜ ≤ balanceCost j)
    (hfixed : ∀ j < shellCount - 1, ∀ total < totalBound j + 1,
      mu.real (fixedTotalThresholdedFailure balanced occupancy threshold
        G j total) ≤ fixedCost j total) :
    mu.real (totalOverflow occupancy threshold shellCount) ≤
      baseCost + ∑ j ∈ Finset.range (shellCount - 1),
        (balanceCost j +
          ∑ total ∈ Finset.range (totalBound j + 1), fixedCost j total) := by
  refine (measureReal_totalOverflow_le mu balanced occupancy threshold G
    shellCount hstep).trans ?_
  gcongr with j hj
  have hjlt : j < shellCount - 1 := Finset.mem_range.mp hj
  calc
    mu.real (thresholdedInterfaceBad balanced occupancy threshold G j) ≤
        mu.real (balanced j)ᶜ +
          mu.real (balanced j ∩
            thresholdedGrowthFailure occupancy threshold G j) :=
      measureReal_thresholdedInterfaceBad_le mu balanced occupancy threshold G j
    _ ≤ balanceCost j +
        ∑ total ∈ Finset.range (totalBound j + 1),
          mu.real (fixedTotalThresholdedFailure balanced occupancy threshold
            G j total) :=
      add_le_add (hbalance j hjlt)
        (measureReal_balanced_thresholdedGrowthFailure_le_fixedTotalSum
          mu balanced occupancy threshold G j (totalBound j)
            (hpairBound j hjlt))
    _ ≤ balanceCost j +
        ∑ total ∈ Finset.range (totalBound j + 1), fixedCost j total := by
      gcongr with total htotal
      exact hfixed j hjlt total (Finset.mem_range.mp htotal)

/-- Uniform-cost corollary of the random-total recurrence.  It is useful when
the exact-total urn estimate is independent of the realized total. -/
theorem measureReal_totalOverflow_le_of_fixedTotalUniformCost
    [MeasurableSpace Omega] (mu : Measure Omega) [IsFiniteMeasure mu]
    (balanced : ℕ → Set Omega) (occupancy : Omega → ℕ → ℕ)
    (threshold : ℕ → ℕ) (G shellCount : ℕ)
    (totalBound : ℕ → ℕ)
    (hstep : ∀ j, j + 1 < shellCount →
      G * threshold j ≤ threshold (j + 1))
    (hpairBound : ∀ j < shellCount - 1, ∀ omega,
      omega ∈ balanced j ∩
          thresholdedGrowthFailure occupancy threshold G j →
        occupancy omega j + occupancy omega (j + 1) ≤ totalBound j)
    {baseCost : ℝ} {balanceCost interfaceCost : ℕ → ℝ}
    (hbase : mu.real (shellOverflow occupancy threshold 0) ≤ baseCost)
    (hbalance : ∀ j < shellCount - 1,
      mu.real (balanced j)ᶜ ≤ balanceCost j)
    (hfixed : ∀ j < shellCount - 1, ∀ total < totalBound j + 1,
      mu.real (fixedTotalThresholdedFailure balanced occupancy threshold
        G j total) ≤ interfaceCost j) :
    mu.real (totalOverflow occupancy threshold shellCount) ≤
      baseCost + ∑ j ∈ Finset.range (shellCount - 1),
        (balanceCost j + (totalBound j + 1 : ℕ) * interfaceCost j) := by
  refine (measureReal_totalOverflow_le_of_fixedTotalDecomposition mu balanced
    occupancy threshold G shellCount totalBound hstep hpairBound hbase
    hbalance hfixed).trans ?_
  gcongr with j hj
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end Erdos1165.NearFavoriteThresholded
