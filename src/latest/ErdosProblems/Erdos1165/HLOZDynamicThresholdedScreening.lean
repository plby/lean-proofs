/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/

import ErdosProblems.Erdos1165.HLOZProposition48Thresholded

/-!
# Thresholded shell screening at a path-dependent stopping cutoff

The physical creation time must remain random in the insertion product law.
This module therefore states Proposition 4.8 for an arbitrary random finite
visited set and arbitrary one-site large events. A path-dependent creation
time is represented by substituting its stopped external range and stopped
external-local-time event for these two arguments.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZDynamicThresholdedScreening

open ExternalThickCount HLOZProposition48Candidates
open HLOZThresholdedShellScreening NearFavoriteShells NearFavoriteThresholded
open ScreeningInstantiation

noncomputable section

/-- External-thick candidates for a random stopped external range. -/
noncomputable def dynamicThickCandidates
    (visited : WalkPath → Finset Point) (large : Point → Set WalkPath)
    (distinguished : WalkPath → Finset Point) (s : WalkPath) : Finset Point :=
  by
    classical
    exact (visited s).filter fun x ↦ s ∈ large x ∧ x ∉ distinguished s

/-- Deficit-shell occupancy of the random-cutoff candidates. -/
noncomputable def dynamicShellOccupancy
    (visited : WalkPath → Finset Point) (large : Point → Set WalkPath)
    (distinguished : WalkPath → Finset Point)
    (totalLocalTime : WalkPath → Point → ℕ) (m width : ℕ)
    (s : WalkPath) (j : ℕ) : ℕ :=
  shellOccupancy (dynamicThickCandidates visited large distinguished s)
    (deficitShellLabel totalLocalTime m width s) j

theorem dynamicThickCandidates_card_le_candidateCount
    (visited : WalkPath → Finset Point) (large : Point → Set WalkPath)
    (distinguished : WalkPath → Finset Point) (s : WalkPath) :
    (dynamicThickCandidates visited large distinguished s).card ≤
      candidateCount visited large s := by
  classical
  unfold dynamicThickCandidates candidateCount
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hx.2.1⟩

theorem dynamicShellOccupancy_le_candidateCount
    (visited : WalkPath → Finset Point) (large : Point → Set WalkPath)
    (distinguished : WalkPath → Finset Point)
    (totalLocalTime : WalkPath → Point → ℕ) (m width : ℕ)
    (s : WalkPath) (j : ℕ) :
    dynamicShellOccupancy visited large distinguished totalLocalTime
        m width s j ≤ candidateCount visited large s := by
  classical
  calc
    dynamicShellOccupancy visited large distinguished totalLocalTime
        m width s j ≤
        (dynamicThickCandidates visited large distinguished s).card := by
      unfold dynamicShellOccupancy shellOccupancy shellCandidates Screening.shell
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ candidateCount visited large s :=
      dynamicThickCandidates_card_le_candidateCount visited large distinguished s

theorem dynamicShellOverflow_zero_subset_candidateCount
    (visited : WalkPath → Finset Point) (large : Point → Set WalkPath)
    (distinguished : WalkPath → Finset Point)
    (totalLocalTime : WalkPath → Point → ℕ)
    (m width J G : ℕ) :
    shellOverflow
        (dynamicShellOccupancy visited large distinguished totalLocalTime
          m width)
        (geometricShellThreshold J G) 0 ⊆
      {s | J < candidateCount visited large s} := by
  intro s hs
  change geometricShellThreshold J G 0 <
    dynamicShellOccupancy visited large distinguished totalLocalTime
      m width s 0 at hs
  change J < candidateCount visited large s
  have hs' : J < dynamicShellOccupancy visited large distinguished
      totalLocalTime m width s 0 := by
    simpa using hs
  exact hs'.trans_le
    (dynamicShellOccupancy_le_candidateCount visited large distinguished
      totalLocalTime m width s 0)

/-- The Tonelli--Markov first-shell estimate at a random cutoff. -/
theorem simpleRandomWalk_dynamicShellOverflow_zero_le
    (visited : WalkPath → Finset Point) (large : Point → Set WalkPath)
    (distinguished : WalkPath → Finset Point)
    (totalLocalTime : WalkPath → Point → ℕ)
    (m width J G : ℕ) (q R : ℝ≥0∞) (hJ : 0 < J)
    (hvisited : ∀ x, MeasurableSet (memberEvent visited x))
    (hlarge : ∀ x, MeasurableSet (large x))
    (hweightedOneSite : ∀ x,
      simpleRandomWalk (candidateEvent visited large x) ≤
        q * simpleRandomWalk (memberEvent visited x))
    (hvisitExpectation :
      ∫⁻ s, ((visited s).card : ℝ≥0∞) ∂simpleRandomWalk ≤ R) :
    simpleRandomWalk
        (shellOverflow
          (dynamicShellOccupancy visited large distinguished totalLocalTime
            m width)
          (geometricShellThreshold J G) 0) ≤
      q * R / J := by
  exact (measure_mono
    (dynamicShellOverflow_zero_subset_candidateCount visited large
      distinguished totalLocalTime m width J G)).trans
    (measure_candidateCount_gt_le simpleRandomWalk visited large q R J hJ
      hvisited hlarge hweightedOneSite hvisitExpectation)

theorem simpleRandomWalk_real_dynamicShellOverflow_zero_le
    (visited : WalkPath → Finset Point) (large : Point → Set WalkPath)
    (distinguished : WalkPath → Finset Point)
    (totalLocalTime : WalkPath → Point → ℕ)
    (m width J G : ℕ) (q R : ℝ≥0∞) (hJ : 0 < J)
    (hq : q ≠ ∞) (hR : R ≠ ∞)
    (hvisited : ∀ x, MeasurableSet (memberEvent visited x))
    (hlarge : ∀ x, MeasurableSet (large x))
    (hweightedOneSite : ∀ x,
      simpleRandomWalk (candidateEvent visited large x) ≤
        q * simpleRandomWalk (memberEvent visited x))
    (hvisitExpectation :
      ∫⁻ s, ((visited s).card : ℝ≥0∞) ∂simpleRandomWalk ≤ R) :
    simpleRandomWalk.real
        (shellOverflow
          (dynamicShellOccupancy visited large distinguished totalLocalTime
            m width)
          (geometricShellThreshold J G) 0) ≤
      (q * R / J).toReal := by
  apply (ENNReal.toReal_le_toReal (by finiteness) ?_).2
  · exact simpleRandomWalk_dynamicShellOverflow_zero_le visited large
      distinguished totalLocalTime m width J G q R hJ hvisited hlarge
      hweightedOneSite hvisitExpectation
  · have hJ0 : (J : ℝ≥0∞) ≠ 0 := by simp [hJ.ne']
    exact ENNReal.div_ne_top (ENNReal.mul_ne_top hq hR) hJ0

/-- Correct random-total shell recurrence at a path-dependent cutoff. -/
theorem simpleRandomWalk_dynamicShell_totalOverflow_le_thresholded
    {Site : Type*}
    (visited : WalkPath → Finset Point) (large : Point → Set WalkPath)
    (distinguished : WalkPath → Finset Point)
    (totalLocalTime : WalkPath → Point → ℕ)
    (m width J G shellCount : ℕ)
    (balanced : ℕ → Set WalkPath)
    (q R : ℝ≥0∞) (hJ : 0 < J) (hq : q ≠ ∞) (hR : R ≠ ∞)
    (hvisited : ∀ x, MeasurableSet (memberEvent visited x))
    (hlarge : ∀ x, MeasurableSet (large x))
    (hweightedOneSite : ∀ x,
      simpleRandomWalk (candidateEvent visited large x) ≤
        q * simpleRandomWalk (memberEvent visited x))
    (hvisitExpectation :
      ∫⁻ s, ((visited s).card : ℝ≥0∞) ∂simpleRandomWalk ≤ R)
    (balanceLaw : ∀ j,
      GeometricBalanceLaw (Site := Site) simpleRandomWalk (balanced j) m)
    (productLaw : RandomTotalProductLaw simpleRandomWalk balanced
      (dynamicShellOccupancy visited large distinguished totalLocalTime m width)
      (geometricShellThreshold J G) G shellCount) :
    simpleRandomWalk.real
        (totalOverflow
          (dynamicShellOccupancy visited large distinguished totalLocalTime
            m width)
          (geometricShellThreshold J G) shellCount) ≤
      (q * R / J).toReal +
        ∑ j ∈ Finset.range (shellCount - 1),
          ((((balanceLaw j).budget : ℝ≥0∞) *
              (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
                ENNReal.ofReal
                  (Real.exp (-17 * balanceRateScale m)))).toReal +
            ∑ total ∈ Finset.range (productLaw.totalBound j + 1),
              productLaw.fixedCost j total) := by
  have hstep : ∀ j, j + 1 < shellCount →
      G * geometricShellThreshold J G j ≤
        geometricShellThreshold J G (j + 1) := by
    intro j _
    exact (geometricShellThreshold_step J G j).le
  apply measureReal_totalOverflow_le_of_geometricBalance_and_randomTotalProduct
    simpleRandomWalk balanced
      (dynamicShellOccupancy visited large distinguished totalLocalTime m width)
      (geometricShellThreshold J G) G shellCount m hstep balanceLaw productLaw
  exact simpleRandomWalk_real_dynamicShellOverflow_zero_le visited large
    distinguished totalLocalTime m width J G q R hJ hq hR hvisited hlarge
    hweightedOneSite hvisitExpectation

/-! ## Dynamic Proposition 4.8 candidates -/

noncomputable def dynamicStoppedCandidateSites48
    (visited : WalkPath → Finset Point) (large : Point → Set WalkPath)
    (distinguished : WalkPath → Finset Point)
    (totalLocalTime : WalkPath → Point → ℕ)
    (m : ℕ) (beta : ℝ) (s : WalkPath) : Finset Point :=
  boundedCandidates (dynamicThickCandidates visited large distinguished s)
    (deficitShellLabel totalLocalTime m (shellWidth48 m) s)
    (shellCount48 m beta)

theorem card_dynamicStoppedCandidateSites48
    (visited : WalkPath → Finset Point) (large : Point → Set WalkPath)
    (distinguished : WalkPath → Finset Point)
    (totalLocalTime : WalkPath → Point → ℕ)
    (m : ℕ) (beta : ℝ) (s : WalkPath) :
    (dynamicStoppedCandidateSites48 visited large distinguished
      totalLocalTime m beta s).card =
      ∑ j ∈ Finset.range (shellCount48 m beta),
        dynamicShellOccupancy visited large distinguished totalLocalTime
          m (shellWidth48 m) s j := by
  rw [dynamicStoppedCandidateSites48,
    ← sum_shellOccupancy_eq_card_boundedCandidates]
  rfl

def dynamicStoppedCandidateOverflow48
    (visited : WalkPath → Finset Point) (large : Point → Set WalkPath)
    (distinguished : WalkPath → Finset Point)
    (totalLocalTime : WalkPath → Point → ℕ)
    (m : ℕ) (beta : ℝ) : Set WalkPath :=
  {s | candidateBudget48 m beta <
    (dynamicStoppedCandidateSites48 visited large distinguished
      totalLocalTime m beta s).card}

theorem dynamicStoppedCandidateOverflow48_subset_totalOverflow
    (visited : WalkPath → Finset Point) (large : Point → Set WalkPath)
    (distinguished : WalkPath → Finset Point)
    (totalLocalTime : WalkPath → Point → ℕ)
    (m : ℕ) (beta : ℝ)
    (hbudget : geometricCandidateBudget48 m beta ≤
      candidateBudget48 m beta) :
    dynamicStoppedCandidateOverflow48 visited large distinguished
        totalLocalTime m beta ⊆
      totalOverflow
        (dynamicShellOccupancy visited large distinguished totalLocalTime
          m (shellWidth48 m))
        (geometricShellThreshold (initialBudget48 m) shellGrowth48)
        (shellCount48 m beta) := by
  intro s hs
  change candidateBudget48 m beta <
    (dynamicStoppedCandidateSites48 visited large distinguished
      totalLocalTime m beta s).card at hs
  change geometricCandidateBudget48 m beta <
    ∑ j ∈ Finset.range (shellCount48 m beta),
      dynamicShellOccupancy visited large distinguished totalLocalTime
        m (shellWidth48 m) s j
  rw [← card_dynamicStoppedCandidateSites48]
  exact hbudget.trans_lt hs

/-- Correct dynamic-cutoff Proposition 4.8 bound. -/
theorem simpleRandomWalk_dynamicStoppedCandidateOverflow48_le_thresholded
    {Site : Type*}
    (visited : WalkPath → Finset Point) (large : Point → Set WalkPath)
    (distinguished : WalkPath → Finset Point)
    (totalLocalTime : WalkPath → Point → ℕ)
    (m : ℕ) (beta : ℝ) (balanced : ℕ → Set WalkPath)
    (q R : ℝ≥0∞) (hq : q ≠ ∞) (hR : R ≠ ∞)
    (hbudget : geometricCandidateBudget48 m beta ≤
      candidateBudget48 m beta)
    (hvisited : ∀ x, MeasurableSet (memberEvent visited x))
    (hlarge : ∀ x, MeasurableSet (large x))
    (hweightedOneSite : ∀ x,
      simpleRandomWalk (candidateEvent visited large x) ≤
        q * simpleRandomWalk (memberEvent visited x))
    (hvisitExpectation :
      ∫⁻ s, ((visited s).card : ℝ≥0∞) ∂simpleRandomWalk ≤ R)
    (balanceLaw : ∀ j,
      GeometricBalanceLaw (Site := Site) simpleRandomWalk (balanced j) m)
    (productLaw : RandomTotalProductLaw simpleRandomWalk balanced
      (dynamicShellOccupancy visited large distinguished totalLocalTime
        m (shellWidth48 m))
      (geometricShellThreshold (initialBudget48 m) shellGrowth48)
      shellGrowth48 (shellCount48 m beta)) :
    simpleRandomWalk
        (dynamicStoppedCandidateOverflow48 visited large distinguished
          totalLocalTime m beta) ≤
      ENNReal.ofReal
        ((q * R / initialBudget48 m).toReal +
          ∑ j ∈ Finset.range (shellCount48 m beta - 1),
            ((((balanceLaw j).budget : ℝ≥0∞) *
                (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
                  ENNReal.ofReal
                    (Real.exp (-17 * balanceRateScale m)))).toReal +
              ∑ total ∈ Finset.range (productLaw.totalBound j + 1),
                productLaw.fixedCost j total)) := by
  have hreal := (measureReal_mono
      (dynamicStoppedCandidateOverflow48_subset_totalOverflow visited large
        distinguished totalLocalTime m beta hbudget)).trans
    (simpleRandomWalk_dynamicShell_totalOverflow_le_thresholded visited large
      distinguished totalLocalTime m (shellWidth48 m) (initialBudget48 m)
      shellGrowth48 (shellCount48 m beta) balanced q R
      (by unfold initialBudget48; omega) hq hR hvisited hlarge hweightedOneSite
      hvisitExpectation balanceLaw productLaw)
  rw [← ENNReal.ofReal_toReal (show
    simpleRandomWalk
        (dynamicStoppedCandidateOverflow48 visited large distinguished
          totalLocalTime m beta) ≠ ∞ by finiteness)]
  exact ENNReal.ofReal_mono hreal

end

end Erdos1165.HLOZDynamicThresholdedScreening
