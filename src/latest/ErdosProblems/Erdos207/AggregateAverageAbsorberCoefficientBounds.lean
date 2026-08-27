/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AverageAbsorberCoefficientBounds
import ErdosProblems.Erdos207.LinearAggregateAverageAbsorberPhase

/-! # Scalar bounds for the six-event averaged phase -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Ambient-independent bound for the aggregate pair-star coefficient. -/
def aggregatePairTwoAwayCoefficientUpper (q b : ℕ) : ℕ :=
  (q + 1) * q * pairExactBankCoefficientUpper q b

theorem aggregatePairTwoAwayThreatExtensionCoefficient_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q b : ℕ} {B : TripleSystemOn V} (hB : B.card ≤ b) :
    aggregatePairTwoAwayThreatExtensionCoefficient q B ≤
      aggregatePairTwoAwayCoefficientUpper q b := by
  have hsingle : ∀ j : IndexedThreatOrder q,
      aggregatePairExactBankExtensionCoefficient q j.1 B ≤
        q * pairExactBankCoefficientUpper q b := by
    intro j
    have hjq : j.1 ≤ q := (mem_Icc.mp j.2).2
    unfold aggregatePairExactBankExtensionCoefficient
    calc
      (∑ r : (Icc 5 q : Finset ℕ), ∑ _K : subsetsUpToCard B q,
          (j.1 - 2) * (2 ^ (r.1 ^ 3) * (r.1 + 1))) ≤
        ∑ r : (Icc 5 q : Finset ℕ), ∑ _K : subsetsUpToCard B q,
          q * (2 ^ (r.1 ^ 3) * (r.1 + 1)) := by
            apply sum_le_sum
            intro r _hr
            apply sum_le_sum
            intro K _hK
            gcongr
            omega
      _ = q * pairExactBankExtensionCoefficient q B := by
        unfold pairExactBankExtensionCoefficient
        rw [mul_sum]
        apply sum_congr rfl
        intro r _hr
        rw [mul_sum]
      _ ≤ q * pairExactBankCoefficientUpper q b :=
        Nat.mul_le_mul_left q (pairExactBankExtensionCoefficient_le hB)
  unfold aggregatePairTwoAwayThreatExtensionCoefficient
  calc
    (∑ j : IndexedThreatOrder q,
        aggregatePairExactBankExtensionCoefficient q j.1 B) ≤
      ∑ _j : IndexedThreatOrder q,
        q * pairExactBankCoefficientUpper q b := by
          apply sum_le_sum
          intro j _hj
          exact hsingle j
    _ = Fintype.card (IndexedThreatOrder q) *
        (q * pairExactBankCoefficientUpper q b) := by simp
    _ ≤ (q + 1) * (q * pairExactBankCoefficientUpper q b) := by
      gcongr
      exact card_indexedThreatOrder_le q
    _ = aggregatePairTwoAwayCoefficientUpper q b := by
      simp [aggregatePairTwoAwayCoefficientUpper, mul_assoc]

/-- Scalar six-event failure expression for a padded absorber. -/
def paddedAggregateAveragePhaseFailureUpper
    (q M c b n phaseSteps sPair sGlobal sInc Kpair Kglobal Kinc I : ℕ)
    (thetaPair aPair vPair thetaAvail aAvail vAvail : ℝ) : ℝ :=
  ((n ^ 2 : ℕ) : ℝ) *
      (2 * Real.exp
        (-thetaPair * aPair + thetaPair ^ 2 * (phaseSteps : ℝ) * vPair)) +
    ((((n ^ 3 : ℕ) : ℝ≥0) * ((n ^ 2 : ℕ) : ℝ≥0) *
      pairTwoAwayTail q sPair Kpair
        (pairTwoAwayCoefficientUpper q b : ℕ) : ℝ≥0) : ℝ) +
    ((((n ^ 3 : ℕ) : ℝ≥0) *
      globalTwoAwayTailUpper q M c b n sGlobal Kglobal : ℝ≥0) : ℝ) +
    ((((n ^ 2 : ℕ) : ℝ≥0) *
      aggregatePairTwoAwayTail q sInc Kinc
        ((aggregatePairTwoAwayCoefficientUpper q b : ℕ) *
          (n + 1 : ℝ≥0) ^ 2) : ℝ≥0) : ℝ) +
    ((totalTwoAwayExpectationUpper q M c b n /
      ((I + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) +
    Real.exp
      (-thetaAvail * aAvail + thetaAvail ^ 2 * (phaseSteps : ℝ) * vAvail)

theorem aggregateAveragedAbsorberPhaseFailure_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M c b n phaseSteps sPair sGlobal sInc Kpair Kglobal Kinc I : ℕ}
    {H : SimpleGraph V} {X : Finset V} {B : TripleSystemOn V}
    (thetaPair aPair vPair thetaAvail aAvail vAvail : ℝ)
    (hn : Fintype.card V = n)
    (hH : (graphSupportFinset H).card ≤ c) (hB : B.card ≤ b) :
    aggregateAveragedAbsorberPhaseFailure q M phaseSteps sPair sGlobal sInc
        Kpair Kglobal Kinc I H X B thetaPair aPair vPair
          thetaAvail aAvail vAvail ≤
      paddedAggregateAveragePhaseFailureUpper q M c b n phaseSteps
        sPair sGlobal sInc Kpair Kglobal Kinc I thetaPair aPair vPair
          thetaAvail aAvail vAvail := by
  have hpairNat : Fintype.card (PairOn V) ≤ n ^ 2 := by
    simpa only [hn] using card_pairOn_le_sq V
  have htripleNat : Fintype.card (TripleOn V) ≤ n ^ 3 := by
    simpa only [hn] using card_tripleOn_le_cube V
  have hpairReal : (Fintype.card (PairOn V) : ℝ) ≤
      ((n ^ 2 : ℕ) : ℝ) := by exact_mod_cast hpairNat
  have hpairNN : (Fintype.card (PairOn V) : ℝ≥0) ≤
      ((n ^ 2 : ℕ) : ℝ≥0) := by exact_mod_cast hpairNat
  have htripleNN : (Fintype.card (TripleOn V) : ℝ≥0) ≤
      ((n ^ 3 : ℕ) : ℝ≥0) := by exact_mod_cast htripleNat
  have haggCoeff :
      ((aggregatePairTwoAwayThreatExtensionCoefficient q B : ℕ) : ℝ≥0) ≤
        (aggregatePairTwoAwayCoefficientUpper q b : ℕ) := by
    exact_mod_cast aggregatePairTwoAwayThreatExtensionCoefficient_le hB
  have hkappa :
      ((aggregatePairTwoAwayThreatExtensionCoefficient q B : ℕ) : ℝ≥0) *
          (Fintype.card V + 1 : ℝ≥0) ^ 2 ≤
        (aggregatePairTwoAwayCoefficientUpper q b : ℕ) *
          (n + 1 : ℝ≥0) ^ 2 := by
    rw [hn]
    gcongr
  have haggregateTail :
      aggregatePairTwoAwayTail q sInc Kinc
          ((aggregatePairTwoAwayThreatExtensionCoefficient q B : ℕ) *
            (Fintype.card V + 1 : ℝ≥0) ^ 2) ≤
        aggregatePairTwoAwayTail q sInc Kinc
          ((aggregatePairTwoAwayCoefficientUpper q b : ℕ) *
            (n + 1 : ℝ≥0) ^ 2) := by
    unfold aggregatePairTwoAwayTail
    gcongr
  unfold aggregateAveragedAbsorberPhaseFailure
    paddedAggregateAveragePhaseFailureUpper
  apply add_le_add
  · apply add_le_add
    · apply add_le_add
      · apply add_le_add
        · apply add_le_add
          · gcongr
          · exact_mod_cast (show
              (Fintype.card (TripleOn V) : ℝ≥0) *
                  (Fintype.card (PairOn V) : ℝ≥0) *
                  pairTwoAwayTail q sPair Kpair
                    (pairTwoAwayThreatExtensionCoefficient q B : ℕ) ≤
                ((n ^ 3 : ℕ) : ℝ≥0) * ((n ^ 2 : ℕ) : ℝ≥0) *
                  pairTwoAwayTail q sPair Kpair
                    (pairTwoAwayCoefficientUpper q b : ℕ) by
              gcongr
              exact pairTwoAwayTail_le hB)
        · exact_mod_cast (show
            (Fintype.card (TripleOn V) : ℝ≥0) *
                envelopeTwoAwayTail q M sGlobal H X B Kglobal ≤
              ((n ^ 3 : ℕ) : ℝ≥0) *
                globalTwoAwayTailUpper q M c b n sGlobal Kglobal by
            gcongr
            simpa only [hn] using envelopeTwoAwayTail_le hH hB)
      · exact_mod_cast (show
          (Fintype.card (PairOn V) : ℝ≥0) *
              aggregatePairTwoAwayTail q sInc Kinc
                ((aggregatePairTwoAwayThreatExtensionCoefficient q B : ℕ) *
                  (Fintype.card V + 1 : ℝ≥0) ^ 2) ≤
            ((n ^ 2 : ℕ) : ℝ≥0) *
              aggregatePairTwoAwayTail q sInc Kinc
                ((aggregatePairTwoAwayCoefficientUpper q b : ℕ) *
                  (n + 1 : ℝ≥0) ^ 2) by
          exact mul_le_mul hpairNN haggregateTail (by positivity) (by positivity))
    · exact_mod_cast (show
        totalTwoAwayExpectationEnvelope q M H X B /
              ((I + 1 : ℕ) : ℝ≥0) ≤
            totalTwoAwayExpectationUpper q M c b n /
              ((I + 1 : ℕ) : ℝ≥0) by
        gcongr
        exact totalTwoAwayExpectationEnvelope_le hn hH hB)
  · exact le_refl _

end

end Erdos207
