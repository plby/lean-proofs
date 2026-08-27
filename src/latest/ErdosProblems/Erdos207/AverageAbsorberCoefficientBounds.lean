/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AbsorberCoefficientBounds
import ErdosProblems.Erdos207.LinearAverageAbsorberPhase

/-!
# Scalar coefficient bounds for the averaged absorber phase

The aggregate-incidence event introduces one additional A2 expression.  This
file bounds it by the same advertised absorber support and bank-size data as
the two maximum-cutoff events, and packages a completely scalar five-term
failure bound.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Scalar upper bound for the aggregate two-away first moment. -/
def totalTwoAwayExpectationUpper
    (q M c b n : ℕ) : ℝ≥0 :=
  ((n ^ 3 : ℕ) : ℝ≥0) *
    ((twoAwayMomentJointConstant q 1 : ℝ≥0) *
      ((2 : ℝ≥0) ^ twoAwayMomentUnionCutoff q 1 *
        globalTwoAwayCoefficientUpper q M c b n))

/-- Five-term scalar failure expression for the averaged padded phase. -/
def paddedAveragePhaseFailureUpper
    (q M c b n phaseSteps sPair sGlobal Kpair Kglobal I : ℕ)
    (thetaPair aPair vPair thetaAvail aAvail vAvail : ℝ) : ℝ :=
  ((n ^ 2 : ℕ) : ℝ) *
      (2 * Real.exp
        (-thetaPair * aPair +
          thetaPair ^ 2 * (phaseSteps : ℝ) * vPair)) +
    ((((n ^ 3 : ℕ) : ℝ≥0) * ((n ^ 2 : ℕ) : ℝ≥0) *
      pairTwoAwayTail q sPair Kpair
        (pairTwoAwayCoefficientUpper q b : ℕ) : ℝ≥0) : ℝ) +
    ((((n ^ 3 : ℕ) : ℝ≥0) *
      globalTwoAwayTailUpper q M c b n sGlobal Kglobal : ℝ≥0) : ℝ) +
    ((totalTwoAwayExpectationUpper q M c b n /
      ((I + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) +
    Real.exp
      (-thetaAvail * aAvail +
        thetaAvail ^ 2 * (phaseSteps : ℝ) * vAvail)

theorem totalTwoAwayExpectationEnvelope_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M c b n : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B : TripleSystemOn V}
    (hn : Fintype.card V = n)
    (hH : (graphSupportFinset H).card ≤ c) (hB : B.card ≤ b) :
    totalTwoAwayExpectationEnvelope q M H X B ≤
      totalTwoAwayExpectationUpper q M c b n := by
  have htripleNat : Fintype.card (TripleOn V) ≤ n ^ 3 := by
    simpa only [hn] using card_tripleOn_le_cube V
  have htripleNN : (Fintype.card (TripleOn V) : ℝ≥0) ≤
      ((n ^ 3 : ℕ) : ℝ≥0) := by
    exact_mod_cast htripleNat
  unfold totalTwoAwayExpectationEnvelope totalTwoAwayExpectationUpper
  gcongr
  have hc := twoAwayThreatExtensionCoefficient_le
    (q := q) (M := M) (c := c) (b := b)
      (H := H) (X := X) (B := B) hH hB
  rw [hn] at hc
  exact_mod_cast hc

/-- The absorber-specific five-event expression is bounded by its scalar
counterpart. -/
theorem averagedAbsorberPhaseFailure_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M c b n phaseSteps sPair sGlobal Kpair Kglobal I : ℕ}
    {H : SimpleGraph V} {X : Finset V} {B : TripleSystemOn V}
    (thetaPair aPair vPair thetaAvail aAvail vAvail : ℝ)
    (hn : Fintype.card V = n)
    (hH : (graphSupportFinset H).card ≤ c) (hB : B.card ≤ b) :
    averagedAbsorberPhaseFailure q M phaseSteps sPair sGlobal
        Kpair Kglobal I H X B thetaPair aPair vPair
          thetaAvail aAvail vAvail ≤
      paddedAveragePhaseFailureUpper q M c b n phaseSteps
        sPair sGlobal Kpair Kglobal I thetaPair aPair vPair
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
  unfold averagedAbsorberPhaseFailure paddedAveragePhaseFailureUpper
  apply add_le_add
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
        totalTwoAwayExpectationEnvelope q M H X B /
              ((I + 1 : ℕ) : ℝ≥0) ≤
            totalTwoAwayExpectationUpper q M c b n /
              ((I + 1 : ℕ) : ℝ≥0) by
        gcongr
        exact totalTwoAwayExpectationEnvelope_le hn hH hB)
  · exact le_refl _

end

end Erdos207
