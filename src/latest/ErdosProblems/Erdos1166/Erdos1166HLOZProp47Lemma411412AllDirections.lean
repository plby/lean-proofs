/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1166.Erdos1166HLOZColumnSourceConsumers
import ErdosProblems.Erdos1166.Erdos1166HLOZProp47Lemma411412XDirections

/-!
# All-six source assembly for HLOZ Lemmas 4.11--4.12

The four checkerboard pairings are transported from the literal X-east
four-branch source data.  The two column pairings are supplied by the two
literal Y terminal phases, padded to the same four-branch arity, and then
reflected only after the two phases have been reunited.  Finiteness of the
six pairing indices intersects the six eventual scale filters.
-/

namespace Erdos1166.HLOZProp47Lemma411412AllDirections

open HLOZPairing
open HLOZProp47Lemma411412Connector
open HLOZProp47Lemma411412XEastBridge
open HLOZProp47Lemma411412XDirections
open HLOZColumnSourceConsumers
open HLOZBandRatios

/-- Literal X-east and two-phase Y source packages provide the complete
four-branch atomization for all six pairing indices.  At `Y'` the reflected
stopped-atom profile exception is retained as an auxiliary theta target;
its probability is paid separately rather than hidden behind a false event
inclusion. -/
theorem finiteBranchAuxThetaInputs_of_xEast_y_source
    (cWindow : ℕ) (rhoCoeff : ℝ)
    (hX : Prop47Lemma411412XEastFourBranchSourceInputs
      cWindow rhoCoeff)
    (hY : Prop47Lemma411412YTwoPhaseSourceInputs
      cWindow rhoCoeff) :
    Prop47Lemma411412FiniteBranchAuxThetaInputs
      sourceEquation447ThetaTarget 4 cWindow
        (Real.exp (sourceAdjacentComparisonExponent cWindow)) rhoCoeff := by
  apply finiteBranchAuxThetaInputs_of_allAt
    sourceEquation447ThetaTarget
  intro i
  fin_cases i
  · apply finiteBranchAuxThetaInputsAt_of_standard
    · intro m r
      simp [sourceEquation447ThetaTarget, yIndex']
    · convert finiteBranchStoppedProfileInputsAt_x_of_source
        (0 : Dir) cWindow rhoCoeff hX using 1 <;>
        ext <;> norm_num [xIndex]
  · apply finiteBranchAuxThetaInputsAt_of_standard
    · intro m r
      simp [sourceEquation447ThetaTarget, yIndex']
    · convert finiteBranchStoppedProfileInputsAt_x_of_source
        (1 : Dir) cWindow rhoCoeff hX using 1 <;>
        ext <;> norm_num [xIndex]
  · apply finiteBranchAuxThetaInputsAt_of_standard
    · intro m r
      simp [sourceEquation447ThetaTarget, yIndex']
    · convert finiteBranchStoppedProfileInputsAt_x_of_source
        (2 : Dir) cWindow rhoCoeff hX using 1 <;>
        ext <;> norm_num [xIndex]
  · apply finiteBranchAuxThetaInputsAt_of_standard
    · intro m r
      simp [sourceEquation447ThetaTarget, yIndex']
    · convert finiteBranchStoppedProfileInputsAt_x_of_source
        (3 : Dir) cWindow rhoCoeff hX using 1 <;>
        ext <;> norm_num [xIndex]
  · apply finiteBranchAuxThetaInputsAt_of_standard
    · exact sourceEquation447ThetaTarget_y
    · convert finiteBranchStoppedProfileInputsAt_four_of_two
        yIndex cWindow
          (Real.exp (sourceAdjacentComparisonExponent cWindow)) rhoCoeff
          (finiteBranchStoppedProfileInputsAt_y_of_source cWindow
            rhoCoeff hY) using 1 <;>
        ext <;> norm_num [yIndex]
  · convert finiteBranchAuxThetaInputsAt_four_of_two
      sourceEquation447ThetaTarget yIndex' cWindow
        (Real.exp (sourceAdjacentComparisonExponent cWindow)) rhoCoeff
        (finiteBranchAuxThetaInputsAt_yPrime_of_source cWindow
          rhoCoeff hY) using 1 <;>
      ext <;> norm_num [yIndex']

/-- Source-faithful all-six assembly for the actual deleted-path switch at
(4.47).  Four X pairings are quarter-turns of the literal X-east package;
the two terminal column phases are padded to four branches and reflected
only after reunion.  The reflected temporal exception is kept in the
auxiliary theta target and paid separately. -/
theorem finiteBranchPathWitnessAuxThetaInputs_of_xEast_y_source
    (cWindow : ℕ) (c : ℝ)
    (hX : Prop47Lemma411412XEastCanonicalFourBranchPathWitnessSourceInputs
      cWindow c)
    (hY : Prop47Lemma411412YCanonicalTwoPhasePathWitnessSourceInputs
      cWindow c) :
    Prop47Lemma411412FiniteBranchPathWitnessAuxThetaInputs
      sourceEquation447ThetaTarget 4 cWindow c (1 / 4 : ℝ) := by
  apply finiteBranchPathWitnessAuxThetaInputs_of_allAt
    sourceEquation447ThetaTarget
  intro i
  fin_cases i
  · apply finiteBranchPathWitnessAuxThetaInputsAt_of_standard
    · intro m r
      simp [sourceEquation447ThetaTarget, yIndex']
    · convert finiteBranchPathWitnessInputsAt_x_of_source
        (0 : Dir) cWindow c hX using 1 <;>
        ext <;> norm_num [xIndex]
  · apply finiteBranchPathWitnessAuxThetaInputsAt_of_standard
    · intro m r
      simp [sourceEquation447ThetaTarget, yIndex']
    · convert finiteBranchPathWitnessInputsAt_x_of_source
        (1 : Dir) cWindow c hX using 1 <;>
        ext <;> norm_num [xIndex]
  · apply finiteBranchPathWitnessAuxThetaInputsAt_of_standard
    · intro m r
      simp [sourceEquation447ThetaTarget, yIndex']
    · convert finiteBranchPathWitnessInputsAt_x_of_source
        (2 : Dir) cWindow c hX using 1 <;>
        ext <;> norm_num [xIndex]
  · apply finiteBranchPathWitnessAuxThetaInputsAt_of_standard
    · intro m r
      simp [sourceEquation447ThetaTarget, yIndex']
    · convert finiteBranchPathWitnessInputsAt_x_of_source
        (3 : Dir) cWindow c hX using 1 <;>
        ext <;> norm_num [xIndex]
  · apply finiteBranchPathWitnessAuxThetaInputsAt_of_standard
    · exact sourceEquation447ThetaTarget_y
    · convert finiteBranchPathWitnessInputsAt_four_of_two
        yIndex cWindow c (1 / 4 : ℝ)
          (finiteBranchPathWitnessInputsAt_y_of_source cWindow c hY) using 1 <;>
        ext <;> norm_num [yIndex]
  · convert finiteBranchPathWitnessAuxThetaInputsAt_four_of_two
      sourceEquation447ThetaTarget yIndex' cWindow c (1 / 4 : ℝ)
        (finiteBranchPathWitnessAuxThetaInputsAt_yPrime_of_source
          cWindow c hY) using 1 <;>
      ext <;> norm_num [yIndex']

end Erdos1166.HLOZProp47Lemma411412AllDirections
