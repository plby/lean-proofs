import Wikipedia.HopfProblem.CuspNormalizationSheafLocalCoordinates
import Wikipedia.HopfProblem.CuspNormalizationSheafGermComplexAxesTables

/-!
# Analytic-germ identities for the source-oriented branch pairs

The positive and negative branch lifts meet along the same actual coordinate
axis. These identities rewrite their analytic-germ restrictions and extensions
using the source-oriented coordinate tables, for both triangle orientations.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspQuotient.NormalizationLocalCoordinates

open ToricFan Triangle NormalizationCurves
open CuspNormalization.Germs CuspNormalization.SheafGermComplex

/-- Restriction through the positive branch is the ambient axis restriction. -/
theorem plusAxisRestriction_toBranch (s : Triangle) (k : Fin 3) (φ : AmbientGerm) :
    axisRestriction (plusAxisIndex s k) (toBranch (plusBranch s k) φ) =
      ambientAxisRestriction (s.axisIndex (sourceEdgeIndex k)) φ := by
  cases hs : s.upper
  · rw [plusAxisIndex_lower s hs, plusBranch_lower s hs]
    fin_cases k <;>
      simp [axisIndex, sourceEdgeIndex, hs, axisRestriction_toBranch_02,
        axisRestriction_toBranch_10, axisRestriction_toBranch_12]
  · rw [plusAxisIndex_upper s hs, plusBranch_upper s hs]
    fin_cases k <;>
      simp [axisIndex, sourceEdgeIndex, hs, axisRestriction_toBranch_01,
        axisRestriction_toBranch_11,
        axisRestriction_toBranch_12]

/-- Restriction through the negative branch is the same ambient axis restriction. -/
theorem minusAxisRestriction_toBranch (s : Triangle) (k : Fin 3) (φ : AmbientGerm) :
    axisRestriction (minusAxisIndex s k) (toBranch (minusBranch s k) φ) =
      ambientAxisRestriction (s.axisIndex (sourceEdgeIndex k)) φ := by
  cases hs : s.upper
  · rw [minusAxisIndex_lower s hs, minusBranch_lower s hs]
    fin_cases k <;>
      simp [axisIndex, sourceEdgeIndex, hs, axisRestriction_toBranch_00,
        axisRestriction_toBranch_01, axisRestriction_toBranch_11]
  · rw [minusAxisIndex_upper s hs, minusBranch_upper s hs]
    fin_cases k <;>
      simp [axisIndex, sourceEdgeIndex, hs, axisRestriction_toBranch_00,
        axisRestriction_toBranch_02, axisRestriction_toBranch_10]

/-- Extension from the negative plane, restricted to the positive plane,
factors through their common axis. -/
theorem toPlusBranch_extendMinusBranch (s : Triangle) (k : Fin 3) (φ : BranchGerm) :
    toBranch (plusBranch s k) (extendBranch (minusBranch s k) φ) =
      axisExtension (plusAxisIndex s k) (axisRestriction (minusAxisIndex s k) φ) := by
  cases hs : s.upper
  · rw [plusBranch_lower s hs, minusBranch_lower s hs,
      plusAxisIndex_lower s hs, minusAxisIndex_lower s hs]
    fin_cases k <;>
      simp [toBranch_extendBranch_01,
        toBranch_extendBranch_20, toBranch_extendBranch_21]
  · rw [plusBranch_upper s hs, minusBranch_upper s hs,
      plusAxisIndex_upper s hs, minusAxisIndex_upper s hs]
    fin_cases k <;>
      simp [toBranch_extendBranch_10, toBranch_extendBranch_12,
        toBranch_extendBranch_20]

/-- The corresponding factorization with the two branch signs interchanged. -/
theorem toMinusBranch_extendPlusBranch (s : Triangle) (k : Fin 3) (φ : BranchGerm) :
    toBranch (minusBranch s k) (extendBranch (plusBranch s k) φ) =
      axisExtension (minusAxisIndex s k) (axisRestriction (plusAxisIndex s k) φ) := by
  cases hs : s.upper
  · rw [minusBranch_lower s hs, plusBranch_lower s hs,
      minusAxisIndex_lower s hs, plusAxisIndex_lower s hs]
    fin_cases k <;>
      simp [toBranch_extendBranch_02, toBranch_extendBranch_10,
        toBranch_extendBranch_12]
  · rw [minusBranch_upper s hs, plusBranch_upper s hs,
      minusAxisIndex_upper s hs, plusAxisIndex_upper s hs]
    fin_cases k <;>
      simp [toBranch_extendBranch_01, toBranch_extendBranch_02,
        toBranch_extendBranch_21]

/-- An ambient axis extension restricts to the positive plane's axis extension. -/
theorem toPlusBranch_ambientAxisExtension (s : Triangle) (k : Fin 3) (φ : AxisGerm) :
    toBranch (plusBranch s k)
        (ambientAxisExtension (s.axisIndex (sourceEdgeIndex k)) φ) =
      axisExtension (plusAxisIndex s k) φ := by
  cases hs : s.upper
  · rw [plusBranch_lower s hs, plusAxisIndex_lower s hs]
    fin_cases k <;>
      simp [axisIndex, sourceEdgeIndex, hs, toBranch_ambientAxisExtension_02,
        toBranch_ambientAxisExtension_20,
        toBranch_ambientAxisExtension_21]
  · rw [plusBranch_upper s hs, plusAxisIndex_upper s hs]
    fin_cases k <;>
      simp [axisIndex, sourceEdgeIndex, hs, toBranch_ambientAxisExtension_10,
        toBranch_ambientAxisExtension_12,
        toBranch_ambientAxisExtension_21]

/-- An ambient axis extension restricts to the negative plane's axis extension. -/
theorem toMinusBranch_ambientAxisExtension (s : Triangle) (k : Fin 3) (φ : AxisGerm) :
    toBranch (minusBranch s k)
        (ambientAxisExtension (s.axisIndex (sourceEdgeIndex k)) φ) =
      axisExtension (minusAxisIndex s k) φ := by
  cases hs : s.upper
  · rw [minusBranch_lower s hs, minusAxisIndex_lower s hs]
    fin_cases k <;>
      simp [axisIndex, sourceEdgeIndex, hs, toBranch_ambientAxisExtension_01,
        toBranch_ambientAxisExtension_10, toBranch_ambientAxisExtension_12]
  · rw [minusBranch_upper s hs, minusAxisIndex_upper s hs]
    fin_cases k <;>
      simp [axisIndex, sourceEdgeIndex, hs, toBranch_ambientAxisExtension_01,
        toBranch_ambientAxisExtension_02, toBranch_ambientAxisExtension_20]

end Wikipedia.HopfProblem.CuspQuotient.NormalizationLocalCoordinates
