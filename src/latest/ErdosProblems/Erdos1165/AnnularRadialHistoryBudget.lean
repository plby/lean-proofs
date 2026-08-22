/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularHistoryLossNumerical
import ErdosProblems.Erdos1165.AnnularRadialProfileWords

/-!
# Numerical budget for the literal radial-word transfer

The walk-facing half of the Appendix-A exponent has to pay for four
independent losses: the two spatial entrance/escape pieces, the accumulated
row comparison along the chronological radial word, the transition from the
forced first excursion to `m₂`, and the terminal window.  This file records
that the reserve already built into `annularHistoryLoss` is smaller than an
explicit product of all those factors.

The two factors `1 / 128` are left visible for the initial and final spatial
pieces.  The factor `1 / 2` is left visible for the product of regular radial
row errors.  No probabilistic comparison is assumed here.
-/

open scoped BigOperators ENNReal

namespace Erdos1165.AnnularRadialHistoryBudget

open AppendixFirstMoment AppendixA11A12OnePoint
  AppendixA11A12ScaleCertificate AnnularHistoryLossNumerical
  AnnularRadialProfileWords TerminalNegativeBinomialWindow

noncomputable section

/-- The reserved annular loss pays simultaneously for the two spatial
pieces, a factor two of accumulated row error, the literal first
negative-binomial transition, and the elementary terminal window. -/
theorem eventually_annularHistoryLoss_mul_profileWeight_le_radial_budget
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ∀ (hq2 : 2 ≤ Proposition13Scales.scaleIndex delta N)
        (m : Profile (Proposition13Scales.scaleIndex delta N)),
        IsConstrainedProfile Proposition13Scales.chosenProfileDelta m →
          annularHistoryLoss delta N * profileWeight m ≤
            (1 / 128 : ℝ) * (1 / 128 : ℝ) * (1 / 2 : ℝ) *
              firstProfileTransitionMass hq2 m *
                terminalWindowMass (Proposition13Scales.scaleIndex delta N)
                  Proposition13Scales.chosenProfileDelta
                  (terminalProfileCount hq2 m) * profileWeight m := by
  filter_upwards
      [eventually_annularHistoryLoss_le_one_div_two_pow_thirty_mul_terminalWindow
        hdelta]
      with N hhistory
  intro hq2 m hm
  let terminalMass : ℝ :=
    terminalWindowMass (Proposition13Scales.scaleIndex delta N)
      Proposition13Scales.chosenProfileDelta
      (terminalProfileCount hq2 m)
  have hfirst : (1 / 8192 : ℝ) ≤ firstProfileTransitionMass hq2 m :=
    one_div_8192_le_firstProfileTransitionMass hq2
      (by norm_num [Proposition13Scales.chosenProfileDelta]) hm
  have hcoefficient :
      (1 / 1073741824 : ℝ) ≤
        (1 / 128 : ℝ) * (1 / 128 : ℝ) * (1 / 2 : ℝ) *
          firstProfileTransitionMass hq2 m := by
    nlinarith
  have hterminal : 0 ≤ terminalMass := by
    exact terminalWindowMass_nonneg _ _ _
      (ExcursionTransition.terminalSuccess_pos hq2).le
      (ExcursionTransition.terminalSuccess_le_one hq2)
  have hweight : 0 ≤ profileWeight m := profileWeight_nonneg m
  calc
    annularHistoryLoss delta N * profileWeight m ≤
        ((1 / 1073741824 : ℝ) * terminalMass) * profileWeight m := by
      gcongr
      simpa only [terminalMass] using hhistory hq2 m hm
    _ ≤
        (((1 / 128 : ℝ) * (1 / 128 : ℝ) * (1 / 2 : ℝ) *
          firstProfileTransitionMass hq2 m) * terminalMass) *
            profileWeight m := by
      gcongr
    _ =
        (1 / 128 : ℝ) * (1 / 128 : ℝ) * (1 / 2 : ℝ) *
          firstProfileTransitionMass hq2 m * terminalMass * profileWeight m := by
      ring

end

end Erdos1165.AnnularRadialHistoryBudget
