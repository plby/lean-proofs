/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.BufferedProfileMarkovUpper
import ErdosProblems.Erdos1165.Proposition13LiteralAssembly

/-!
# A one-point upper bound for the buffered completion event

The exact-profile radial-word estimate and the buffered Markov summation fit
together without paying for the three erased coordinates.  This is the
one-point estimate used by the asymmetric completion construction.
-/

open Filter MeasureTheory
open scoped ENNReal

namespace Erdos1165.BufferedStoppedSuccessfulPointUpper

open AppendixFirstMoment AppendixPairCrossingTail
open AnnularProfileLiteralAtoms AnnularRadialProfileWords
open BufferedProfileMarkovUpper BufferedStoppedSuccessfulPointEvent
open ProfileWeightUpper Proposition13LiteralAssembly ThickPoint

noncomputable section

/-- The buffered stopped event has the sharp profile upper exponent whenever
the chronological exact-profile estimate is available at the given scale. -/
theorem fairSteps_real_stoppedBufferedSuccessfulPointEvent_le_exp
    {start n l : ℕ} {x : Point}
    (hn : 5 ≤ n) (hl : 1 ≤ l) (hln : l + 1 ≤ n)
    (hcutoffn : profileUpperTailStart ≤ n)
    (hrow : fairSteps (stoppedBufferedSuccessfulPointEvent
        start n (l - 3) (l + 1) profileUpperDelta x) ≤
      ∑' m : {m : Profile n //
          IsBufferedInternalProfile (l - 3) (l + 1)
            profileUpperDelta m},
        ENNReal.ofReal
          ((1 + 1 / (n : ℝ) ^ 4) ^
              exactProfileRadialWordMaxTransitions m.1 *
            (firstProfileTransitionMass (by omega) m.1 *
              TerminalNegativeBinomialWindow.terminalWindowMass
                n profileUpperDelta
                  (TerminalNegativeBinomialWindow.terminalProfileCount
                    (by omega) m.1) *
              profileWeight m.1))) :
    fairSteps.real (stoppedBufferedSuccessfulPointEvent
        start n (l - 3) (l + 1) profileUpperDelta x) ≤
      Real.exp (-(2 * (n : ℝ)) +
        profileUpperConstant * (n : ℝ) ^ (3 / 5 : ℝ)) := by
  have hmeasure := hrow.trans
    (tsum_buffered_exactProfileCost_le_exp_separation
      hn hl hln hcutoffn)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
  simpa only [Measure.real,
    ENNReal.toReal_ofReal (Real.exp_nonneg _)] using hreal

/-- The same estimate in the public Proposition 1.3 envelope, whose fixed
prefix reserve is nonnegative. -/
theorem fairSteps_real_stoppedBufferedSuccessfulPointEvent_le_pairPointEnvelope
    {delta : ℝ} {blockIndex start n l : ℕ} {x : Point}
    (hn : 5 ≤ n) (hl : 1 ≤ l) (hln : l + 1 ≤ n)
    (hcutoffn : profileUpperTailStart ≤ n)
    (hnIndex : n = Proposition13Scales.scaleIndex delta blockIndex)
    (hrow : fairSteps (stoppedBufferedSuccessfulPointEvent
        start n (l - 3) (l + 1) profileUpperDelta x) ≤
      ∑' m : {m : Profile n //
          IsBufferedInternalProfile (l - 3) (l + 1)
            profileUpperDelta m},
        ENNReal.ofReal
          ((1 + 1 / (n : ℝ) ^ 4) ^
              exactProfileRadialWordMaxTransitions m.1 *
            (firstProfileTransitionMass (by omega) m.1 *
              TerminalNegativeBinomialWindow.terminalWindowMass
                n profileUpperDelta
                  (TerminalNegativeBinomialWindow.terminalProfileCount
                    (by omega) m.1) *
              profileWeight m.1))) :
    fairSteps.real (stoppedBufferedSuccessfulPointEvent
        start n (l - 3) (l + 1) profileUpperDelta x) ≤
      pairPointEnvelope delta blockIndex := by
  have hsharp :=
    fairSteps_real_stoppedBufferedSuccessfulPointEvent_le_exp
      hn hl hln hcutoffn hrow
  apply hsharp.trans
  unfold pairPointEnvelope
  rw [← hnIndex]
  exact Real.exp_le_exp.mpr (by
    linarith [prefixProfileCostDeficit_nonneg])

end

end Erdos1165.BufferedStoppedSuccessfulPointUpper
