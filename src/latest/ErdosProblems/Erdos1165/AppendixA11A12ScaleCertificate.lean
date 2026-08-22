/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.AppendixA11A12OnePoint
import ErdosProblems.Erdos1165.Proposition13Scales

/-!
# Walk-facing adapter for the shifted A.11--A.12 one-point bound

The cycle-free analytic module proves a lower bound for the exact constrained
profile probability.  This file composes it with the remaining annular
one-point transfer and packages the result in the precise
`Proposition13Scales.AnnularComparisons` interface.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace Erdos1165.AppendixA11A12ScaleCertificate

noncomputable section

open AppendixFirstMoment GaussianBlockFactorization GaussianMultiBlockProfile
  AppendixA11A12OnePoint Proposition13Assembly Proposition13Scales

/-- The explicit reserve for the initial hit, the forced first upcrossing,
the terminal window, the final escape, and the accumulated annular Harnack
loss.  Half of `scaleCost` is reserved for this walk-facing comparison; the
other half pays for the A.11--A.12 profile construction. -/
def annularHistoryLoss (delta : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-(1 / 2 : ℝ) * scaleCost delta n)

lemma annularHistoryLoss_pos (delta : ℝ) (n : ℕ) :
    0 < annularHistoryLoss delta n := Real.exp_pos _

/-- The genuine walk-specific one-point annular comparison, with the exact
block starts and successful-point event used by `AnnularComparisons`.

The coefficient is essential: HLOZ Lemma A.6 contains a forced first
upcrossing of mass `1/4`, as well as initial-hit, terminal-window, final-escape,
and accumulated Harnack factors.  The source proves comparability, not a
coefficient-one domination by the ideal constrained-profile sum. -/
structure AnnularOnePointProfileTransfer (delta : ℝ) (n : ℕ) : Prop where
  historyLoss_mul_constrainedProfile_le :
    ∀ (i : Fin (chosenBlockCount delta n)) x,
      x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      annularHistoryLoss delta n *
          constrainedProfileWeight (scaleIndex delta n) chosenProfileDelta ≤
        fairSteps.real
          (stoppedSuccessfulPointEvent
            ((i : ℕ) * chosenBlockLength delta n)
            (scaleIndex delta n) chosenProfileDelta x)

/-- The other two annular fields, kept separate so that the analytic
one-point proof can be replaced without repackaging them. -/
structure TerminalPairComparisons (delta : ℝ) (n : ℕ) : Prop where
  terminalThick : ∀ (i : Fin (chosenBlockCount delta n)) x,
    x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
    (1 - terminalEpsilon) * fairSteps.real
        (stoppedSuccessfulPointEvent
          ((i : ℕ) * chosenBlockLength delta n)
          (scaleIndex delta n) chosenProfileDelta x) ≤
      fairSteps.real
        (stoppedThickPointEvent
          ((i : ℕ) * chosenBlockLength delta n)
          (scaleIndex delta n) chosenProfileDelta
          (chosenThickDelta delta) x)
  pairMoment : ∀ i : Fin (chosenBlockCount delta n),
    (∑ x ∈ ThickPoint.candidateBox (scaleIndex delta n),
      ∑ y ∈ ThickPoint.candidateBox (scaleIndex delta n),
        fairSteps.real
          (stoppedThickPointEvent
              ((i : ℕ) * chosenBlockLength delta n)
              (scaleIndex delta n) chosenProfileDelta
              (chosenThickDelta delta) x ∩
            stoppedThickPointEvent
              ((i : ℕ) * chosenBlockLength delta n)
              (scaleIndex delta n) chosenProfileDelta
              (chosenThickDelta delta) y)) ≤
      pairMomentBound delta n

/-- The exact `AnnularComparisons.onePointProfile` field obtained from the
shifted A.11--A.12 multiblock estimate. -/
theorem annularComparisons_onePointProfile_of_multiblock
    {targetN : ℕ} {targetDelta : ℝ}
    {b : GaussianBlock} {bs : List GaussianBlock} {A B C : ℝ}
    (hq : 2 ≤ scaleIndex targetDelta targetN)
    (hbstart : 2 ≤ b.start)
    (hconsecutive : ConsecutiveBlocks (b :: bs))
    (hend : gaussianBlocksEnd (b :: bs) = scaleIndex targetDelta targetN)
    (hstart : ∀ c ∈ b :: bs, 0 < c.start)
    (hscale : ∀ c ∈ b :: bs,
      (2560 : ℝ) * (c.start + c.steps : ℕ) ^ 2 ≤ (c.radius : ℝ) ^ 2)
    (hcenter : ∀ c ∈ b :: bs, ∀ l, BlockContains c l →
      c.radius ≤ profileCenter l)
    (hwidth : ∀ c ∈ b :: bs, ∀ l, BlockContains c l →
      (c.radius : ℝ) ≤ (l : ℝ) ^ (1 + chosenProfileDelta))
    (cert : EmbeddedTailA11Certificate (scaleIndex targetDelta targetN)
      b.start chosenProfileDelta A B C (b :: bs))
    (hnumerical : onePointBound targetDelta targetN ≤
      annularHistoryLoss targetDelta targetN *
        multiblockProfileLower (scaleIndex targetDelta targetN)
          chosenProfileDelta A B C (b :: bs))
    (hannular : AnnularOnePointProfileTransfer targetDelta targetN) :
    ∀ (i : Fin (chosenBlockCount targetDelta targetN)) x,
      x ∈ ThickPoint.candidateBox (scaleIndex targetDelta targetN) →
      onePointBound targetDelta targetN ≤ fairSteps.real
        (stoppedSuccessfulPointEvent
          ((i : ℕ) * chosenBlockLength targetDelta targetN)
          (scaleIndex targetDelta targetN) chosenProfileDelta x) := by
  intro i x hx
  exact hnumerical.trans ((mul_le_mul_of_nonneg_left
    (multiblockProfileLower_le_constrainedProfileWeight
      hq hbstart hconsecutive hend hstart hscale hcenter hwidth cert)
    (annularHistoryLoss_pos targetDelta targetN).le).trans
      (hannular.historyLoss_mul_constrainedProfile_le i x hx))

/-- **Direct constructor for the exact `AnnularComparisons` interface.**

After the deterministic schedule inequalities and the shifted A.11
certificate are supplied, the only probabilistic hypotheses are the three
annular comparisons themselves. -/
theorem annularComparisons_of_multiblock
    {targetN : ℕ} {targetDelta : ℝ}
    {b : GaussianBlock} {bs : List GaussianBlock} {A B C : ℝ}
    (hq : 2 ≤ scaleIndex targetDelta targetN)
    (hbstart : 2 ≤ b.start)
    (hconsecutive : ConsecutiveBlocks (b :: bs))
    (hend : gaussianBlocksEnd (b :: bs) = scaleIndex targetDelta targetN)
    (hstart : ∀ c ∈ b :: bs, 0 < c.start)
    (hscale : ∀ c ∈ b :: bs,
      (2560 : ℝ) * (c.start + c.steps : ℕ) ^ 2 ≤ (c.radius : ℝ) ^ 2)
    (hcenter : ∀ c ∈ b :: bs, ∀ l, BlockContains c l →
      c.radius ≤ profileCenter l)
    (hwidth : ∀ c ∈ b :: bs, ∀ l, BlockContains c l →
      (c.radius : ℝ) ≤ (l : ℝ) ^ (1 + chosenProfileDelta))
    (cert : EmbeddedTailA11Certificate (scaleIndex targetDelta targetN)
      b.start chosenProfileDelta A B C (b :: bs))
    (hnumerical : onePointBound targetDelta targetN ≤
      annularHistoryLoss targetDelta targetN *
        multiblockProfileLower (scaleIndex targetDelta targetN)
          chosenProfileDelta A B C (b :: bs))
    (honePoint : AnnularOnePointProfileTransfer targetDelta targetN)
    (hterminalPair : TerminalPairComparisons targetDelta targetN) :
    AnnularComparisons targetDelta targetN := by
  exact {
    onePointProfile := annularComparisons_onePointProfile_of_multiblock
      hq hbstart hconsecutive hend hstart hscale hcenter hwidth cert
        hnumerical honePoint
    terminalThick := hterminalPair.terminalThick
    pairMoment := hterminalPair.pairMoment }

end

end Erdos1165.AppendixA11A12ScaleCertificate
