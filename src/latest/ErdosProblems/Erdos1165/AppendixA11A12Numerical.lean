/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.AppendixA11A12ScaleCertificate

/-!
# Exact numerical budget for the shifted A.11--A.12 lower bound

The first Gaussian block may start after a fixed finite prefix.  This file
records the exact logarithmic price of that prefix and shows that the sole
remaining numerical comparison is additive: prefix reserve, shifted A.11
error, and the A.12 block/connector cost must fit inside `scaleCost`.

This formulation also prevents an inadmissibly long deterministic prefix
from being hidden inside an unexplained one-point comparison.
-/

open scoped BigOperators

namespace Erdos1165.AppendixA11A12Numerical

noncomputable section

open AppendixFirstMoment ProfileSmallBall ProfileTaylor ProfileA11Assembly
  GaussianBlockFactorization GaussianMultiBlockProfile
  AppendixA11A12OnePoint AppendixA11A12ScaleCertificate
  Proposition13Assembly Proposition13Scales

/-- Exact extra logarithmic cost of forcing the centered profile on the
finite prefix before the first Gaussian block. -/
def centeredPrefixReserve (start : ℕ) : ℝ :=
  -(2 * (start : ℝ)) -
    ∑ l ∈ Finset.Ico 2 start,
      edgeStirlingExponent (profileCenter l) (profileCenter (l + 1))

lemma exp_neg_two_start_sub_centeredPrefixReserve (start : ℕ) :
    Real.exp (-(2 * (start : ℝ)) - centeredPrefixReserve start) =
      centeredPrefixStirlingWeight start := by
  unfold centeredPrefixReserve centeredPrefixStirlingWeight
  congr 1
  ring

/-- The exact additive cost appearing in the multiblock profile lower
bound.  For a schedule whose first block starts at a fixed scale, the first
term is a fixed constant; the other two terms are the A.11 and A.12 costs. -/
def multiblockProfileCost (n start : ℕ) (delta A B C : ℝ)
    (blocks : List GaussianBlock) : ℝ :=
  centeredPrefixReserve start +
    a11ErrorCoefficient delta A B C * (n : ℝ) ^ (3 * delta) +
    gaussianBlockTotalCost blocks

/-- Exact exponential form of `multiblockProfileLower`, with its leading
`exp (-2*n)` factor exposed. -/
lemma multiblockProfileLower_eq_exp_neg_two_sub_cost
    {n : ℕ} {delta A B C : ℝ} {b : GaussianBlock} {bs : List GaussianBlock}
    (hbn : b.start ≤ n) :
    multiblockProfileLower n delta A B C (b :: bs) =
      Real.exp (-(2 * (n : ℝ)) -
        multiblockProfileCost n b.start delta A B C (b :: bs)) := by
  change centeredPrefixStirlingWeight b.start *
      Real.exp (-(2 * (n - b.start : ℕ) : ℝ) -
        a11ErrorCoefficient delta A B C * (n : ℝ) ^ (3 * delta) -
        gaussianBlockTotalCost (b :: bs)) = _
  rw [← exp_neg_two_start_sub_centeredPrefixReserve b.start,
    ← Real.exp_add]
  unfold multiblockProfileCost
  rw [Nat.cast_sub hbn]
  congr 1
  ring

/-- An additive budget inequality is sufficient for the exact numerical
one-point comparison required by `AnnularComparisons`. -/
theorem onePointBound_le_multiblockProfileLower_of_cost
    {targetN : ℕ} {targetDelta : ℝ}
    {b : GaussianBlock} {bs : List GaussianBlock} {A B C : ℝ}
    (hbn : b.start ≤ scaleIndex targetDelta targetN)
    (hcost : multiblockProfileCost (scaleIndex targetDelta targetN) b.start
        chosenProfileDelta A B C (b :: bs) ≤ scaleCost targetDelta targetN) :
    onePointBound targetDelta targetN ≤
      multiblockProfileLower (scaleIndex targetDelta targetN)
        chosenProfileDelta A B C (b :: bs) := by
  rw [multiblockProfileLower_eq_exp_neg_two_sub_cost hbn]
  unfold onePointBound
  apply Real.exp_le_exp.mpr
  linarith

/-- The sound walk-facing numerical comparison.  The A.11--A.12 profile
construction uses at most half of `scaleCost`; the remaining half is the
explicit `annularHistoryLoss` multiplying the ideal profile probability. -/
theorem onePointBound_le_annularHistoryLoss_mul_multiblockProfileLower_of_cost
    {targetN : ℕ} {targetDelta : ℝ}
    {b : GaussianBlock} {bs : List GaussianBlock} {A B C : ℝ}
    (hbn : b.start ≤ scaleIndex targetDelta targetN)
    (hcost : multiblockProfileCost (scaleIndex targetDelta targetN) b.start
        chosenProfileDelta A B C (b :: bs) ≤
      (1 / 2 : ℝ) * scaleCost targetDelta targetN) :
    onePointBound targetDelta targetN ≤
      annularHistoryLoss targetDelta targetN *
        multiblockProfileLower (scaleIndex targetDelta targetN)
          chosenProfileDelta A B C (b :: bs) := by
  rw [multiblockProfileLower_eq_exp_neg_two_sub_cost hbn]
  unfold annularHistoryLoss onePointBound
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

/-- Exact `AnnularComparisons.onePointProfile` field with the numerical
hypothesis stated as the transparent additive A.11--A.12 cost budget. -/
theorem annularComparisons_onePointProfile_of_multiblockCost
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
    (hcost : multiblockProfileCost (scaleIndex targetDelta targetN) b.start
        chosenProfileDelta A B C (b :: bs) ≤
      (1 / 2 : ℝ) * scaleCost targetDelta targetN)
    (hannular : AnnularOnePointProfileTransfer targetDelta targetN) :
    ∀ (i : Fin (chosenBlockCount targetDelta targetN)) x,
      x ∈ ThickPoint.candidateBox (scaleIndex targetDelta targetN) →
      onePointBound targetDelta targetN ≤ fairSteps.real
        (stoppedSuccessfulPointEvent
          ((i : ℕ) * chosenBlockLength targetDelta targetN)
          (scaleIndex targetDelta targetN) chosenProfileDelta x) := by
  have hbn : b.start ≤ scaleIndex targetDelta targetN := by
    rw [← hend]
    exact gaussianBlocksEnd_ge_start hconsecutive
  exact annularComparisons_onePointProfile_of_multiblock hq hbstart
    hconsecutive hend hstart hscale hcenter hwidth cert
    (onePointBound_le_annularHistoryLoss_mul_multiblockProfileLower_of_cost
      hbn hcost) hannular

/-- Direct constructor for `AnnularComparisons` from the transparent
multiblock cost budget and the two genuinely annular terminal/pair inputs. -/
theorem annularComparisons_of_multiblockCost
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
    (hcost : multiblockProfileCost (scaleIndex targetDelta targetN) b.start
        chosenProfileDelta A B C (b :: bs) ≤
      (1 / 2 : ℝ) * scaleCost targetDelta targetN)
    (honePoint : AnnularOnePointProfileTransfer targetDelta targetN)
    (hterminalPair : TerminalPairComparisons targetDelta targetN) :
    AnnularComparisons targetDelta targetN := by
  exact {
    onePointProfile := annularComparisons_onePointProfile_of_multiblockCost
      hq hbstart hconsecutive hend hstart hscale hcenter hwidth cert hcost honePoint
    terminalThick := hterminalPair.terminalThick
    pairMoment := hterminalPair.pairMoment }

end

end Erdos1165.AppendixA11A12Numerical
