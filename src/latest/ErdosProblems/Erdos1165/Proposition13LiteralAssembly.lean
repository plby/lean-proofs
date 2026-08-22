/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.GaussianGeometricOnePoint
import ErdosProblems.Erdos1165.AnnularProfileMarkedSkeleton
import ErdosProblems.Erdos1165.AppendixTerminalMarkedAssembly
import ErdosProblems.Erdos1165.AppendixPairMomentActualKernel
import ErdosProblems.Erdos1165.AppendixPairReferenceMass
import ErdosProblems.Erdos1165.AppendixPairCrossingTail

/-!
# Literal marked-skeleton assembly for Proposition 1.3

This module is the final adapter below `AnnularComparisons`.  Its hypotheses
do not restate any of the three fields of `AnnularComparisons`:

* the one-point lower bound is obtained from disjoint full-skeleton atoms;
* the terminal lower bound is obtained from a marked stopped-data lower
  decomposition and the literal terminal Poisson kernel;
* the far-pair upper bound is obtained from a marked stopped-data upper
  decomposition, the actual joint visit-count/exit-point kernel, and separate
  one-sided bounds for the retained outside skeleton and its endpoint-integrated
  radial continuation.  The terminal marked reference mass is normalized
  separately.  The near band is controlled by a one-point upper estimate.

Thus the remaining assumptions name the literal path decompositions and the
one-point and two-point Harnack comparisons which have not yet been constructed from
the walk.
-/

open Filter MeasureTheory Set
open scoped ENNReal BigOperators

namespace Erdos1165.Proposition13LiteralAssembly

noncomputable section

open AppendixFirstMoment AppendixLocalTime AppendixPair AppendixPairMoment
open AppendixA11A12ScaleCertificate
open AppendixPairCrossingTail
open AppendixPairMomentActualKernel AppendixPairReferenceMass
open AppendixTerminalMarkedAssembly AnnularProfileMarkedSkeleton
open GaussianGeometricOnePoint GaussianGeometricSchedule
open MarkedBoundaryVisitKernel MarkedTerminalDisintegration
open PoissonKernelMarkedAlgebra Proposition13Assembly Proposition13Scales
open PoissonKernelMarkedHarnack
open TerminalExcursionDisintegration TerminalMarkedSkeletonDecomposition
open TerminalMarkedParameterBounds TerminalMarkedSkeletonMass
open TerminalParameterBounds TerminalSkeletonWords

/-! ## Literal one-point and terminal data -/

/-- The complete literal one-point input at a fixed scale: one disjoint
full-skeleton family for each block and candidate point. -/
def FullProfileFamilies (delta : ℝ) (n : ℕ) :=
  ∀ (i : Fin (chosenBlockCount delta n)) (x : Point),
    x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      FullSkeletonProfileFamily
        ((i : ℕ) * chosenBlockLength delta n)
        (scaleIndex delta n) chosenProfileDelta
        (annularHistoryLoss delta n) x

/-- Literal data consumed by the terminal marked-Poisson adapter.  The
canonical scale certificate contains all numerical, geometric, and Harnack
estimates.  The only path-space field retains the complete complementary
skeleton and inserts all terminal visit counts simultaneously. -/
structure TerminalMarkedLowerData (delta : ℝ) (n : ℕ) : Type where
  certificate : TerminalMarkedScaleCertificate delta (scaleIndex delta n)
  decomposition : ∀ (i : Fin (chosenBlockCount delta n)) (x : Point),
    x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
    ∃ skeletonWeight :
        TerminalSkeletonData
            (requiredTerminalCount
              (scaleIndex delta n) chosenProfileDelta) →
          (Fin (requiredTerminalCount
              (scaleIndex delta n) chosenProfileDelta) →
            TerminalEntrance (scaleIndex delta n) x) →
          (Fin (requiredTerminalCount
              (scaleIndex delta n) chosenProfileDelta) →
            TerminalExit (scaleIndex delta n) x) → ℝ≥0∞,
      MarkedStoppedDataLowerDecomposition fairSteps
        (stoppedSuccessfulPointEvent
          ((i : ℕ) * chosenBlockLength delta n)
          (scaleIndex delta n) chosenProfileDelta x)
        (stoppedThickPointEvent
          ((i : ℕ) * chosenBlockLength delta n)
          (scaleIndex delta n) chosenProfileDelta
          (chosenThickDelta delta) x)
        skeletonWeight
        (supportedTerminalSkeletonKernel
          (profileDelta := chosenProfileDelta) (scaleIndex delta n) x)
        (supportedTerminalMarkedKernel
          (profileDelta := chosenProfileDelta) (scaleIndex delta n) x)
        (terminalVisitEvent (scaleIndex delta n)
          (chosenThickDelta delta)
          (requiredTerminalCount
            (scaleIndex delta n) chosenProfileDelta))

theorem terminalThick_of_literalData
    {delta : ℝ} {n : ℕ} (data : TerminalMarkedLowerData delta n) :
    ∀ (i : Fin (chosenBlockCount delta n)) (x : Point),
      x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      (1 - terminalEpsilon) * fairSteps.real
          (stoppedSuccessfulPointEvent
            ((i : ℕ) * chosenBlockLength delta n)
            (scaleIndex delta n) chosenProfileDelta x) ≤
        fairSteps.real
          (stoppedThickPointEvent
            ((i : ℕ) * chosenBlockLength delta n)
            (scaleIndex delta n) chosenProfileDelta
            (chosenThickDelta delta) x) := by
  exact annularComparisons_terminalThick_of_markedScaleCertificate_decomposition
    data.certificate data.decomposition

/-- The terminal literal-data package itself is automatic at every
sufficiently large selected scale: its analytic component is the canonical
eventual certificate and its path-space component is the no-premise stopped
word insertion decomposition. -/
theorem eventually_terminalMarkedLowerData
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop, Nonempty (TerminalMarkedLowerData delta n) := by
  filter_upwards
      [eventually_terminalMarkedScaleCertificate_scaleIndex hdelta]
      with n hcertificate
  refine ⟨{ certificate := hcertificate, decomposition := ?_ }⟩
  intro i x _hx
  exact exists_terminalMarkedStoppedDataLowerDecomposition
    ((i : ℕ) * chosenBlockLength delta n) (scaleIndex delta n)
    chosenProfileDelta (chosenThickDelta delta) x (by
      have hs := hcertificate.marked.scale_ge_four
      omega)

/-! ## Literal marked upper data for one far pair -/

/-- The source-correct common point envelope for the near contribution and
the two one-sided factors in the far contribution.  This is the explicit
A.11 upper exponent used by `AppendixPairCrossingTail`, rather than the
stronger exact constrained-profile mass. -/
def pairPointEnvelope (delta : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-2 * (scaleIndex delta n : ℝ) +
    (ProfileWeightUpper.profileUpperConstant *
      (scaleIndex delta n : ℝ) ^ (3 / 5 : ℝ) +
        prefixProfileCostDeficit))

lemma pairPointEnvelope_nonneg (delta : ℝ) (n : ℕ) :
    0 ≤ pairPointEnvelope delta n :=
  Real.exp_nonneg _

/-- A complete marked stopped-data upper decomposition for one far pair.
The local kernel is not an abstract comparison: it is the actual joint
terminal visit-count/next-exit kernel.  The retained outside skeleton and
the endpoint-integrated radial continuation are bounded separately, in the
one-sided weighted form of HLOZ (A.16)--(A.17); no radial offspring count is
represented by the terminal marked kernel. -/
structure ActualMarkedFarPairData
    (delta : ℝ) (n : ℕ) (harnackFactor : ℝ)
    (i : Fin (chosenBlockCount delta n)) (x y : Point) : Type 1 where
  Data : Type
  Entrance : Type
  Exit : Type
  coordinateCount : ℕ
  successful : Set StepPath
  retained : Set StepPath
  radialTail : ℝ
  boundary : Fin coordinateCount → Set Point
  target : Fin coordinateCount → Point
  entrance : Fin coordinateCount → Entrance → Point
  endpoint : Fin coordinateCount → Exit → Point
  hitProbability : Fin coordinateCount → ℝ
  escapeProbability : Fin coordinateCount → ℝ
  hitError : Fin coordinateCount → ℝ
  exitError : Fin coordinateCount → ℝ
  target_not_boundary : ∀ j, target j ∉ boundary j
  escape_nonneg : ∀ j, 0 ≤ escapeProbability j
  escape_le_one : ∀ j, escapeProbability j ≤ 1
  escape_eq : ∀ j, escapeProbability j =
    BoundaryVisitRegeneration.escapeBeforePositiveReturnProbability
      (BoundaryVisitLaw.relativeBoundary (boundary j) (target j))
  hit_nonneg : ∀ j, 0 ≤ hitProbability j
  hit_lt_one : ∀ j, hitProbability j < 1
  hitError_nonneg : ∀ j, 0 ≤ hitError j
  exitError_nonneg : ∀ j, 0 ≤ exitError j
  hitFactor_nonneg : ∀ j, 0 ≤ 1 - hitError j
  exitFactor_nonneg : ∀ j, 0 ≤ 1 - exitError j
  hitLower : ∀ j u,
    (1 - hitError j) * hitProbability j ≤
      boundaryStoppedHitKernel (boundary j) (target j) (entrance j u)
  hitUpper : ∀ j u,
    boundaryStoppedHitKernel (boundary j) (target j) (entrance j u) ≤
      (1 + hitError j) * hitProbability j
  exitLower : ∀ j u z,
    (1 - exitError j) *
        (terminalSkeletonKernel (boundary j) (entrance j u)
          (endpoint j z)).toReal ≤
      (terminalSkeletonKernel (boundary j) (target j)
        (endpoint j z)).toReal
  exitUpper : ∀ j u z,
    (terminalSkeletonKernel (boundary j) (target j)
        (endpoint j z)).toReal ≤
      (1 + exitError j) *
        (terminalSkeletonKernel (boundary j) (entrance j u)
          (endpoint j z)).toReal
  visitEvent : Set (Fin coordinateCount → ℕ)
  skeletonWeight : Data →
    (Fin coordinateCount → Entrance) →
    (Fin coordinateCount → Exit) → ℝ≥0∞
  decomposition : MarkedStoppedDataUpperDecomposition fairSteps
    (stoppedThickPointEvent
        ((i : ℕ) * chosenBlockLength delta n)
        (scaleIndex delta n) chosenProfileDelta
        (chosenThickDelta delta) x ∩
      stoppedThickPointEvent
        ((i : ℕ) * chosenBlockLength delta n)
        (scaleIndex delta n) chosenProfileDelta
        (chosenThickDelta delta) y)
    successful skeletonWeight
    (fun j u z ↦ terminalSkeletonKernel
      (boundary j) (entrance j u) (endpoint j z))
    (fun j u k z ↦ terminalMarkedKernel
      (boundary j) (target j) (entrance j u) k (endpoint j z))
    visitEvent
  referenceMass_le_one :
    referenceEventMass
      (fun j k ↦ ENNReal.ofReal
        (visitMass (hitProbability j) (escapeProbability j) k))
      visitEvent ≤ 1
  accumulatedLoss_le :
    (∏ j, ENNReal.ofReal
      (markedPoissonUpperLoss
        (hitProbability j) (hitError j) (exitError j))).toReal ≤
      harnackFactor
  radialTail_nonneg : 0 ≤ radialTail
  /-- The complete successful skeleton includes the post-separation radial
  continuation, whose endpoint-integrated coefficient is `radialTail`. -/
  successful_le : fairSteps.real successful ≤
    radialTail * fairSteps.real retained
  /-- The retained outside event carries the `Γ_x` condition. -/
  retained_le : fairSteps.real retained ≤ pairPointEnvelope delta n
  /-- A.16--A.17 conditional radial-profile continuation bound.  Terminal
  point-local-time marks remain in `referenceEventMass_le_one`. -/
  radialTail_le : radialTail ≤
      pairPointEnvelope delta n /
        prefixProfileLower
          (pairPrefixScale (scaleIndex delta n)
            (separationLevel (scaleIndex delta n) x y))

theorem ActualMarkedFarPairData.pair_le
    {delta : ℝ} {n : ℕ} {harnackFactor : ℝ}
    {i : Fin (chosenBlockCount delta n)} {x y : Point}
    (data : ActualMarkedFarPairData delta n harnackFactor i x y)
    (hharnack0 : 0 ≤ harnackFactor) :
    fairSteps.real
        (stoppedThickPointEvent
            ((i : ℕ) * chosenBlockLength delta n)
            (scaleIndex delta n) chosenProfileDelta
            (chosenThickDelta delta) x ∩
          stoppedThickPointEvent
            ((i : ℕ) * chosenBlockLength delta n)
            (scaleIndex delta n) chosenProfileDelta
            (chosenThickDelta delta) y) ≤
      harnackFactor *
        (pairPointEnvelope delta n ^ 2 /
          prefixProfileLower
            (pairPrefixScale (scaleIndex delta n)
              (separationLevel (scaleIndex delta n) x y))) := by
  let loss : Fin data.coordinateCount → ℝ≥0∞ := fun j ↦
    ENNReal.ofReal (markedPoissonUpperLoss
      (data.hitProbability j) (data.hitError j) (data.exitError j))
  let referenceMass : Fin data.coordinateCount → ℕ → ℝ≥0∞ :=
    fun j k ↦ ENNReal.ofReal
      (visitMass (data.hitProbability j) (data.escapeProbability j) k)
  have hupper : MarkedKernelUpper loss referenceMass
      (fun j u z ↦ terminalSkeletonKernel
        (data.boundary j) (data.entrance j u) (data.endpoint j z))
      (fun j u k z ↦ terminalMarkedKernel
        (data.boundary j) (data.target j) (data.entrance j u) k
          (data.endpoint j z)) := by
    exact terminalMarkedKernel_family_markedKernelUpper
      data.boundary data.target data.entrance data.endpoint
      data.hitProbability data.escapeProbability data.hitError data.exitError
      data.target_not_boundary data.escape_nonneg data.escape_le_one
      data.escape_eq data.hit_nonneg data.hit_lt_one data.hitError_nonneg
      data.exitError_nonneg data.hitFactor_nonneg data.exitFactor_nonneg
      data.hitLower data.hitUpper data.exitLower data.exitUpper
  have hcoefficient :
      (∏ j, loss j) * referenceEventMass referenceMass data.visitEvent ≠ ⊤ := by
    apply markedUpperCoefficient_ne_top
    · intro j
      exact ENNReal.ofReal_ne_top
    · exact data.referenceMass_le_one
  have hreferenceReal :
      (referenceEventMass referenceMass data.visitEvent).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top
      data.referenceMass_le_one
  have hjoint :
      (referenceEventMass referenceMass data.visitEvent).toReal *
          fairSteps.real data.successful ≤
        pairPointEnvelope delta n ^ 2 /
          prefixProfileLower
            (pairPrefixScale (scaleIndex delta n)
              (separationLevel (scaleIndex delta n) x y)) := by
    exact referenceEventMass_mul_successful_le_pairPrefixEnvelope_of_twoStage
      referenceMass data.visitEvent data.successful data.retained
      data.radialTail (pairPointEnvelope delta n)
      (pairPointEnvelope_nonneg _ _) hreferenceReal
      data.successful_le data.retained_le data.radialTail_le
  exact stoppedFarPair_le_of_markedStoppedData
    data.successful loss referenceMass data.skeletonWeight
    (fun j u z ↦ terminalSkeletonKernel
      (data.boundary j) (data.entrance j u) (data.endpoint j z))
    (fun j u k z ↦ terminalMarkedKernel
      (data.boundary j) (data.target j) (data.entrance j u) k
        (data.endpoint j z))
    data.visitEvent hupper data.decomposition hcoefficient
    data.accumulatedLoss_le hharnack0
    hjoint

/-! ## Fixed-scale and eventual assembly -/

/-- Exact pair input below `AnnularFarNearPairComparison`.  In particular,
the far-pair inequality is derived from `ActualMarkedFarPairData`, rather
than stored as a field. -/
structure LiteralPairData (delta : ℝ) (n : ℕ) : Type 1 where
  harnackFactor : ℝ
  harnackFactor_nonneg : 0 ≤ harnackFactor
  harnackFactor_le_budget :
    harnackFactor ≤ Real.exp (scaleCost delta n / 64)
  onePointUpper : ∀ (i : Fin (chosenBlockCount delta n)) x,
    x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
    fairSteps.real
        (stoppedThickPointEvent
          ((i : ℕ) * chosenBlockLength delta n)
          (scaleIndex delta n) chosenProfileDelta
          (chosenThickDelta delta) x) ≤
      pairPointEnvelope delta n
  farPairData : ∀ (i : Fin (chosenBlockCount delta n)) x,
    x ∈ ThickPoint.candidateBox (scaleIndex delta n) → ∀ y,
    y ∈ ThickPoint.candidateBox (scaleIndex delta n) →
    separationLevel (scaleIndex delta n) x y ≤
      decorrelationCutoff (scaleIndex delta n) →
    ActualMarkedFarPairData delta n harnackFactor i x y

theorem LiteralPairData.farNearComparison
    {delta : ℝ} {n : ℕ} (data : LiteralPairData delta n) :
    AnnularFarNearPairComparison
      (chosenBlockCount delta n) (chosenBlockLength delta n)
      (scaleIndex delta n) chosenProfileDelta (chosenThickDelta delta)
      (pairPointEnvelope delta n)
      data.harnackFactor := by
  refine {
    pointUpper_nonneg := pairPointEnvelope_nonneg _ _
    harnackFactor_nonneg := data.harnackFactor_nonneg
    onePoint_le := data.onePointUpper
    farPair_le := ?_ }
  intro i x hx y hy hfar
  exact (data.farPairData i x hx y hy hfar).pair_le
    data.harnackFactor_nonneg

/-- All deterministic pair arithmetic for the explicit crossing-tail point
envelope.  The two copies of the A.11 upper error, the prefix denominator,
and the accumulated marked/Harnack loss each use their checked reserved
shares of `scaleCost`. -/
theorem eventually_pairMoment_of_literalPairData
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop, LiteralPairData delta n →
      ∀ i : Fin (chosenBlockCount delta n),
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
                  (chosenThickDelta delta) y)) ≤ pairMomentBound delta n := by
  filter_upwards
      [eventually_scaleIndex_pos delta,
       eventually_decorrelationCutoff_mem_scaleIndices,
       eventually_cutoff_scaleRadius_le_three_mul_pow12,
       eventually_profileUpperCost_add_deficit_le_sixtyFourth_scaleCost hdelta,
       eventually_geometricPrefixCost_le_sixtyFourth_scaleCost hdelta,
       eventually_geometricCutoff_le_pairPrefixScale,
       eventually_decorrelationPadding_le_scaleCost_share hdelta]
      with n hqOne hcutoff hR hprofile hprefix hprefixCutoff hpadding
  intro data
  have hcost0 : 0 ≤ scaleCost delta n := by
    unfold scaleCost
    positivity
  apply annularComparisons_pairMoment_of_farNearComparison
    hcutoff data.farNearComparison
  · unfold pairPointEnvelope pointUpperBound
    apply Real.exp_le_exp.mpr
    linarith
  · exact hR
  · intro l hl
    have hlIcc := Finset.mem_Icc.mp hl
    have hadd : l + decorrelationPadding (scaleIndex delta n) ≤
        scaleIndex delta n := by
      have hle : l ≤ scaleIndex delta n -
          decorrelationPadding (scaleIndex delta n) := by
        simpa [decorrelationCutoff] using hlIcc.2
      omega
    have hlq : l ≤ scaleIndex delta n :=
      hlIcc.2.trans (Nat.sub_le _ _)
    have hprefixCost : prefixProfileCost
        (pairPrefixScale (scaleIndex delta n) l) ≤
          scaleCost delta n / 64 :=
      prefixProfileCost_pairPrefixScale_le_of_budget
        (hprefixCutoff l hl) hprefix
    apply farLevelTerm_le_of_analyticBudgets
      (A := ProfileWeightUpper.profileUpperConstant *
        (scaleIndex delta n : ℝ) ^ (3 / 5 : ℝ) +
          prefixProfileCostDeficit)
      (B := scaleCost delta n / 64)
      (H := scaleCost delta n / 64)
      (C := scaleCost delta n)
      hqOne hlIcc.1 hlq hadd (hprefixCutoff l hl)
      (pairPointEnvelope_nonneg delta n)
    · exact le_rfl
    · exact data.harnackFactor_nonneg
    · exact data.harnackFactor_le_budget
    · exact hprefixCost
    · nlinarith

/-- All literal data needed at one fixed scale. -/
structure LiteralAnnularScaleData (delta : ℝ) (n : ℕ) : Type 1 where
  profileFamilies : FullProfileFamilies delta n
  pair : LiteralPairData delta n

/-- The analytic estimates are all already eventual; the literal marked
skeleton data therefore constructs the full three-field annular certificate
for every sufficiently large scale. -/
theorem eventually_annularComparisons_of_literalData
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop,
      LiteralAnnularScaleData delta n → AnnularComparisons delta n := by
  filter_upwards
      [eventually_annularComparisons_onePointProfile_of_transfer hdelta,
       eventually_annularComparisons_terminalThick hdelta,
       eventually_pairMoment_of_literalPairData hdelta]
      with n honePoint hterminal hpair
  intro data
  have htransfer : AnnularOnePointProfileTransfer delta n :=
    annularOnePointProfileTransfer_of_fullSkeletonFamilies data.profileFamilies
  refine {
    onePointProfile := honePoint htransfer
    terminalThick := hterminal
    pairMoment := ?_ }
  exact hpair data.pair

/-- Eventual existence of only the literal skeleton data used above. -/
def HasLiteralAnnularScaleData : Prop :=
  ∀ delta : ℝ, 0 < delta → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    Nonempty (LiteralAnnularScaleData delta n)

theorem hasAnnularComparisons_of_literalData
    (hliteral : HasLiteralAnnularScaleData) : HasAnnularComparisons := by
  intro delta hdelta
  obtain ⟨N₁, hN₁⟩ := hliteral delta hdelta
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp
    (eventually_annularComparisons_of_literalData hdelta)
  refine ⟨max N₁ N₂, fun n hn ↦ ?_⟩
  have hn₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn₂ : N₂ ≤ n := le_trans (le_max_right _ _) hn
  exact ⟨hN₂ n hn₂ (Classical.choice (hN₁ n hn₁))⟩

/-- Final Proposition 1.3 consequence from the literal marked-skeleton
obligations, with no `AnnularComparisons` field assumed. -/
theorem hasPlanarMaximumLowerDeviation_of_literalData
    (hliteral : HasLiteralAnnularScaleData) :
    HasPlanarMaximumLowerDeviation simpleRandomWalk :=
  hasPlanarMaximumLowerDeviation_of_annularComparisons
    (hasAnnularComparisons_of_literalData hliteral)

end

end Erdos1165.Proposition13LiteralAssembly
