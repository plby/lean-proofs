/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos1165.HLOZLazyOverflow
import ErdosProblems.Erdos1165.TilingStoppedProductDisintegration

/-!
# Closed estimates for the stopped lazy/random-clock split

This file is the assembly layer above `HLOZLazyOverflow`.  It first replaces
the genuine random-clock visited range by the deterministic HLOZ-cap range,
only on the canonical support of simple random walk.  The off-support set is
proved null, rather than silently identifying arbitrary `WalkPath`s with
increment trajectories.  It then packages the finite family of remaining
dynamic product laws and the exact random-clock return numerics.

The all-six tiling stopped-coordinate law remains a single visible datum.
It is intended to be constructed from
`TilingStoppedCoordinateProductSpec`; in particular it is not a path-level
transition estimate and it contains no fixed physical creation time.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZLazyOverflowClosure

open HLOZLazyOverflow HLOZGapRandomClockScreen HLOZGapRandomClockNumerics
open HLOZGapEstimate HLOZPathEvents HLOZProposition48Candidates
open HLOZDynamicStoppedOnePointClosure HLOZDynamicThresholdedScreening
open HLOZThresholdedShellScreening ExternalStoppedWeightedOnePoint
open ExternalProposition44 NearFavoriteShells ScreeningInstantiation
open VariableStoppedTracePartition
open HLOZTraceCappedProductScreening TilingStoppedProductDisintegration
open TilingVariableStoppedTracePartition CappedCoordinateMassCertificate
open GeometricChernoff Balancedness
open LazyDecomposition

noncomputable section

/-! ## Exact overflow domination on the simple-walk support -/

/-- The full finite-band overflow after enlarging each stopped external range
to the deterministic HLOZ cap. -/
def randomClockDominatingCandidateOverflow
    (m cutoff : ℕ) (bands : Finset RandomClockBand) : Set WalkPath :=
  candidateOverflow bands
    (fun s band ↦ randomClockDominatingBandSites m cutoff band s)
    (fun band ↦ candidateBudget48 m band.beta)

/-- The noncanonical complement really is null under simple random walk. -/
theorem simpleRandomWalk_validStepWalk_compl :
    simpleRandomWalk validStepWalkᶜ = 0 := by
  have hvalid : simpleRandomWalk validStepWalk = 1 := by
    have huniv : walkLift (Set.univ : Set StepPath) = validStepWalk := by
      ext s
      simp [walkLift]
    rw [← huniv, simpleRandomWalk_walkLift MeasurableSet.univ]
    simp
  rw [measure_compl measurableSet_validStepWalk
    (measure_ne_top simpleRandomWalk validStepWalk), hvalid]
  simp

/-- Literal path-set domination, with the null off-support piece displayed. -/
theorem randomClockCandidateOverflow_subset_dominating_union_invalid
    {m cutoff : ℕ} {bands : Finset RandomClockBand}
    (hcutoff : cutoff ≤ hlozCutoff44 m) :
    candidateOverflow bands (randomClockBandSites m cutoff)
        (fun band ↦ candidateBudget48 m band.beta) ⊆
      randomClockDominatingCandidateOverflow m cutoff bands ∪
        validStepWalkᶜ := by
  rintro s ⟨band, hband, hoverflow⟩
  by_cases hvalid : s ∈ validStepWalk
  · left
    exact ⟨band, hband, hoverflow.trans_le (Finset.card_le_card
      (randomClockBandSites_subset_dominating_of_valid hcutoff hvalid))⟩
  · exact Or.inr hvalid

/-- The genuine finite-band overflow therefore costs no more than the
deterministic-cap dynamic overflow. -/
theorem simpleRandomWalk_randomClockCandidateOverflow_le_dominating
    {m cutoff : ℕ} {bands : Finset RandomClockBand}
    (hcutoff : cutoff ≤ hlozCutoff44 m) :
    simpleRandomWalk
        (candidateOverflow bands (randomClockBandSites m cutoff)
          (fun band ↦ candidateBudget48 m band.beta)) ≤
      simpleRandomWalk (randomClockDominatingCandidateOverflow m cutoff bands) := by
  calc
    simpleRandomWalk
        (candidateOverflow bands (randomClockBandSites m cutoff)
          (fun band ↦ candidateBudget48 m band.beta)) ≤
        simpleRandomWalk
          (randomClockDominatingCandidateOverflow m cutoff bands ∪
            validStepWalkᶜ) :=
      measure_mono
        (randomClockCandidateOverflow_subset_dominating_union_invalid hcutoff)
    _ ≤ simpleRandomWalk (randomClockDominatingCandidateOverflow m cutoff bands) +
        simpleRandomWalk validStepWalkᶜ := measure_union_le _ _
    _ = simpleRandomWalk
        (randomClockDominatingCandidateOverflow m cutoff bands) := by
      rw [simpleRandomWalk_validStepWalk_compl, add_zero]

/-- Finite union over bands, now in exactly the single-band form consumed by
the closed stopped one-point Proposition 4.8 theorem. -/
theorem simpleRandomWalk_randomClockCandidateOverflow_le_sum_dominating
    {m cutoff : ℕ} {bands : Finset RandomClockBand}
    (hcutoff : cutoff ≤ hlozCutoff44 m) :
    simpleRandomWalk
        (candidateOverflow bands (randomClockBandSites m cutoff)
          (fun band ↦ candidateBudget48 m band.beta)) ≤
      ∑ band ∈ bands,
        simpleRandomWalk (randomClockDominatingBandOverflow m cutoff band) := by
  refine (simpleRandomWalk_randomClockCandidateOverflow_le_dominating
    hcutoff).trans ?_
  simpa only [randomClockDominatingCandidateOverflow,
    randomClockDominatingBandOverflow, candidateOverflow,
    Screening.someCandidateBad, Set.mem_ofPred_eq] using
      (Screening.measure_someCandidateBad_le_sum simpleRandomWalk bands
        (fun band ↦ randomClockDominatingBandOverflow m cutoff band))

/-! ## Actual stopped lazy laws from variable-time tiling fibres -/

/-- The literal geometric upper-tail cost used to certify one stopped lazy
overflow.  It is deliberately the exact finite law, before the checked
moderate-deviation estimate is applied. -/
noncomputable def stoppedLazyGeometricUpperCost (m : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal
    ((geometric15Vector m).real
      {g | (m : ℝ) / 15 + geometricDeviation m ≤ geometricSum g})

theorem stoppedLazyOverflowEvent_subset_thresholdReachStage
    (o : Orientation) (m k cap : ℕ) :
    stoppedLazyOverflowEvent o m k cap ⊆ thresholdReachStage m k := by
  intro s hs
  rcases Set.mem_iUnion.mp hs with ⟨n, hn⟩
  exact ⟨n, hn.1.1⟩

/-- A genuine variable-time trace certificate for one stopped lazy event.
The stage is the whole rank-`k` reaching event, so the trace index contains no
physical creation time. -/
abbrev StoppedLazyTraceScreen (o : Orientation) (m k cap : ℕ) :=
  SomeTraceCappedProductScreening
    (thresholdReachStage m k) (stoppedLazyOverflowEvent o m k cap)
    (stoppedLazyGeometricUpperCost m)

/-- The all-six state-dependent coordinate specification produces the exact
trace certificate needed here.  Its `coordinate_identity` field is an
equality of finite geometric sums, rather than the desired path probability
bound. -/
def stoppedLazyTraceScreenOfTilingCoordinateSpec
    (t : TilingLazyDecomposition.DominoTiling)
    (o : Orientation) (m k cap : ℕ)
    (spec : TilingStoppedCoordinateProductSpec
      (favoriteTilingStagePiece t m k (thresholdReachStage m k))
      (stoppedLazyOverflowEvent o m k cap)
      (stoppedLazyGeometricUpperCost m)) :
    StoppedLazyTraceScreen o m k cap :=
  someFavoriteTilingTraceCappedScreenOfStoppedCoordinateSpec
    t m k (thresholdReachStage m k)
    (stoppedLazyOverflowEvent o m k cap)
    (stoppedLazyGeometricUpperCost m)
    (measurableSet_thresholdReachStage m k) (fun _ hs ↦ hs)
    (stoppedLazyOverflowEvent_subset_thresholdReachStage o m k cap) spec

/-- A variable-time trace screen bounds its stopped lazy overflow by the
literal geometric upper tail. -/
theorem simpleRandomWalk_stoppedLazyOverflowEvent_le_geometricUpper
    {o : Orientation} {m k cap : ℕ}
    (screen : StoppedLazyTraceScreen o m k cap) :
    simpleRandomWalk (stoppedLazyOverflowEvent o m k cap) ≤
      stoppedLazyGeometricUpperCost m := by
  have hstage : simpleRandomWalk (thresholdReachStage m k) ≤ 1 := by
    simpa using measure_mono (μ := simpleRandomWalk)
      (subset_univ (thresholdReachStage m k))
  calc
    simpleRandomWalk (stoppedLazyOverflowEvent o m k cap) ≤
        stoppedLazyGeometricUpperCost m *
          simpleRandomWalk (thresholdReachStage m k) :=
      @transition_measure_le_of_traceCappedProductScreening
        screen.Index screen.countableIndex
        (thresholdReachStage m k) (stoppedLazyOverflowEvent o m k cap)
        (measurableSet_stoppedLazyOverflowEvent o m k cap)
        (stoppedLazyGeometricUpperCost m) ENNReal.ofReal_ne_top
        screen.screening
    _ ≤ stoppedLazyGeometricUpperCost m * 1 := by gcongr
    _ = stoppedLazyGeometricUpperCost m := mul_one _

/-- Construct the actual `GeometricBalanceLaw`: the sole candidate is the
complete stopped-past lazy overflow, and its one-site upper law is supplied
by the exact variable-time product screen. -/
def stoppedLazyBalanceLawOfTraceScreen
    {o : Orientation} {m k cap : ℕ} (hm : 0 < m)
    (hdeviation : geometricDeviation m ≤ m)
    (screen : StoppedLazyTraceScreen o m k cap) :
    StoppedLazyBalanceLaw o m k cap where
  sites := {(0 : Point)}
  lowerBad := fun _ ↦ ∅
  upperBad := fun _ ↦ stoppedLazyOverflowEvent o m k cap
  budget := 1
  successes := fun _ ↦ m
  identify := by
    ext s
    simp [Screening.someCandidateBad, Balancedness.twoSidedBad]
  m_pos := hm
  card_le := by simp
  successes_pos := by simpa using hm
  successes_le := by simp
  deviation_le := by simpa using hdeviation
  lower_law := by simp
  upper_law := by
    intro _ _
    exact simpleRandomWalk_stoppedLazyOverflowEvent_le_geometricUpper screen

theorem eventually_geometricDeviation_le_self :
    ∀ᶠ m : ℕ in atTop, geometricDeviation m ≤ m := by
  filter_upwards [eventually_geometricDeviation_le_half,
    eventually_ge_atTop (1 : ℕ)] with m hhalf hm
  have hm0 : (0 : ℝ) ≤ m := by positivity
  exact hhalf.trans (by nlinarith)

end

end Erdos1165.HLOZLazyOverflowClosure
