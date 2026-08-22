/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZFullBetaRegimeSplit
import ErdosProblems.Erdos1165.HLOZHighSpatialBudgetNumerics
import ErdosProblems.Erdos1165.AppendixPair

/-!
# The spatially restricted high-beta screen in HLOZ Lemma 4.10

For the deficit bands above the Proposition 4.8 range, HLOZ enumerate only
lattice points in the deterministic spatial ball around the old favorite.
This file implements that source-level branch.  The candidate square is a
slightly enlarged box containing the mesh ball, and its explicit budget is
`ceil (100 * exp (2 * m ^ alpha))`.  Thus candidate overflow is impossible;
no near-favorite cardinality theorem is invoked in this branch.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZLargeDeficitSpatialScreen

open AppendixPair HLOZGapBetaArithmetic HLOZGapEstimate
open HLOZGapBetaNumerics HLOZGapMeshEscape HLOZGapRandomClockScreen HLOZPathEvents
open HLOZGapPointReturn HLOZGapStoppedCandidate
open HLOZFullBetaRegimeSplit HLOZHighSpatialBudgetNumerics
open HLOZProposition48Candidates
open HLOZTilingEndpointBandSelector HLOZTilingGapBandExtraction
open PointBeforeReturn ScreeningInstantiation StoppedInsertion

noncomputable section

set_option linter.constructorNameAsVariable false

abbrev DominoTiling := Tilings.Tiling

/-- Finite source index for a large-deficit band.  It contains no physical
creation times. -/
structure LargeDeficitSpatialTag where
  pair : Fin 3
  scale : {a : GapScale // a ∈ lowGapMesh}
  index : Fin fullBetaBandCount
  deriving DecidableEq, Fintype

/-- The upper exponent of the adjacent deficit strip represented by a tag. -/
def LargeDeficitSpatialTag.betaNext
    (tag : LargeDeficitSpatialTag) : ℝ :=
  deficitExponent48 (meshExponent tag.scale.1) (tag.index + 1)

/-- Only the source-paper high bands are kept: the split is at the upper
strip exponent `7 / 10`, exactly as in HLOZ Lemma 4.10. -/
noncomputable def largeDeficitSpatialTags : Finset LargeDeficitSpatialTag := by
  classical
  exact Finset.univ.filter fun tag ↦ (7 / 10 : ℝ) < tag.betaNext

theorem mem_largeDeficitSpatialTags_iff
    (tag : LargeDeficitSpatialTag) :
    tag ∈ largeDeficitSpatialTags ↔ (7 / 10 : ℝ) < tag.betaNext := by
  classical
  simp [largeDeficitSpatialTags]

/-- Expanded form of the high-band condition, packaged once to keep later
finite-sum elaboration shallow. -/
theorem deficitExponent48_betaNext_gt_sevenTenths_of_mem
    {tag : LargeDeficitSpatialTag}
    (htag : tag ∈ largeDeficitSpatialTags) :
    (7 / 10 : ℝ) < deficitExponent48 (meshExponent tag.scale.1)
      ((tag.index : ℕ) + 1) := by
  change (7 / 10 : ℝ) < tag.betaNext
  rw [mem_largeDeficitSpatialTags_iff] at htag
  exact htag

/-- Random-clock data attached to a source high-beta tag.  The orientation,
vertex phase, and lazy thresholds are irrelevant to the spatial enumeration;
the return witness uses only ranks, scale, and return count. -/
noncomputable def LargeDeficitSpatialTag.band
    (m : ℕ) (tag : LargeDeficitSpatialTag) : RandomClockBand where
  orientation := .even
  vertexPhase := false
  oldRank := tag.pair + 1
  newRank := tag.pair + 2
  returns := requiredReturns48 m
    (deficitExponent48 (meshExponent tag.scale.1) tag.index)
  externalThreshold := 0
  lazyCap := 0
  beta := tag.betaNext
  scale := tag.scale.1
  oldRank_pos := by omega
  newRank_pos := by omega
  rank_lt := by omega
  newRank_le_four := by omega
  scale_proper := (mem_lowGapMesh_iff.mp tag.scale.2).1

/-- Radius of the coordinate square containing the Euclidean mesh ball. -/
def largeDeficitSpatialRadius (m : ℕ) (a : GapScale) : ℕ :=
  Nat.ceil (2 * meshRadius m a)

/-- The spatial candidate family used in the high-beta source branch. -/
noncomputable def largeDeficitSpatialSites
    (m cutoff : ℕ) (s : WalkPath) (tag : LargeDeficitSpatialTag) :
    Finset Point :=
  coordinateSquare
    (s (pathTruncatedLevelTime m (tag.band m).oldRank cutoff s))
    (largeDeficitSpatialRadius m tag.scale.1)

/-- Named realization predicate, kept reducibly small in the finite-screen
interfaces below. -/
def largeDeficitSpatialRealizes
    (m cutoff : ℕ) (s : WalkPath) (tag : LargeDeficitSpatialTag)
    (x : Point) : Prop :=
  RandomClockPairRealizes m cutoff s (tag.band m) x

/-- The numerical budget used by the high-beta absorption lemma. -/
abbrev largeDeficitSpatialBudget (m : ℕ)
    (tag : LargeDeficitSpatialTag) : ℕ :=
  highSpatialCandidateBudget m tag.scale.1

/-- One tag's complete deterministic-budget/geometric-return contribution. -/
noncomputable def largeDeficitSpatialScreenCost
    (m : ℕ) (tag : LargeDeficitSpatialTag) : ℝ≥0∞ :=
  (largeDeficitSpatialBudget m tag : ℝ≥0∞) *
    Gap.geometricReturnCost
      (meshPointEscapeChance m tag.scale.1) (tag.band m).returns

lemma meshRadius_one_le (m : ℕ) (a : GapScale) :
    1 ≤ meshRadius m a := by
  unfold meshRadius
  exact Real.one_le_exp (Real.rpow_nonneg (by positivity) _)

/-- A point in the defining mesh cell lies in the enumerated coordinate
square centered at the old point. -/
theorem mem_largeDeficitSpatialSites_of_gapScaleOf_eq
    {m cutoff : ℕ} {s : WalkPath} {tag : LargeDeficitSpatialTag}
    {x : Point}
    (hscale : gapScaleOf m
      (s (pathTruncatedLevelTime m (tag.band m).oldRank cutoff s)) x =
        tag.scale.1) :
    x ∈ largeDeficitSpatialSites m cutoff s tag := by
  let old := s (pathTruncatedLevelTime m (tag.band m).oldRank cutoff s)
  let R := meshRadius m tag.scale.1
  have hdist : latticeDistance old x ≤ R :=
    latticeDistance_le_meshRadius_of_gapScaleOf_eq
      (mem_lowGapMesh_iff.mp tag.scale.2).1 hscale
  have hxold : x ∈ ThickPoint.disc old R := hdist
  have hxx : x ∈ ThickPoint.disc x R := by
    change latticeDistance x x ≤ R
    have hself : latticeDistance x x = 0 := by
      simp [latticeDistance]
    rw [hself]
    have hR := meshRadius_one_le m tag.scale.1
    exact zero_le_one.trans hR
  change x ∈ coordinateSquare old (Nat.ceil (2 * R))
  exact mem_coordinateSquare_of_common_disc_point hxold hxx

/-- Exact square cardinality before the exponential simplification. -/
theorem card_largeDeficitSpatialSites
    (m cutoff : ℕ) (s : WalkPath) (tag : LargeDeficitSpatialTag) :
    (largeDeficitSpatialSites m cutoff s tag).card =
      (2 * largeDeficitSpatialRadius m tag.scale.1 + 1) ^ 2 := by
  exact card_coordinateSquare _ _

/-- The enlarged square always fits in the explicit HLOZ spatial budget. -/
theorem card_largeDeficitSpatialSites_le_budget
    (m cutoff : ℕ) (s : WalkPath) (tag : LargeDeficitSpatialTag) :
    (largeDeficitSpatialSites m cutoff s tag).card ≤
      largeDeficitSpatialBudget m tag := by
  let p : ℝ := (m : ℝ) ^ meshExponent tag.scale.1
  let R : ℝ := Real.exp p
  let q : ℕ := Nat.ceil (2 * R)
  have hR : 1 ≤ R := Real.one_le_exp (Real.rpow_nonneg (by positivity) _)
  have hq : (q : ℝ) < 2 * R + 1 :=
    Nat.ceil_lt_add_one (by positivity : 0 ≤ 2 * R)
  have hbase : ((2 * q + 1 : ℕ) : ℝ) ≤ 7 * R := by
    push_cast
    linarith
  have hcardR : (((2 * q + 1) ^ 2 : ℕ) : ℝ) ≤ 49 * R ^ 2 := by
    push_cast
    nlinarith [sq_nonneg ((2 : ℝ) * q + 1), sq_nonneg (7 * R)]
  have hRpow : R ^ 2 = Real.exp (2 * p) := by
    dsimp only [R]
    calc
      Real.exp p ^ 2 = Real.exp p * Real.exp p := pow_two _
      _ = Real.exp (p + p) := (Real.exp_add p p).symm
      _ = Real.exp (2 * p) := by ring_nf
  have hreal : (((2 * q + 1) ^ 2 : ℕ) : ℝ) ≤
      100 * Real.exp (2 * p) := by
    rw [← hRpow]
    nlinarith [sq_nonneg R]
  rw [card_largeDeficitSpatialSites]
  change (2 * q + 1) ^ 2 ≤
    Nat.ceil (100 * Real.exp (2 * p))
  exact_mod_cast hreal.trans (Nat.le_ceil _)

private theorem pack_two_exists
    {A B : Type*} {P : A → Prop} {Q R : A → B → Prop}
    {a : A} {b : B} (hP : P a) (hQ : Q a b) (hR : R a b) :
    ∃ a', P a' ∧ ∃ b', Q a' b' ∧ R a' b' :=
  ⟨a, hP, b, hQ, hR⟩

/-! ## Source-band extraction -/

/-- The finite spatial tag canonically attached to a full beta-band failed
pair.  Naming this constructor keeps the subsequent path witness shallow
enough for Lean's default recursion limit. -/
noncomputable def spatialTagOfFailedPair
    {t : DominoTiling} {m cutoff : ℕ} {s : WalkPath}
    (p : LowGapFailedPair t m cutoff s) (j : ℕ)
    (hj : j < fullBetaBandCount) : LargeDeficitSpatialTag := by
  have holdLe : p.oldRank ≤ 3 := by
    have hnewLe := p.newRank_le_four
    rw [p.rank_succ] at hnewLe
    omega
  exact
    { pair := ⟨p.oldRank - 1, by have := p.oldRank_pos; omega⟩
      scale := ⟨p.scale, p.scale_low⟩
      index := ⟨j, hj⟩ }

theorem spatialTagOfFailedPair_oldRank
    {t : DominoTiling} {m cutoff j : ℕ} {s : WalkPath}
    (p : LowGapFailedPair t m cutoff s) (hj : j < fullBetaBandCount) :
    ((spatialTagOfFailedPair p j hj).band m).oldRank = p.oldRank := by
  have holdLe : p.oldRank ≤ 3 := by
    have hnewLe := p.newRank_le_four
    rw [p.rank_succ] at hnewLe
    omega
  have holdPos := p.oldRank_pos
  simp only [spatialTagOfFailedPair, LargeDeficitSpatialTag.band]
  omega

theorem spatialTagOfFailedPair_newRank
    {t : DominoTiling} {m cutoff j : ℕ} {s : WalkPath}
    (p : LowGapFailedPair t m cutoff s) (hj : j < fullBetaBandCount) :
    ((spatialTagOfFailedPair p j hj).band m).newRank = p.newRank := by
  have holdLe : p.oldRank ≤ 3 := by
    have hnewLe := p.newRank_le_four
    rw [p.rank_succ] at hnewLe
    omega
  have holdPos := p.oldRank_pos
  simp only [spatialTagOfFailedPair, LargeDeficitSpatialTag.band]
  rw [p.rank_succ]
  omega

theorem spatialTagOfFailedPair_mem
    {t : DominoTiling} {m cutoff j : ℕ} {s : WalkPath}
    (p : LowGapFailedPair t m cutoff s) (hj : j < fullBetaBandCount)
    (hlarge : (7 / 10 : ℝ) <
      deficitExponent48 (meshExponent p.scale) (j + 1)) :
    spatialTagOfFailedPair p j hj ∈ largeDeficitSpatialTags := by
  rw [mem_largeDeficitSpatialTags_iff]
  exact hlarge

theorem spatialTagOfFailedPair_newPoint_mem
    {t : DominoTiling} {m cutoff j : ℕ} {s : WalkPath}
    (p : LowGapFailedPair t m cutoff s) (hj : j < fullBetaBandCount) :
    s p.nNew ∈ largeDeficitSpatialSites m cutoff s
      (spatialTagOfFailedPair p j hj) := by
  apply mem_largeDeficitSpatialSites_of_gapScaleOf_eq
  change gapScaleOf m
    (s (pathTruncatedLevelTime m
      ((spatialTagOfFailedPair p j hj).band m).oldRank cutoff s))
      (s p.nNew) = p.scale
  rw [spatialTagOfFailedPair_oldRank p hj, p.oldClock]
  exact p.scale_eq

theorem spatialTagOfFailedPair_realizes
    {t : DominoTiling} {m cutoff j : ℕ} {s : WalkPath}
    (p : LowGapFailedPair t m cutoff s) (hm : 0 < m)
    (hj : j < fullBetaBandCount) (hband : FailedPairBetaBand p j) :
    largeDeficitSpatialRealizes m cutoff s
      (spatialTagOfFailedPair p j hj) (s p.nNew) := by
  apply p.randomClockPairRealizes
      ((spatialTagOfFailedPair p j hj).band m)
    ⟨spatialTagOfFailedPair_oldRank p hj,
      spatialTagOfFailedPair_newRank p hj⟩
    (by rfl)
  have hpow : 0 < (m : ℝ) ^
      deficitExponent48 (meshExponent p.scale) j :=
    Real.rpow_pos_of_pos (by exact_mod_cast hm) _
  change requiredReturns48 m
      (deficitExponent48 (meshExponent p.scale) j) + 1 ≤ p.deficit
  rw [requiredReturns48_add_one hpow]
  exact hband.1

theorem failedPair_has_spatial_tag_and_point
    {t : DominoTiling} {m cutoff j : ℕ} {s : WalkPath}
    (p : LowGapFailedPair t m cutoff s) (hm : 0 < m)
    (hj : j < fullBetaBandCount) (hband : FailedPairBetaBand p j)
    (hlarge : (7 / 10 : ℝ) <
      deficitExponent48 (meshExponent p.scale) (j + 1)) :
    ∃ tag' ∈ largeDeficitSpatialTags,
      ∃ x' ∈ largeDeficitSpatialSites m cutoff s tag',
        largeDeficitSpatialRealizes m cutoff s tag' x' := by
  apply @pack_two_exists LargeDeficitSpatialTag Point
    (fun tag' ↦ tag' ∈ largeDeficitSpatialTags)
    (fun tag' x' ↦ x' ∈ largeDeficitSpatialSites m cutoff s tag')
    (fun tag' x' ↦ largeDeficitSpatialRealizes m cutoff s tag' x')
    (spatialTagOfFailedPair p j hj) (s p.nNew)
  · rw [mem_largeDeficitSpatialTags_iff]
    exact hlarge
  · apply mem_largeDeficitSpatialSites_of_gapScaleOf_eq
    change gapScaleOf m
      (s (pathTruncatedLevelTime m
        ((spatialTagOfFailedPair p j hj).band m).oldRank cutoff s))
        (s p.nNew) = p.scale
    rw [spatialTagOfFailedPair_oldRank p hj, p.oldClock]
    exact p.scale_eq
  · apply p.randomClockPairRealizes
        ((spatialTagOfFailedPair p j hj).band m)
      ⟨spatialTagOfFailedPair_oldRank p hj,
        spatialTagOfFailedPair_newRank p hj⟩
      (by rfl)
    have hpow : 0 < (m : ℝ) ^
        deficitExponent48 (meshExponent p.scale) j :=
      Real.rpow_pos_of_pos (by exact_mod_cast hm) _
    change requiredReturns48 m
        (deficitExponent48 (meshExponent p.scale) j) + 1 ≤ p.deficit
    rw [requiredReturns48_add_one hpow]
    exact hband.1

/-- Every path in the large-deficit branch is represented by one of the
finite high-beta tags and by one point in its spatial square. -/
theorem largeDeficitSpatialPathGapWitness
    (t : DominoTiling) (m : ℕ) (hm : 1 < m) :
    PathGapWitness
      (onTimeSpatialBetaLowGapExceptionalEvent t m)
      largeDeficitSpatialTags
      (largeDeficitSpatialSites m
        (levelCutoffTime upperTailDelta m))
      (largeDeficitSpatialBudget m)
      (largeDeficitSpatialRealizes m
        (levelCutoffTime upperTailDelta m)) := by
  intro s hs _hoverflow
  obtain ⟨p, j, hfull, hlargeBeta⟩ := hs.2
  rcases hfull with ⟨hj, hband, _hupper⟩
  exact failedPair_has_spatial_tag_and_point p (zero_lt_one.trans hm) hj
    hband hlargeBeta

/-- The spatial budget dominates the candidate square on every path, so the
candidate-overflow event for the high-beta branch is empty. -/
theorem largeDeficitSpatialCandidateOverflow_eq_empty
    (m cutoff : ℕ) :
    candidateOverflow largeDeficitSpatialTags
        (largeDeficitSpatialSites m cutoff)
        (largeDeficitSpatialBudget m) = ∅ := by
  ext s
  simp only [candidateOverflow, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
    iff_false]
  rintro ⟨tag, _htag, hoverflow⟩
  exact (Nat.not_lt_of_ge
    (card_largeDeficitSpatialSites_le_budget m cutoff s tag)) hoverflow

/-! ## Stopped spatial slots -/

/-- Point occupying a fixed slot of the spatial square. -/
def largeDeficitSpatialSlotCandidatePoint
    (m cutoff : ℕ) (tag : LargeDeficitSpatialTag) (slot : ℕ)
    (omega : StepPath) : Point :=
  (finsetSlot
    (largeDeficitSpatialSites m cutoff (trajectory omega) tag) slot).getD 0

lemma largeDeficitSpatialSlotCandidatePoint_eq_of_slot
    {m cutoff : ℕ} {tag : LargeDeficitSpatialTag} {slot : ℕ}
    {omega : StepPath} {x : Point}
    (hslot : finsetSlot
      (largeDeficitSpatialSites m cutoff (trajectory omega) tag) slot =
        some x) :
    largeDeficitSpatialSlotCandidatePoint m cutoff tag slot omega = x := by
  simp [largeDeficitSpatialSlotCandidatePoint, hslot]

/-- The spatial slot is determined by the stopped old position. -/
theorem largeDeficitSpatialSlotCandidatePoint_observable
    (m cutoff : ℕ) (tag : LargeDeficitSpatialTag) (slot : ℕ)
    (x : Point) :
    IsMeasurableAtStopping
      (truncatedLevelTime m (tag.band m).oldRank cutoff)
      {omega |
        largeDeficitSpatialSlotCandidatePoint m cutoff tag slot omega = x} := by
  intro n
  let deterministicPoint : StepPath → Point := fun omega ↦
    (finsetSlot
      (coordinateSquare (trajectory omega n)
        (largeDeficitSpatialRadius m tag.scale.1)) slot).getD 0
  have hdetMeas : MeasurableSet[incrementFiltration n]
      {omega | deterministicPoint omega = x} := by
    exact measurableSet_eq_fun
      ((measurable_of_countable (fun center : Point ↦
        (finsetSlot (coordinateSquare center
          (largeDeficitSpatialRadius m tag.scale.1)) slot).getD 0)).comp
        (measurable_trajectory_at_incrementFiltration n)) measurable_const
  have heq :
      {omega |
          largeDeficitSpatialSlotCandidatePoint m cutoff tag slot omega = x} ∩
          {omega |
            truncatedLevelTime m (tag.band m).oldRank cutoff omega = n} =
        {omega | deterministicPoint omega = x} ∩
          {omega |
            truncatedLevelTime m (tag.band m).oldRank cutoff omega = n} := by
    ext omega
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hpoint, hclock⟩
      refine ⟨?_, hclock⟩
      simpa only [largeDeficitSpatialSlotCandidatePoint,
        largeDeficitSpatialSites, pathTruncatedLevelTime_trajectory,
        hclock, deterministicPoint] using hpoint
    · rintro ⟨hpoint, hclock⟩
      refine ⟨?_, hclock⟩
      simpa only [largeDeficitSpatialSlotCandidatePoint,
        largeDeficitSpatialSites, pathTruncatedLevelTime_trajectory,
        hclock, deterministicPoint] using hpoint
  rw [heq]
  exact hdetMeas.inter
    ((isFiniteStoppingTime_truncatedLevelTime m (tag.band m).oldRank cutoff).measurableSet_eq n)

/-- A spatial slot-success event is measurable. -/
theorem measurableSet_largeDeficitSpatialSlotSuccess
    (m cutoff : ℕ) (tag : LargeDeficitSpatialTag) (slot : ℕ) :
    MeasurableSet
      (slotSuccessEvent (largeDeficitSpatialSites m cutoff)
        (largeDeficitSpatialRealizes m cutoff) tag slot) := by
  have heq :
      slotSuccessEvent (largeDeficitSpatialSites m cutoff)
          (largeDeficitSpatialRealizes m cutoff) tag slot =
        ⋃ x : Point,
          {s | finsetSlot
            (largeDeficitSpatialSites m cutoff s tag) slot = some x} ∩
          {s | largeDeficitSpatialRealizes m cutoff s tag x} := by
    ext s
    simp only [slotSuccessEvent, Set.mem_ofPred_eq, Set.mem_iUnion,
      Set.mem_inter_iff]
  rw [heq]
  apply MeasurableSet.iUnion
  intro x
  have hslot : MeasurableSet
      {s : WalkPath | finsetSlot
        (largeDeficitSpatialSites m cutoff s tag) slot = some x} := by
    have hclock := measurableSet_pathTruncatedLevelTime_eq
      m (tag.band m).oldRank cutoff
    have heqSlot :
        {s : WalkPath | finsetSlot
            (largeDeficitSpatialSites m cutoff s tag) slot = some x} =
          ⋃ n : ℕ,
            {s | pathTruncatedLevelTime m (tag.band m).oldRank cutoff s = n} ∩
            {s | finsetSlot
              (coordinateSquare (s n)
                (largeDeficitSpatialRadius m tag.scale.1)) slot = some x} := by
      ext s
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro hs
        refine ⟨pathTruncatedLevelTime m (tag.band m).oldRank cutoff s,
          rfl, ?_⟩
        simpa only [largeDeficitSpatialSites] using hs
      · rintro ⟨n, hn, hs⟩
        simpa only [largeDeficitSpatialSites, hn] using hs
    rw [heqSlot]
    apply MeasurableSet.iUnion
    intro n
    have hcenter : MeasurableSet {center : Point |
        finsetSlot (coordinateSquare center
          (largeDeficitSpatialRadius m tag.scale.1)) slot = some x} :=
      (Set.to_countable _).measurableSet
    have hslotAtN : MeasurableSet {s : WalkPath |
        finsetSlot (coordinateSquare (s n)
          (largeDeficitSpatialRadius m tag.scale.1)) slot = some x} := by
      have happ : Measurable (fun s : WalkPath ↦ s n) := measurable_pi_apply n
      simpa only [Set.preimage_ofPred_eq] using
        (happ hcenter)
    exact (hclock n).inter hslotAtN
  exact hslot.inter
    (by
      change MeasurableSet
        {s | RandomClockPairRealizes m cutoff s (tag.band m) x}
      exact measurableSet_randomClockPairRealizes m cutoff (tag.band m) x)

/-- Spatial cell selected by the stopped old position and the slot point. -/
def largeDeficitSpatialGuard
    (m cutoff : ℕ) (tag : LargeDeficitSpatialTag) (slot : ℕ) :
    Set StepPath :=
  {omega | gapScaleOf m
      (trajectory omega
        (truncatedLevelTime m (tag.band m).oldRank cutoff omega))
      (largeDeficitSpatialSlotCandidatePoint m cutoff tag slot omega) =
        tag.scale.1}

theorem largeDeficitSpatialGuard_observable
    (m cutoff : ℕ) (tag : LargeDeficitSpatialTag) (slot : ℕ) :
    IsMeasurableAtStopping
      (truncatedLevelTime m (tag.band m).oldRank cutoff)
      (largeDeficitSpatialGuard m cutoff tag slot) := by
  have hold : ∀ x, IsMeasurableAtStopping
      (truncatedLevelTime m (tag.band m).oldRank cutoff)
      {omega | trajectory omega
        (truncatedLevelTime m (tag.band m).oldRank cutoff omega) = x} := by
    intro x
    simpa only [stoppedLocation] using
      (stoppedLocation_fiber_observable
        (isFiniteStoppingTime_truncatedLevelTime m
          (tag.band m).oldRank cutoff) x)
  have hcandidate := largeDeficitSpatialSlotCandidatePoint_observable
    m cutoff tag slot
  simpa only [largeDeficitSpatialGuard] using
    (isMeasurableAtStopping_binary_fiber hold hcandidate
      (fun old candidate ↦ gapScaleOf m old candidate) tag.scale.1)

/-- A fixed spatial slot carries the literal ordered return schedule.  The
candidate is selected at the stopped old-creation clock; all its scheduled
visits occur before the new-creation clock, and the old favorite is avoided
until the last such visit. -/
noncomputable def largeDeficitSpatialSlotScheduleWitness
    (m cutoff : ℕ) (tag : LargeDeficitSpatialTag) (slot : ℕ) :
    GuardedStoppedCandidateScheduleWitness
      (slotSuccessEvent (largeDeficitSpatialSites m cutoff)
        (largeDeficitSpatialRealizes m cutoff) tag slot)
      (cutoff + 1) (tag.band m).returns
      (meshPointEscapeChance m tag.scale.1) where
  past := truncatedLevelTime m (tag.band m).oldRank cutoff
  candidate := largeDeficitSpatialSlotCandidatePoint m cutoff tag slot
  oldFavorite := fun omega ↦ trajectory omega
    (truncatedLevelTime m (tag.band m).oldRank cutoff omega)
  past_isStopping :=
    isFiniteStoppingTime_truncatedLevelTime m (tag.band m).oldRank cutoff
  past_lt_deadline := fun omega ↦
    Nat.lt_succ_of_le
      (truncatedLevelTime_le m (tag.band m).oldRank cutoff omega)
  candidate_observable := largeDeficitSpatialSlotCandidatePoint_observable
    m cutoff tag slot
  oldFavorite_observable := by
    intro x
    simpa only [stoppedLocation] using
      (stoppedLocation_fiber_observable
        (isFiniteStoppingTime_truncatedLevelTime m
          (tag.band m).oldRank cutoff) x)
  guard := largeDeficitSpatialGuard m cutoff tag slot
  guard_observable := largeDeficitSpatialGuard_observable m cutoff tag slot
  event_guard := by
    intro omega homega
    obtain ⟨x, hslot, hrealizes⟩ := homega
    have hcandidate :
        largeDeficitSpatialSlotCandidatePoint m cutoff tag slot omega = x :=
      largeDeficitSpatialSlotCandidatePoint_eq_of_slot hslot
    change gapScaleOf m
      (trajectory omega
        (truncatedLevelTime m (tag.band m).oldRank cutoff omega))
      (largeDeficitSpatialSlotCandidatePoint m cutoff tag slot omega) =
        tag.scale.1
    rw [hcandidate]
    have hx : x = trajectory omega
        (truncatedLevelTime m (tag.band m).newRank cutoff omega) := by
      simpa only [largeDeficitSpatialRealizes, RandomClockPairRealizes,
        pathTruncatedLevelTime_trajectory] using hrealizes.1.2.2.2.2.2.2
    rw [hx]
    change gapScaleOf m
      (trajectory omega
        (truncatedLevelTime m (tag.band m).oldRank cutoff omega))
      (trajectory omega
        (truncatedLevelTime m (tag.band m).newRank cutoff omega)) =
      (tag.band m).scale
    simpa only [largeDeficitSpatialRealizes, RandomClockPairRealizes,
      pathTruncatedLevelTime_trajectory] using hrealizes.1.2.2.2.2.1
  event_distinct := by
    intro omega homega
    obtain ⟨x, hslot, hrealizes⟩ := homega
    have hcandidate :
        largeDeficitSpatialSlotCandidatePoint m cutoff tag slot omega = x :=
      largeDeficitSpatialSlotCandidatePoint_eq_of_slot hslot
    change trajectory omega
      (truncatedLevelTime m (tag.band m).oldRank cutoff omega) ≠
        largeDeficitSpatialSlotCandidatePoint m cutoff tag slot omega
    rw [hcandidate]
    have hx : x = trajectory omega
        (truncatedLevelTime m (tag.band m).newRank cutoff omega) := by
      simpa only [largeDeficitSpatialRealizes, RandomClockPairRealizes,
        pathTruncatedLevelTime_trajectory] using hrealizes.1.2.2.2.2.2.2
    rw [hx]
    exact creation_locations_ne (tag.band m).oldRank_pos
      (tag.band m).newRank_pos (tag.band m).rank_lt
      (by simpa only [largeDeficitSpatialRealizes, RandomClockPairRealizes,
        pathTruncatedLevelTime_trajectory] using hrealizes.1.1)
      (by simpa only [largeDeficitSpatialRealizes, RandomClockPairRealizes,
        pathTruncatedLevelTime_trajectory] using hrealizes.1.2.1)
  event_schedule := by
    intro omega homega
    obtain ⟨x, hslot, hrealizes⟩ := homega
    let nOld := truncatedLevelTime m (tag.band m).oldRank cutoff omega
    let nNew := truncatedLevelTime m (tag.band m).newRank cutoff omega
    let nTerminal := truncatedLevelTime m 4 cutoff omega
    have hold : ThresholdCreation (trajectory omega) m
        (tag.band m).oldRank nOld := by
      simpa only [largeDeficitSpatialRealizes, RandomClockPairRealizes,
        pathTruncatedLevelTime_trajectory, nOld, nNew, nTerminal] using
        hrealizes.1.1
    have hnew : ThresholdCreation (trajectory omega) m
        (tag.band m).newRank nNew := by
      simpa only [largeDeficitSpatialRealizes, RandomClockPairRealizes,
        pathTruncatedLevelTime_trajectory, nOld, nNew, nTerminal] using
        hrealizes.1.2.1
    have hnext : thresholdCount (trajectory omega) nTerminal (m + 1) = 0 := by
      simpa only [largeDeficitSpatialRealizes, RandomClockPairRealizes,
        pathTruncatedLevelTime_trajectory, nOld, nNew, nTerminal] using
        hrealizes.1.2.2.1
    have hnewTerminal : nNew ≤ nTerminal := by
      simpa only [largeDeficitSpatialRealizes, RandomClockPairRealizes,
        pathTruncatedLevelTime_trajectory, nOld, nNew, nTerminal] using
        hrealizes.1.2.2.2.1
    have hcandidate :
        largeDeficitSpatialSlotCandidatePoint m cutoff tag slot omega = x :=
      largeDeficitSpatialSlotCandidatePoint_eq_of_slot hslot
    have hx : x = trajectory omega nNew := by
      simpa only [largeDeficitSpatialRealizes, RandomClockPairRealizes,
        pathTruncatedLevelTime_trajectory, nOld, nNew, nTerminal] using
        hrealizes.1.2.2.2.2.2.2
    have hreturn : localTime (trajectory omega) nOld x +
        ((tag.band m).returns + 1) ≤ m := by
      simpa only [largeDeficitSpatialRealizes, RandomClockPairRealizes,
        pathTruncatedLevelTime_trajectory, nOld, nNew, nTerminal] using
        hrealizes.2
    have hthreshold : m ≤ localTime (trajectory omega) nNew x := by
      rw [hx]
      exact (mem_thresholdSites (trajectory omega) nNew m
        (trajectory omega nNew)).mp
          (position_mem_thresholdSites_of_creation
            (tag.band m).newRank_pos hnew) |>.2
    have holdNew : nOld < nNew :=
      creation_time_lt (tag.band m).oldRank_pos (tag.band m).newRank_pos
        (tag.band m).rank_lt hold hnew
    have hgain : localTime (trajectory omega) nOld
        (largeDeficitSpatialSlotCandidatePoint m cutoff tag slot omega) +
          ((tag.band m).returns + 1) ≤
        localTime (trajectory omega) nNew
          (largeDeficitSpatialSlotCandidatePoint m cutoff tag slot omega) := by
      rw [hcandidate]
      exact hreturn.trans hthreshold
    have hschedule : HasStrictVisitSchedule
        (truncatedLevelTime m (tag.band m).oldRank cutoff)
        (largeDeficitSpatialSlotCandidatePoint m cutoff tag slot)
        (nNew + 1) ((tag.band m).returns + 1) omega := by
      apply hasStrictVisitSchedule_of_localTime_gain
        (past := truncatedLevelTime m (tag.band m).oldRank cutoff)
        (target := largeDeficitSpatialSlotCandidatePoint m cutoff tag slot)
      · simpa only [nOld] using Nat.lt_succ_of_lt holdNew
      · simpa only [Nat.add_sub_cancel] using hgain
    obtain ⟨times, hmono, hafter, hbeforeNew, hvisit⟩ := hschedule
    refine ⟨times, hmono, hafter, ?_, hvisit, ?_⟩
    · intro i
      exact (hbeforeNew i).trans_le
        (Nat.succ_le_succ
          (truncatedLevelTime_le m (tag.band m).newRank cutoff omega))
    · intro q hpast hq
      have hlastNew :
          times ⟨(tag.band m).returns,
            Nat.lt_succ_self (tag.band m).returns⟩ ≤ nNew :=
        Nat.lt_succ_iff.mp (hbeforeNew _)
      have havoid := no_oldCreation_visit_of_no_next_level
        (tag.band m).oldRank_pos hold hnext
      exact havoid q (by simpa only [nOld] using hpast)
        ((hq.trans hlastNew).trans hnewTerminal)
  guard_lower := by
    intro omega hguard hdistinct
    exact meshPointEscapeChance_le_pointBeforeReturnProbability
      (tag.band m).scale_proper hguard hdistinct

/-- Sharp one-slot probability bound for the spatial high-beta screen. -/
theorem measure_largeDeficitSpatialSlotSuccess_le_geometric
    (m cutoff : ℕ) (tag : LargeDeficitSpatialTag) (slot : ℕ) :
    simpleRandomWalk
        (slotSuccessEvent (largeDeficitSpatialSites m cutoff)
          (largeDeficitSpatialRealizes m cutoff) tag slot) ≤
      Gap.geometricReturnCost
        (meshPointEscapeChance m tag.scale.1) (tag.band m).returns := by
  exact measure_le_geometricReturnCost_of_guardedStoppedCandidateSchedule
    (measurableSet_largeDeficitSpatialSlotSuccess m cutoff tag slot)
    (meshPointEscapeChance_pos m tag.scale.1).le
    (meshPointEscapeChance_le_one m tag.scale.1)
    (largeDeficitSpatialSlotScheduleWitness m cutoff tag slot)

/-- Complete measure bound for the exact source high-beta event.  The
candidate overflow term vanishes because the spatial square fits in its
deterministic budget. -/
theorem measure_onTimeSpatialBetaLowGapExceptionalEvent_le_spatialScreen
    (t : DominoTiling) (m : ℕ) (hm : 1 < m) :
    simpleRandomWalk (onTimeSpatialBetaLowGapExceptionalEvent t m) ≤
      ∑ tag ∈ largeDeficitSpatialTags,
        (largeDeficitSpatialBudget m tag : ℝ≥0∞) *
          Gap.geometricReturnCost
            (meshPointEscapeChance m tag.scale.1) (tag.band m).returns := by
  let cutoff := levelCutoffTime upperTailDelta m
  let sites := largeDeficitSpatialSites m cutoff
  let budget := largeDeficitSpatialBudget m
  let realizes := largeDeficitSpatialRealizes m cutoff
  have hwitness := largeDeficitSpatialPathGapWitness t m hm
  have hoverflow : candidateOverflow largeDeficitSpatialTags sites budget = ∅ :=
    largeDeficitSpatialCandidateOverflow_eq_empty m cutoff
  have hcover : Gap.GapEventCovered
      (onTimeSpatialBetaLowGapExceptionalEvent t m)
      largeDeficitSpatialTags
      (fun tag ↦ Finset.range (budget tag))
      (slotSuccessEvent sites realizes) := by
    have hcovered := gapEvent_diff_overflow_covered_by_slots
      (onTimeSpatialBetaLowGapExceptionalEvent t m)
      largeDeficitSpatialTags sites budget realizes hwitness
    simpa only [hoverflow, sdiff_empty] using hcovered
  exact Gap.measure_gapEvent_le_geometric_sum simpleRandomWalk
    (onTimeSpatialBetaLowGapExceptionalEvent t m)
    largeDeficitSpatialTags
    (fun tag ↦ Finset.range (budget tag))
    (slotSuccessEvent sites realizes) budget
    (fun tag ↦ meshPointEscapeChance m tag.scale.1)
    (fun tag ↦ (tag.band m).returns)
    hcover (range_candidateCountBound largeDeficitSpatialTags budget)
    (by
      intro tag _htag slot _hslot
      exact measure_largeDeficitSpatialSlotSuccess_le_geometric
        m cutoff tag slot)

/-- The finite spatial screen is absorbed by the high-beta return exponent.
This direct finite-tag proof avoids elaborating an auxiliary image/template
type and stays within Lean's default recursion limit. -/
theorem eventually_largeDeficitSpatial_geometric_sum_le
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ m : ℕ in atTop,
      ∑ tag ∈ largeDeficitSpatialTags,
        largeDeficitSpatialScreenCost m tag ≤
        ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) := by
  have heach : ∀ tag ∈ largeDeficitSpatialTags, ∀ᶠ m : ℕ in atTop,
      largeDeficitSpatialScreenCost m tag ≤
        ENNReal.ofReal
          (Real.exp (-(2 * c) * Real.log (m : ℝ) ^ 2)) := by
    intro tag htag
    rw [mem_largeDeficitSpatialTags_iff] at htag
    have hlarge : (7 / 10 : ℝ) <
        deficitExponent48 (meshExponent tag.scale.1)
          ((tag.index : ℕ) + 1) := by
      change (7 / 10 : ℝ) < tag.betaNext
      exact htag
    have hone :=
      eventually_highSpatialBudget_mul_meshGeometricReturnCost_le_exp_neg
        tag.scale.1 (tag.index : ℕ) (2 * c) tag.scale.2 hlarge
    simpa only [largeDeficitSpatialScreenCost, largeDeficitSpatialBudget,
      LargeDeficitSpatialTag.band] using hone
  have hall := (Finset.eventually_all largeDeficitSpatialTags).2 heach
  have habsorb := eventually_nat_mul_exp_neg_two_log_sq_le_exp_neg
    largeDeficitSpatialTags.card hc
  filter_upwards [hall, habsorb] with m hallM habsorbM
  let q : ℝ≥0∞ := ENNReal.ofReal
    (Real.exp (-(2 * c) * Real.log (m : ℝ) ^ 2))
  calc
    ∑ tag ∈ largeDeficitSpatialTags,
        largeDeficitSpatialScreenCost m tag ≤
        largeDeficitSpatialTags.card • q :=
      largeDeficitSpatialTags.sum_le_card_nsmul
        (largeDeficitSpatialScreenCost m) q hallM
    _ = (largeDeficitSpatialTags.card : ℝ≥0∞) * q := by
      exact nsmul_eq_mul _ _
    _ ≤ ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) :=
      habsorbM

/-- Premise-free stretched-logarithmic envelope for the exact source
high-beta exceptional event. -/
theorem eventually_simpleRandomWalk_onTimeSpatialBetaLowGapExceptionalEvent_le_exp
    (t : DominoTiling) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk (onTimeSpatialBetaLowGapExceptionalEvent t m) ≤
        ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) := by
  have hsum := eventually_largeDeficitSpatial_geometric_sum_le hc
  filter_upwards [hsum, eventually_ge_atTop (2 : ℕ)] with m hsumM hm
  have hmeasure :=
    measure_onTimeSpatialBetaLowGapExceptionalEvent_le_spatialScreen t m hm
  change simpleRandomWalk (onTimeSpatialBetaLowGapExceptionalEvent t m) ≤
    ∑ tag ∈ largeDeficitSpatialTags,
      largeDeficitSpatialScreenCost m tag at hmeasure
  exact hmeasure.trans hsumM

/-- The high-beta spatial branch is summable, with no assumed event
probability estimate. -/
theorem simpleRandomWalk_onTimeSpatialBetaLowGapExceptionalEvent_series_ne_top
    (t : DominoTiling) :
    ∑' m, simpleRandomWalk
      (onTimeSpatialBetaLowGapExceptionalEvent t m) ≠ ∞ := by
  exact HLOZUpperEstimates.measure_series_ne_top_of_eventually_exp_neg_log_sq_bound
    simpleRandomWalk (onTimeSpatialBetaLowGapExceptionalEvent t)
    (by norm_num : (0 : ℝ) < 1)
    (eventually_simpleRandomWalk_onTimeSpatialBetaLowGapExceptionalEvent_le_exp
      t (c := 1) (by norm_num))

end

end Erdos1165.HLOZLargeDeficitSpatialScreen
