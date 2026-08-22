/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos1165.HLOZDynamicThresholdedScreening
import ErdosProblems.Erdos1165.HLOZGapCandidateRealization
import ErdosProblems.Erdos1165.HLOZGapRandomClockScreen
import ErdosProblems.Erdos1165.ExternalStoppedWeightedOnePoint
import ErdosProblems.Erdos1165.HLOZDynamicStoppedOnePointClosure
import ErdosProblems.Erdos1165.HLOZGapRandomClockNumerics
import ErdosProblems.Erdos1165.VariableStoppedFiber
import ErdosProblems.Erdos1165.VariableStoppedTracePartition

/-!
# Lazy-overflow events at the variable HLOZ creation clock

The next favorite location is not observable at the preceding creation
clock.  Consequently the lazy-excursion reduction used before Proposition
4.8 must not single out that future point.  This file uses the stronger,
stopped-past event on which the lazy contribution is capped simultaneously
at every lattice point.  Its complement is a countable union of finite-prefix
events and is therefore measurable.

The clock is kept genuinely variable: `stoppedLazyOverflowEvent` is the union
over the unique physical creation time, rather than a refinement which fixes
that time inside an external-word fibre.  The last section records the exact
finite-cap insertion-law interface used to estimate this event.  It is stated
directly in terms of the geometric point masses produced by
`VariableStoppedFiber`, so it cannot be discharged by assuming the target
transition or by conditioning on a fixed physical time.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZLazyOverflow

open HLOZGapCandidateRealization HLOZPathEvents LazyDecomposition
open PathInsertion PreStoppingFiber SpatialInsertionFiber StoppedInsertion
open VariableStoppedFiber
open HLOZThresholdedShellScreening ScreeningInstantiation
open HLOZDynamicThresholdedScreening HLOZGapRandomClockScreen
open HLOZGapFixedPair HLOZProposition48Candidates NearFavoriteShells
open PreStoppingSpatialLaw
open HLOZGapEstimate HLOZGapMeshEscape
open ExternalStoppedWeightedOnePoint HLOZDynamicStoppedOnePointClosure
open VariableStoppedTracePartition

noncomputable section

/-! ## The stopped-past good and bad events -/

/-- The fixed boundary atom together with all deleted excursions accumulated
at a point by a deterministic prefix. -/
def orientedNonExternalLocalTime (o : Orientation) (s : WalkPath)
    (n : ℕ) (x : Point) : ℕ :=
  orientedBoundaryLocalTime o s x + orientedLazyLocalTime o s n x

/-- At one deterministic prefix, every point has at most `cap` units of
local time omitted by the oriented external trace. -/
def LazyGoodAt (o : Orientation) (n cap : ℕ) (s : WalkPath) : Prop :=
  ∀ x, orientedNonExternalLocalTime o s n x ≤ cap

/-- Complement of `LazyGoodAt`, written existentially for measurability and
finite-union estimates. -/
def LazyOverflowAt (o : Orientation) (n cap : ℕ) (s : WalkPath) : Prop :=
  ∃ x, cap < orientedNonExternalLocalTime o s n x

theorem lazyOverflowAt_iff_not_lazyGoodAt
    (o : Orientation) (n cap : ℕ) (s : WalkPath) :
    LazyOverflowAt o n cap s ↔ ¬LazyGoodAt o n cap s := by
  simp only [LazyOverflowAt, LazyGoodAt, not_forall, not_le]

/-- Overflow at the genuine level-`m`, rank-`k` creation clock.  The physical
creation time remains under the countable union; it is not part of the
external-word data on which the insertion coordinates are conditioned. -/
def stoppedLazyOverflowEvent (o : Orientation) (m k cap : ℕ) : Set WalkPath :=
  ⋃ n, thresholdCreationSet m k n ∩ {s | LazyOverflowAt o n cap s}

/-- The corresponding stopped-past good event. -/
def stoppedLazyGoodEvent (o : Orientation) (m k cap : ℕ) : Set WalkPath :=
  ⋃ n, thresholdCreationSet m k n ∩ {s | LazyGoodAt o n cap s}

/-- The finite family needed by the three possible preceding creations and
the two checkerboard orientations. -/
def lazyOverflowExceptionalEvent (m cap : ℕ) : Set WalkPath :=
  (⋃ k : Fin 3, stoppedLazyOverflowEvent .even m (k + 1) cap) ∪
    ⋃ k : Fin 3, stoppedLazyOverflowEvent .shifted m (k + 1) cap

/-- The lazy-good part of an arbitrary gap event.  Parameterizing the target
lets the same stopped-past split be used for the low-mesh exceptional event,
without committing this module to a particular spatial scale cutoff. -/
def lazyGoodPart (gapEvent : Set WalkPath) (m cap : ℕ) : Set WalkPath :=
  gapEvent \ lazyOverflowExceptionalEvent m cap

/-- Compatibility specialization for the original all-scale on-time gap. -/
def lazyGoodGapEvent (t : DominoTiling) (m cap : ℕ) : Set WalkPath :=
  lazyGoodPart (onTimeGapDeficitExceptionalEvent t m) m cap

/-! ## Finite-prefix measurability -/

private def orientedNonExternalLocalTimePrefix (o : Orientation) {n : ℕ}
    (u : Fin (n + 1) → Point) (x : Point) : ℕ :=
  match o with
  | .even => finiteLazyLocalTime .even u x
  | .shifted => (if u 0 = x then 1 else 0) + shiftedLazyLocalTime u x

private theorem orientedNonExternalLocalTime_eq_prefix
    (o : Orientation) (s : WalkPath) (n : ℕ) (x : Point) :
    orientedNonExternalLocalTime o s n x =
      orientedNonExternalLocalTimePrefix o (pathPrefix s n) x := by
  cases o with
  | even =>
      simp [orientedNonExternalLocalTime, orientedNonExternalLocalTimePrefix,
        orientedBoundaryLocalTime, orientedLazyLocalTime, lazyLocalTime]
  | shifted =>
      simp only [orientedNonExternalLocalTime,
        orientedNonExternalLocalTimePrefix, orientedBoundaryLocalTime,
        orientedLazyLocalTime, shiftedLazyLocalTimeAt]
      have hzero : pathPrefix s n 0 = s 0 := rfl
      rw [hzero]

theorem measurable_orientedNonExternalLocalTime
    (o : Orientation) (n : ℕ) (x : Point) :
    Measurable fun s : WalkPath ↦ orientedNonExternalLocalTime o s n x := by
  have h : Measurable
      (orientedNonExternalLocalTimePrefix o (n := n) (x := x) ∘
        fun s : WalkPath ↦ pathPrefix s n) :=
    (measurable_of_countable
      (orientedNonExternalLocalTimePrefix o (n := n) (x := x))).comp
        (measurable_pathPrefix n)
  convert h using 1
  funext s
  exact orientedNonExternalLocalTime_eq_prefix o s n x

theorem measurableSet_lazyOverflowAt (o : Orientation) (n cap : ℕ) :
    MeasurableSet {s : WalkPath | LazyOverflowAt o n cap s} := by
  rw [show {s : WalkPath | LazyOverflowAt o n cap s} =
      ⋃ x : Point, {s | cap < orientedNonExternalLocalTime o s n x} by
    ext s
    simp [LazyOverflowAt]]
  exact MeasurableSet.iUnion fun x ↦
    measurableSet_lt measurable_const
      (measurable_orientedNonExternalLocalTime o n x)

theorem measurableSet_lazyGoodAt (o : Orientation) (n cap : ℕ) :
    MeasurableSet {s : WalkPath | LazyGoodAt o n cap s} := by
  rw [show {s : WalkPath | LazyGoodAt o n cap s} =
      {s | LazyOverflowAt o n cap s}ᶜ by
    ext s
    simp [lazyOverflowAt_iff_not_lazyGoodAt]]
  exact (measurableSet_lazyOverflowAt o n cap).compl

theorem measurableSet_stoppedLazyOverflowEvent
    (o : Orientation) (m k cap : ℕ) :
    MeasurableSet (stoppedLazyOverflowEvent o m k cap) := by
  exact MeasurableSet.iUnion fun n ↦
    (measurableSet_thresholdCreationSet m k n).inter
      (measurableSet_lazyOverflowAt o n cap)

theorem measurableSet_stoppedLazyGoodEvent
    (o : Orientation) (m k cap : ℕ) :
    MeasurableSet (stoppedLazyGoodEvent o m k cap) := by
  exact MeasurableSet.iUnion fun n ↦
    (measurableSet_thresholdCreationSet m k n).inter
      (measurableSet_lazyGoodAt o n cap)

theorem measurableSet_lazyOverflowExceptionalEvent (m cap : ℕ) :
    MeasurableSet (lazyOverflowExceptionalEvent m cap) := by
  unfold lazyOverflowExceptionalEvent
  exact (MeasurableSet.iUnion fun k : Fin 3 ↦
    measurableSet_stoppedLazyOverflowEvent .even m (k + 1) cap).union
      (MeasurableSet.iUnion fun k : Fin 3 ↦
        measurableSet_stoppedLazyOverflowEvent .shifted m (k + 1) cap)

theorem measurableSet_lazyGoodGapEvent
    (t : DominoTiling) (m cap : ℕ) :
    MeasurableSet (lazyGoodGapEvent t m cap) :=
  (measurableSet_onTimeGapDeficitExceptionalEvent t m).diff
    (measurableSet_lazyOverflowExceptionalEvent m cap)

theorem measurableSet_lazyGoodPart
    {gapEvent : Set WalkPath} (hgap : MeasurableSet gapEvent)
    (m cap : ℕ) :
    MeasurableSet (lazyGoodPart gapEvent m cap) :=
  hgap.diff (measurableSet_lazyOverflowExceptionalEvent m cap)

/-! ## Exact stopped-past coverage -/

theorem lazyGoodAt_of_creation_not_mem_stoppedLazyOverflow
    {o : Orientation} {m k cap n : ℕ} {s : WalkPath}
    (hcreation : ThresholdCreation s m k n)
    (hnot : s ∉ stoppedLazyOverflowEvent o m k cap) :
    LazyGoodAt o n cap s := by
  by_contra hgood
  apply hnot
  exact Set.mem_iUnion.mpr ⟨n, hcreation,
    (lazyOverflowAt_iff_not_lazyGoodAt o n cap s).2 hgood⟩

theorem orientedNonExternalLocalTime_le_of_creation_not_overflow
    {o : Orientation} {m k cap n : ℕ} {s : WalkPath} {x : Point}
    (hcreation : ThresholdCreation s m k n)
    (hnot : s ∉ stoppedLazyOverflowEvent o m k cap) :
    orientedNonExternalLocalTime o s n x ≤ cap :=
  lazyGoodAt_of_creation_not_mem_stoppedLazyOverflow hcreation hnot x

theorem onTimeGapDeficit_subset_lazyOverflow_union_good
    (t : DominoTiling) (m cap : ℕ) :
    onTimeGapDeficitExceptionalEvent t m ⊆
      lazyOverflowExceptionalEvent m cap ∪ lazyGoodGapEvent t m cap := by
  intro s hs
  by_cases hoverflow : s ∈ lazyOverflowExceptionalEvent m cap
  · exact Or.inl hoverflow
  · exact Or.inr ⟨hs, hoverflow⟩

theorem subset_lazyOverflow_union_lazyGoodPart
    (gapEvent : Set WalkPath) (m cap : ℕ) :
    gapEvent ⊆ lazyOverflowExceptionalEvent m cap ∪
      lazyGoodPart gapEvent m cap := by
  intro s hs
  by_cases hoverflow : s ∈ lazyOverflowExceptionalEvent m cap
  · exact Or.inl hoverflow
  · exact Or.inr ⟨hs, hoverflow⟩

/-! ## Insertion-law estimate of the overflow branch -/

/-- A literal one-site stopped insertion certificate for one orientation and
one old creation rank.  Its balanced set is definitionally the complement of
the stopped lazy-overflow event.  Thus the `lower_law` and `upper_law` fields
of `GeometricBalanceLaw` must be proved from the geometric product measure;
they cannot be replaced by the desired union bound. -/
abbrev StoppedLazyBalanceLaw
    (o : Orientation) (m k cap : ℕ) :=
  GeometricBalanceLaw (Site := Point) simpleRandomWalk
    (stoppedLazyOverflowEvent o m k cap)ᶜ m

/-- The exact ENNReal cost delivered by the checked negative-binomial
moderate-deviation theorem for one stopped lazy screen. -/
noncomputable def stoppedLazyBalanceCost
    {o : Orientation} {m k cap : ℕ}
    (law : StoppedLazyBalanceLaw o m k cap) : ℝ≥0∞ :=
  (law.budget : ℝ≥0∞) *
    (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
      ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)))

/-- The path-space stopped-overflow bound derived from the literal geometric
one-site laws. -/
theorem simpleRandomWalk_stoppedLazyOverflowEvent_le
    {o : Orientation} {m k cap : ℕ}
    (law : StoppedLazyBalanceLaw o m k cap) :
    simpleRandomWalk (stoppedLazyOverflowEvent o m k cap) ≤
      stoppedLazyBalanceCost law := by
  have hreal := measureReal_compl_le_of_geometricBalanceLaw
    simpleRandomWalk (stoppedLazyOverflowEvent o m k cap)ᶜ m law
  have hcostTop : stoppedLazyBalanceCost law ≠ ∞ := by
    unfold stoppedLazyBalanceCost
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top <|
      ENNReal.add_ne_top.mpr
        ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) hcostTop).mp
  simpa [MeasureTheory.Measure.real, stoppedLazyBalanceCost] using hreal

/-- Six literal insertion-law certificates bound the complete stopped lazy
exception. -/
theorem simpleRandomWalk_lazyOverflowExceptionalEvent_le
    {m cap : ℕ}
    (evenLaw : ∀ k : Fin 3,
      StoppedLazyBalanceLaw .even m (k + 1) cap)
    (shiftedLaw : ∀ k : Fin 3,
      StoppedLazyBalanceLaw .shifted m (k + 1) cap) :
    simpleRandomWalk (lazyOverflowExceptionalEvent m cap) ≤
      (∑ k : Fin 3, stoppedLazyBalanceCost (evenLaw k)) +
        ∑ k : Fin 3, stoppedLazyBalanceCost (shiftedLaw k) := by
  unfold lazyOverflowExceptionalEvent
  refine (measure_union_le _ _).trans (add_le_add ?_ ?_)
  · refine (MeasureTheory.measure_iUnion_le _).trans ?_
    rw [tsum_fintype]
    exact Finset.sum_le_sum fun k _ ↦
      simpleRandomWalk_stoppedLazyOverflowEvent_le (evenLaw k)
  · refine (MeasureTheory.measure_iUnion_le _).trans ?_
    rw [tsum_fintype]
    exact Finset.sum_le_sum fun k _ ↦
      simpleRandomWalk_stoppedLazyOverflowEvent_le (shiftedLaw k)

/-- Literal stopped insertion laws for all six old-rank/orientation screens
at every level. -/
structure StoppedLazyLawFamily (cap : ℕ → ℕ) where
  lawStart : ℕ
  evenLaw : ∀ m, lawStart ≤ m → 0 < m → ∀ k : Fin 3,
    StoppedLazyBalanceLaw .even m (k + 1) (cap m)
  shiftedLaw : ∀ m, lawStart ≤ m → 0 < m → ∀ k : Fin 3,
    StoppedLazyBalanceLaw .shifted m (k + 1) (cap m)

/-- The complete six-screen negative-binomial cost. -/
noncomputable def stoppedLazyOverflowCost
    {cap : ℕ → ℕ} (laws : StoppedLazyLawFamily cap) (m : ℕ) : ℝ≥0∞ :=
  if htail : laws.lawStart ≤ m ∧ 0 < m then
    (∑ k : Fin 3,
      stoppedLazyBalanceCost (laws.evenLaw m htail.1 htail.2 k)) +
      ∑ k : Fin 3,
        stoppedLazyBalanceCost (laws.shiftedLaw m htail.1 htail.2 k)
  else 1

theorem simpleRandomWalk_lazyOverflowExceptionalEvent_le_family
    {cap : ℕ → ℕ} (laws : StoppedLazyLawFamily cap) (m : ℕ) :
    simpleRandomWalk (lazyOverflowExceptionalEvent m (cap m)) ≤
      stoppedLazyOverflowCost laws m := by
  by_cases htail : laws.lawStart ≤ m ∧ 0 < m
  · rw [stoppedLazyOverflowCost, dif_pos htail]
    exact simpleRandomWalk_lazyOverflowExceptionalEvent_le
      (laws.evenLaw m htail.1 htail.2)
      (laws.shiftedLaw m htail.1 htail.2)
  · rw [stoppedLazyOverflowCost, dif_neg htail]
    simpa using measure_mono (μ := simpleRandomWalk)
      (subset_univ (lazyOverflowExceptionalEvent m (cap m)))

/-- Numerical endpoint of the checked geometric moderate deviations. -/
def HasStoppedLazyOverflowRate
    (c : ℝ) {cap : ℕ → ℕ} (laws : StoppedLazyLawFamily cap) : Prop :=
  ∀ᶠ m : ℕ in atTop,
    stoppedLazyOverflowCost laws m ≤
      ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2))

theorem eventually_simpleRandomWalk_lazyOverflowExceptionalEvent_le_exp
    {c : ℝ} {cap : ℕ → ℕ} (laws : StoppedLazyLawFamily cap)
    (hrate : HasStoppedLazyOverflowRate c laws) :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk (lazyOverflowExceptionalEvent m (cap m)) ≤
        ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) := by
  filter_upwards [hrate] with m hm
  exact (simpleRandomWalk_lazyOverflowExceptionalEvent_le_family laws m).trans hm

theorem simpleRandomWalk_lazyOverflowExceptionalEvent_series_ne_top
    {c : ℝ} (hc : 0 < c) {cap : ℕ → ℕ}
    (laws : StoppedLazyLawFamily cap)
    (hrate : HasStoppedLazyOverflowRate c laws) :
    ∑' m, simpleRandomWalk (lazyOverflowExceptionalEvent m (cap m)) ≠ ∞ := by
  exact HLOZUpperEstimates.measure_series_ne_top_of_eventually_exp_neg_log_sq_bound
    simpleRandomWalk (fun m ↦ lazyOverflowExceptionalEvent m (cap m)) hc
      (eventually_simpleRandomWalk_lazyOverflowExceptionalEvent_le_exp
        laws hrate)

/-! ## The exceptional family with the lazy split made explicit -/

/-- The upper exceptional event with the on-time gap term split into a
stopped-past lazy overflow and the genuinely screenable lazy-good branch. -/
def hlozExceptionalEventWithLazy
    (t : DominoTiling) (m cap : ℕ) : Set WalkPath :=
  (lateLevelSet upperTailDelta m 4 ∪ meshOverflowEvent t m) ∪
    (lazyOverflowExceptionalEvent m cap ∪ lazyGoodGapEvent t m cap)

theorem measurableSet_hlozExceptionalEventWithLazy
    (t : DominoTiling) (m cap : ℕ) :
    MeasurableSet (hlozExceptionalEventWithLazy t m cap) := by
  exact ((LowerAssembly.measurableSet_lateLevelSet
    upperTailDelta m 4 (by omega)).union
      (measurableSet_meshOverflowEvent t m)).union
        ((measurableSet_lazyOverflowExceptionalEvent m cap).union
          (measurableSet_lazyGoodGapEvent t m cap))

theorem hlozExceptionalEvent_subset_withLazy
    (t : DominoTiling) (m cap : ℕ) :
    hlozExceptionalEvent t m ⊆ hlozExceptionalEventWithLazy t m cap := by
  intro s hs
  rcases hs with hbase | hgap
  · exact Or.inl hbase
  · exact Or.inr (onTimeGapDeficit_subset_lazyOverflow_union_good
      t m cap hgap)

/-- The probability hypotheses after the sound lazy split.  The first is
derived above from literal variable-time geometric laws; the second is the
return screen applied only on the lazy-good branch. -/
def HasLazyGoodGapReturnBound (c : ℝ) (cap : ℕ → ℕ) : Prop :=
  ∀ t : DominoTiling, ∀ᶠ m : ℕ in atTop,
    simpleRandomWalk (lazyGoodGapEvent t m (cap m)) ≤
      ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2))

theorem simpleRandomWalk_lazyGoodGapEvent_series_ne_top
    {c : ℝ} (hc : 0 < c) {cap : ℕ → ℕ}
    (hgood : HasLazyGoodGapReturnBound c cap) (t : DominoTiling) :
    ∑' m, simpleRandomWalk (lazyGoodGapEvent t m (cap m)) ≠ ∞ := by
  exact HLOZUpperEstimates.measure_series_ne_top_of_eventually_exp_neg_log_sq_bound
    simpleRandomWalk (fun m ↦ lazyGoodGapEvent t m (cap m)) hc (hgood t)

/-- Summability of the original HLOZ exceptional family after splitting its
gap term.  This is the integration point consumed by the existing upper
assembly; the original event need not be redefined. -/
theorem simpleRandomWalk_hlozExceptional_series_ne_top_of_lazySplit
    (hProp13 : HasPlanarMaximumLowerDeviation simpleRandomWalk)
    {cLazy cGood : ℝ} (hcLazy : 0 < cLazy) (hcGood : 0 < cGood)
    {cap : ℕ → ℕ} (laws : StoppedLazyLawFamily cap)
    (hrate : HasStoppedLazyOverflowRate cLazy laws)
    (hgood : HasLazyGoodGapReturnBound cGood cap)
    (t : DominoTiling) :
    ∑' m, simpleRandomWalk (hlozExceptionalEvent t m) ≠ ∞ := by
  have hlate := HLOZUpperEstimates.simpleRandomWalk_lateLevel_series_ne_top
    hProp13
  have hmesh := HLOZUpperEstimates.simpleRandomWalk_meshOverflow_series_ne_top
    hProp13 t
  have hlazy := simpleRandomWalk_lazyOverflowExceptionalEvent_series_ne_top
    hcLazy laws hrate
  have hgoodSeries := simpleRandomWalk_lazyGoodGapEvent_series_ne_top
    hcGood hgood t
  have hmajor : ∑' m,
      (((simpleRandomWalk (lateLevelSet upperTailDelta m 4) +
          simpleRandomWalk (meshOverflowEvent t m)) +
        simpleRandomWalk (lazyOverflowExceptionalEvent m (cap m))) +
        simpleRandomWalk (lazyGoodGapEvent t m (cap m))) ≠ ∞ := by
    rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add]
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr
        ⟨ENNReal.add_ne_top.mpr ⟨hlate, hmesh⟩, hlazy⟩, hgoodSeries⟩
  apply ne_top_of_le_ne_top hmajor
  apply ENNReal.tsum_le_tsum
  intro m
  calc
    simpleRandomWalk (hlozExceptionalEvent t m) ≤
        simpleRandomWalk (hlozExceptionalEventWithLazy t m (cap m)) :=
      measure_mono (hlozExceptionalEvent_subset_withLazy t m (cap m))
    _ ≤ (simpleRandomWalk (lateLevelSet upperTailDelta m 4) +
          simpleRandomWalk (meshOverflowEvent t m)) +
        (simpleRandomWalk (lazyOverflowExceptionalEvent m (cap m)) +
          simpleRandomWalk (lazyGoodGapEvent t m (cap m))) := by
      exact (measure_union_le _ _).trans <| add_le_add
        (measure_union_le _ _) (measure_union_le _ _)
    _ = (((simpleRandomWalk (lateLevelSet upperTailDelta m 4) +
          simpleRandomWalk (meshOverflowEvent t m)) +
        simpleRandomWalk (lazyOverflowExceptionalEvent m (cap m))) +
        simpleRandomWalk (lazyGoodGapEvent t m (cap m))) := by
      ac_rfl

/-- On the good branch the lazy cap is available at every one of the three
possible old creation clocks and for both orientations.  No future target is
mentioned in the statement. -/
theorem lazy_cap_at_every_old_creation_of_mem_lazyGoodPart
    {gapEvent : Set WalkPath} {m cap : ℕ} {s : WalkPath}
    (hs : s ∈ lazyGoodPart gapEvent m cap)
    (o : Orientation) (k : Fin 3) {n : ℕ}
    (hcreation : ThresholdCreation s m (k + 1) n) (x : Point) :
    orientedNonExternalLocalTime o s n x ≤ cap := by
  apply orientedNonExternalLocalTime_le_of_creation_not_overflow hcreation
  intro hoverflow
  apply hs.2
  cases o with
  | even => exact Or.inl (Set.mem_iUnion.mpr ⟨k, hoverflow⟩)
  | shifted => exact Or.inr (Set.mem_iUnion.mpr ⟨k, hoverflow⟩)

theorem lazy_cap_at_every_old_creation_of_mem_lazyGoodGap
    {t : DominoTiling} {m cap : ℕ} {s : WalkPath}
    (hs : s ∈ lazyGoodGapEvent t m cap)
    (o : Orientation) (k : Fin 3) {n : ℕ}
    (hcreation : ThresholdCreation s m (k + 1) n) (x : Point) :
    orientedNonExternalLocalTime o s n x ≤ cap := by
  exact lazy_cap_at_every_old_creation_of_mem_lazyGoodPart
    hs o k hcreation x

/-- The preceding target-free statement specializes to the genuine random
old clock carried by a failed-pair band.  The proof uses only the old
creation component of `hrealizes`; in particular the future candidate does
not enter the definition of the good event. -/
theorem lazy_cap_at_randomClock_of_mem_lazyGoodGap
    {t : DominoTiling} {m cutoff cap : ℕ} {s : WalkPath}
    {band : RandomClockBand} {x : Point}
    (hs : s ∈ lazyGoodGapEvent t m cap)
    (hrealizes : RandomClockPairRealizes m cutoff s band x) (y : Point) :
    orientedNonExternalLocalTime band.orientation s
        (pathTruncatedLevelTime m band.oldRank cutoff s) y ≤ cap := by
  have holdLe : band.oldRank ≤ 3 := by
    have hrank := band.rank_lt
    have hnew := band.newRank_le_four
    omega
  let k : Fin 3 := ⟨band.oldRank - 1, by omega⟩
  have hk : (k : ℕ) + 1 = band.oldRank := by
    dsimp only [k]
    have hold := band.oldRank_pos
    omega
  apply lazy_cap_at_every_old_creation_of_mem_lazyGoodGap hs band.orientation k
    (x := y)
  simpa only [hk, RandomClockPairRealizes, FixedPairReturnRealizes,
    FixedPairRealizes] using hrealizes.1.1

theorem lazy_cap_at_randomClock_of_mem_lazyGoodPart
    {gapEvent : Set WalkPath} {m cutoff cap : ℕ} {s : WalkPath}
    {band : RandomClockBand} {x : Point}
    (hs : s ∈ lazyGoodPart gapEvent m cap)
    (hrealizes : RandomClockPairRealizes m cutoff s band x) (y : Point) :
    orientedNonExternalLocalTime band.orientation s
        (pathTruncatedLevelTime m band.oldRank cutoff s) y ≤ cap := by
  have holdLe : band.oldRank ≤ 3 := by
    have hrank := band.rank_lt
    have hnew := band.newRank_le_four
    omega
  let k : Fin 3 := ⟨band.oldRank - 1, by omega⟩
  have hk : (k : ℕ) + 1 = band.oldRank := by
    dsimp only [k]
    have hold := band.oldRank_pos
    omega
  apply lazy_cap_at_every_old_creation_of_mem_lazyGoodPart
    hs band.orientation k (x := y)
  simpa only [hk, RandomClockPairRealizes, FixedPairReturnRealizes,
    FixedPairRealizes] using hrealizes.1.1

/-- On a lazy-good path, the realized next favorite is a member of the
literal Proposition 4.8 candidate set evaluated at the random old clock.
All band arithmetic is explicit; the only use of the lazy event is the
target-independent stopped-past cap proved above. -/
theorem randomClockPairRealizes_mem_sites_of_lazyGoodGap
    {t : DominoTiling} {m cutoff cap : ℕ} {s : WalkPath}
    {band : RandomClockBand} {x : Point}
    (hs : s ∈ lazyGoodGapEvent t m cap)
    (hrealizes : RandomClockPairRealizes m cutoff s band x)
    (hcap : cap ≤ band.lazyCap)
    (hthreshold : 0 < band.externalThreshold)
    (hcompatible : SpatialInsertionFiber.OrientationCompatible
      band.orientation x)
    (hseparated : ∀ y ∈ thresholdSites s
        (pathTruncatedLevelTime m band.oldRank cutoff s) m,
      dominoBase band.orientation y ≠ dominoBase band.orientation x)
    (hwidth : 0 < shellWidth48 m)
    (hband : (m - localTime s
        (pathTruncatedLevelTime m band.oldRank cutoff s) x) /
          shellWidth48 m < shellCount48 m band.beta)
    (hscale : band.externalThreshold + band.lazyCap +
        shellWidth48 m * shellCount48 m band.beta ≤ m + 1) :
    x ∈ randomClockBandSites m cutoff s band := by
  apply fixedPairReturnRealizes_mem_stoppedCandidateSites48
    band.oldRank_pos band.newRank_pos band.rank_lt hrealizes
    hthreshold hcompatible
  · exact (lazy_cap_at_randomClock_of_mem_lazyGoodGap hs hrealizes x).trans hcap
  · exact hseparated
  · exact hwidth
  · exact hband
  · exact hscale

theorem randomClockPairRealizes_mem_sites_of_lazyGoodPart
    {gapEvent : Set WalkPath} {m cutoff cap : ℕ} {s : WalkPath}
    {band : RandomClockBand} {x : Point}
    (hs : s ∈ lazyGoodPart gapEvent m cap)
    (hrealizes : RandomClockPairRealizes m cutoff s band x)
    (hcap : cap ≤ band.lazyCap)
    (hthreshold : 0 < band.externalThreshold)
    (hcompatible : SpatialInsertionFiber.OrientationCompatible
      band.orientation x)
    (hseparated : ∀ y ∈ thresholdSites s
        (pathTruncatedLevelTime m band.oldRank cutoff s) m,
      dominoBase band.orientation y ≠ dominoBase band.orientation x)
    (hwidth : 0 < shellWidth48 m)
    (hband : (m - localTime s
        (pathTruncatedLevelTime m band.oldRank cutoff s) x) /
          shellWidth48 m < shellCount48 m band.beta)
    (hscale : band.externalThreshold + band.lazyCap +
        shellWidth48 m * shellCount48 m band.beta ≤ m + 1) :
    x ∈ randomClockBandSites m cutoff s band := by
  apply fixedPairReturnRealizes_mem_stoppedCandidateSites48
    band.oldRank_pos band.newRank_pos band.rank_lt hrealizes
    hthreshold hcompatible
  · exact (lazy_cap_at_randomClock_of_mem_lazyGoodPart hs hrealizes x).trans hcap
  · exact hseparated
  · exact hwidth
  · exact hband
  · exact hscale

/-! ## Random-cutoff Proposition 4.8 interface -/

/-- The finite oriented external range at a genuine random old clock. -/
noncomputable def randomClockVisitedSites
    (m cutoff : ℕ) (band : RandomClockBand) (s : WalkPath) : Finset Point :=
  ExternalThickCount.orientedExternalVisitedSites band.orientation s
    (pathTruncatedLevelTime m band.oldRank cutoff s)

/-- The positive external-local-time threshold at that same random clock. -/
def randomClockExternalLargeEvent
    (m cutoff : ℕ) (band : RandomClockBand) (x : Point) : Set WalkPath :=
  {s | band.externalThreshold ≤
    ExternalThickCount.orientedExternalLocalTime band.orientation s
      (pathTruncatedLevelTime m band.oldRank cutoff s) x}

/-- The old favorite-domino bases, evaluated without fixing the clock. -/
noncomputable def randomClockDistinguishedSites
    (m cutoff : ℕ) (band : RandomClockBand) (s : WalkPath) : Finset Point :=
  favoriteDominoBases band.orientation s
    (pathTruncatedLevelTime m band.oldRank cutoff s)

/-- The actual local-time profile at the random old clock. -/
def randomClockTotalLocalTime
    (m cutoff : ℕ) (band : RandomClockBand) (s : WalkPath) (x : Point) : ℕ :=
  localTime s (pathTruncatedLevelTime m band.oldRank cutoff s) x

/-- The random-clock candidates used by the finite gap screen are
definitionally the dynamic-cutoff candidates to which the thresholded
Proposition 4.8 estimate applies. -/
theorem randomClockBandSites_eq_dynamic
    (m cutoff : ℕ) (band : RandomClockBand) (s : WalkPath) :
    randomClockBandSites m cutoff s band =
      dynamicStoppedCandidateSites48
        (randomClockVisitedSites m cutoff band)
        (randomClockExternalLargeEvent m cutoff band)
        (randomClockDistinguishedSites m cutoff band)
        (randomClockTotalLocalTime m cutoff band)
        m band.beta s := by
  classical
  ext x
  simp only [randomClockBandSites, dynamicStoppedCandidateSites48,
    randomClockVisitedSites, stoppedCandidateSites48,
    dynamicThickCandidates, externalThickCandidates, mem_boundedCandidates,
    Finset.mem_filter]
  simp [randomClockExternalLargeEvent, randomClockDistinguishedSites,
    randomClockTotalLocalTime, deficitShellLabel]

theorem measurableSet_memberEvent_randomClockVisitedSites
    (m cutoff : ℕ) (band : RandomClockBand) (x : Point) :
    MeasurableSet (ExternalThickCount.memberEvent
      (randomClockVisitedSites m cutoff band) x) := by
  rw [show ExternalThickCount.memberEvent
      (randomClockVisitedSites m cutoff band) x =
        ⋃ n : ℕ,
          {s | pathTruncatedLevelTime m band.oldRank cutoff s = n} ∩
            {s | x ∈ ExternalThickCount.orientedExternalVisitedSites
              band.orientation s n} by
    ext s
    simp only [ExternalThickCount.memberEvent, randomClockVisitedSites,
      Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hs
      exact ⟨pathTruncatedLevelTime m band.oldRank cutoff s, rfl, hs⟩
    · rintro ⟨n, hn, hs⟩
      simpa only [hn] using hs]
  exact MeasurableSet.iUnion fun n ↦
    (measurableSet_pathTruncatedLevelTime_eq m band.oldRank cutoff n).inter
      (ExternalThickCount.measurableSet_member_orientedExternalVisitedSites
        band.orientation n x)

theorem measurableSet_randomClockExternalLargeEvent
    (m cutoff : ℕ) (band : RandomClockBand) (x : Point) :
    MeasurableSet (randomClockExternalLargeEvent m cutoff band x) := by
  rw [show randomClockExternalLargeEvent m cutoff band x =
        ⋃ n : ℕ,
          {s | pathTruncatedLevelTime m band.oldRank cutoff s = n} ∩
            {s | band.externalThreshold ≤
              ExternalThickCount.orientedExternalLocalTime
                band.orientation s n x} by
    ext s
    simp only [randomClockExternalLargeEvent, Set.mem_ofPred_eq,
      Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hs
      exact ⟨pathTruncatedLevelTime m band.oldRank cutoff s, rfl, hs⟩
    · rintro ⟨n, hn, hs⟩
      simpa only [hn] using hs]
  exact MeasurableSet.iUnion fun n ↦
    (measurableSet_pathTruncatedLevelTime_eq m band.oldRank cutoff n).inter
      (measurableSet_le measurable_const
        (ExternalThickCount.measurable_orientedExternalLocalTime
          band.orientation n x))

/-- The exact dynamic candidate overflow is the band overflow occurring in
the random-clock finite screen.  This is the direct consumer seam for
`simpleRandomWalk_dynamicStoppedCandidateOverflow48_le_thresholded`. -/
theorem randomClockBandOverflow_eq_dynamic
    (m cutoff : ℕ) (band : RandomClockBand) :
    {s | candidateBudget48 m band.beta <
      (randomClockBandSites m cutoff s band).card} =
      dynamicStoppedCandidateOverflow48
        (randomClockVisitedSites m cutoff band)
        (randomClockExternalLargeEvent m cutoff band)
        (randomClockDistinguishedSites m cutoff band)
        (randomClockTotalLocalTime m cutoff band)
        m band.beta := by
  ext s
  simp only [dynamicStoppedCandidateOverflow48, Set.mem_ofPred_eq,
    randomClockBandSites_eq_dynamic]

/-! ## Domination by the deterministic HLOZ external cap -/

/-- The dynamic candidate set with the same stopped large-local-time
predicate as the random-clock band, but with the visited range enlarged to
the deterministic HLOZ cap.  This is exactly the input expected by the
closed stopped one-point theorem. -/
noncomputable def randomClockDominatingBandSites
    (m cutoff : ℕ) (band : RandomClockBand) (s : WalkPath) : Finset Point :=
  dynamicStoppedCandidateSites48
    (stoppedCapVisitedSites band.orientation m)
    (stoppedOrientedLargeEvent band.orientation
      (pathTruncatedLevelTime m band.oldRank cutoff) band.externalThreshold)
    (randomClockDistinguishedSites m cutoff band)
    (randomClockTotalLocalTime m cutoff band)
    m band.beta s

/-- Its single-band overflow event. -/
def randomClockDominatingBandOverflow
    (m cutoff : ℕ) (band : RandomClockBand) : Set WalkPath :=
  {s | candidateBudget48 m band.beta <
    (randomClockDominatingBandSites m cutoff band s).card}

theorem randomClockExternalLargeEvent_eq_stopped
    (m cutoff : ℕ) (band : RandomClockBand) (x : Point) :
    randomClockExternalLargeEvent m cutoff band x =
      stoppedOrientedLargeEvent band.orientation
        (pathTruncatedLevelTime m band.oldRank cutoff)
        band.externalThreshold x := by
  rfl

/-- On the support of simple random walk, the external range at the genuine
old creation clock is contained in the range at any later deterministic
cap.  No value of the physical creation clock is fixed in this statement. -/
theorem randomClockVisitedSites_subset_stoppedCapVisitedSites_of_valid
    {m cutoff : ℕ} {band : RandomClockBand} {s : WalkPath}
    (hcutoff : cutoff ≤ ExternalProposition44.hlozCutoff44 m)
    (hvalid : s ∈ validStepWalk) :
    randomClockVisitedSites m cutoff band s ⊆
      stoppedCapVisitedSites band.orientation m s := by
  classical
  rw [show s = trajectory (stepsOfWalk s) by
    exact (show trajectory (stepsOfWalk s) = s from hvalid).symm]
  intro x hx
  have hxclass : ExternalThickCount.orientationClass band.orientation x := by
    unfold randomClockVisitedSites ExternalThickCount.orientedExternalVisitedSites at hx
    exact (Finset.mem_filter.mp hx).2
  have hxpos : 0 < ExternalThickCount.orientedExternalLocalTime band.orientation
      (trajectory (stepsOfWalk s))
      (pathTruncatedLevelTime m band.oldRank cutoff
        (trajectory (stepsOfWalk s))) x := by
    unfold randomClockVisitedSites ExternalThickCount.orientedExternalVisitedSites at hx
    have hmem := (Finset.mem_filter.mp hx).1
    rw [List.mem_toFinset, ← List.count_pos_iff] at hmem
    exact hmem
  have htime : pathTruncatedLevelTime m band.oldRank cutoff
      (trajectory (stepsOfWalk s)) ≤ ExternalProposition44.hlozCutoff44 m :=
    (pathTruncatedLevelTime_le m band.oldRank cutoff _).trans hcutoff
  have hxmono := orientedExternalLocalTime_mono_of_orientationClass
    band.orientation (stepsOfWalk s) htime x hxclass
  apply mem_orientedExternalVisitedSites_of_localTime_pos
  · exact (orientationCompatible_iff_orientationClass
      band.orientation x).mpr hxclass
  · exact hxpos.trans_le hxmono

/-- Hence every genuine random-clock candidate is retained by the
deterministic-cap dynamic screen, on the full-measure canonical support. -/
theorem randomClockBandSites_subset_dominating_of_valid
    {m cutoff : ℕ} {band : RandomClockBand} {s : WalkPath}
    (hcutoff : cutoff ≤ ExternalProposition44.hlozCutoff44 m)
    (hvalid : s ∈ validStepWalk) :
    randomClockBandSites m cutoff s band ⊆
      randomClockDominatingBandSites m cutoff band s := by
  classical
  rw [randomClockBandSites_eq_dynamic]
  unfold randomClockDominatingBandSites dynamicStoppedCandidateSites48
  intro x hx
  rw [mem_boundedCandidates] at hx ⊢
  refine ⟨?_, hx.2⟩
  unfold dynamicThickCandidates at hx ⊢
  simp only [Finset.mem_filter] at hx ⊢
  refine ⟨randomClockVisitedSites_subset_stoppedCapVisitedSites_of_valid
    hcutoff hvalid hx.1.1, ?_⟩
  simpa only [randomClockExternalLargeEvent_eq_stopped] using hx.1.2

/-- Single-band overflow is likewise dominated on the canonical support. -/
theorem randomClockBandOverflow_subset_dominating_union_invalid
    {m cutoff : ℕ} {band : RandomClockBand}
    (hcutoff : cutoff ≤ ExternalProposition44.hlozCutoff44 m) :
    {s | candidateBudget48 m band.beta <
        (randomClockBandSites m cutoff s band).card} ⊆
      randomClockDominatingBandOverflow m cutoff band ∪ validStepWalkᶜ := by
  intro s hs
  by_cases hvalid : s ∈ validStepWalk
  · left
    exact hs.trans_le (Finset.card_le_card
      (randomClockBandSites_subset_dominating_of_valid hcutoff hvalid))
  · exact Or.inr hvalid

/-! ## Lazy-good random-clock finite screen -/

/-- Band extraction from the lazy-good part of an arbitrary target event. -/
def LazyGoodRandomClockExtraction
    (gapEvent : Set WalkPath) (m cutoff cap : ℕ)
    (bands : Finset RandomClockBand) : Prop :=
  PathGapWitness (lazyGoodPart gapEvent m cap) bands
    (randomClockBandSites m cutoff)
    (fun band ↦ candidateBudget48 m band.beta)
    (RandomClockPairRealizes m cutoff)

/-- Sound extraction is required only on the lazy-good branch.  Its finite
index retains beta/scale/rank/orientation data, but no physical clock value. -/
def LazyGoodRandomClockBandExtraction
    (t : DominoTiling) (m cutoff cap : ℕ)
    (bands : Finset RandomClockBand) : Prop :=
  LazyGoodRandomClockExtraction
    (onTimeGapDeficitExceptionalEvent t m) m cutoff cap bands

theorem lazyGoodRandomClockBandExtraction_of_full
    {t : DominoTiling} {m cutoff cap : ℕ}
    {bands : Finset RandomClockBand}
    (h : RandomClockBandExtraction t m cutoff bands) :
    LazyGoodRandomClockBandExtraction t m cutoff cap bands := by
  intro s hs hno
  exact h s hs.1 hno

/-- The strong-Markov random-clock screen applied to the lazy-good part of
an arbitrary event.  The slot estimate is unchanged, and there is still no
time-atom factor. -/
theorem measure_lazyGoodPart_le_randomClockScreen
    (gapEvent : Set WalkPath) (m cutoff cap : ℕ)
    (bands : Finset RandomClockBand)
    (hextract : LazyGoodRandomClockExtraction
      gapEvent m cutoff cap bands) :
    simpleRandomWalk (lazyGoodPart gapEvent m cap) ≤
      simpleRandomWalk
        (candidateOverflow bands (randomClockBandSites m cutoff)
          (fun band ↦ candidateBudget48 m band.beta)) +
        ∑ band ∈ bands,
          (candidateBudget48 m band.beta : ℝ≥0∞) *
            Gap.geometricReturnCost
              (meshPointEscapeChance m band.scale) band.returns := by
  let sites := randomClockBandSites m cutoff
  let budget : RandomClockBand → ℕ := fun band ↦
    candidateBudget48 m band.beta
  let realizes := RandomClockPairRealizes m cutoff
  let overflow := candidateOverflow bands sites budget
  let screened := lazyGoodPart gapEvent m cap \ overflow
  have hsplit : lazyGoodPart gapEvent m cap ⊆ overflow ∪ screened := by
    intro s hs
    by_cases hoverflow : s ∈ overflow
    · exact Or.inl hoverflow
    · exact Or.inr ⟨hs, hoverflow⟩
  calc
    simpleRandomWalk (lazyGoodPart gapEvent m cap) ≤
        simpleRandomWalk (overflow ∪ screened) := measure_mono hsplit
    _ ≤ simpleRandomWalk overflow + simpleRandomWalk screened :=
      measure_union_le _ _
    _ ≤ simpleRandomWalk overflow +
        ∑ band ∈ bands, (budget band : ℝ≥0∞) *
          Gap.geometricReturnCost
            (meshPointEscapeChance m band.scale) band.returns := by
      gcongr
      exact Gap.measure_gapEvent_le_geometric_sum simpleRandomWalk screened bands
        (fun band ↦ Finset.range (budget band))
        (slotSuccessEvent sites realizes) budget
        (fun band ↦ meshPointEscapeChance m band.scale)
        RandomClockBand.returns
        (by
          dsimp only [screened, overflow]
          exact gapEvent_diff_overflow_covered_by_slots
            (lazyGoodPart gapEvent m cap) bands sites budget realizes hextract)
        (range_candidateCountBound bands budget)
        (by
          intro band _hband slot _hslot
          exact measure_randomClockBandSlotSuccess_le_geometric
            m cutoff band slot)

theorem measure_lazyGoodGapEvent_le_randomClockScreen
    (t : DominoTiling) (m cutoff cap : ℕ)
    (bands : Finset RandomClockBand)
    (hextract : LazyGoodRandomClockBandExtraction
      t m cutoff cap bands) :
    simpleRandomWalk (lazyGoodGapEvent t m cap) ≤
      simpleRandomWalk
        (candidateOverflow bands (randomClockBandSites m cutoff)
          (fun band ↦ candidateBudget48 m band.beta)) +
        ∑ band ∈ bands,
          (candidateBudget48 m band.beta : ℝ≥0∞) *
            Gap.geometricReturnCost
              (meshPointEscapeChance m band.scale) band.returns := by
  exact measure_lazyGoodPart_le_randomClockScreen
    (onTimeGapDeficitExceptionalEvent t m) m cutoff cap bands hextract

/-- Complete pathwise lazy-bad/lazy-good split, followed by the finite
random-clock screen on the good branch. -/
theorem measure_gapEvent_le_lazy_randomClockScreen
    (gapEvent : Set WalkPath) (m cutoff cap : ℕ)
    (bands : Finset RandomClockBand)
    (hextract : LazyGoodRandomClockExtraction
      gapEvent m cutoff cap bands) :
    simpleRandomWalk gapEvent ≤
      simpleRandomWalk (lazyOverflowExceptionalEvent m cap) +
        (simpleRandomWalk
            (candidateOverflow bands (randomClockBandSites m cutoff)
              (fun band ↦ candidateBudget48 m band.beta)) +
          ∑ band ∈ bands,
            (candidateBudget48 m band.beta : ℝ≥0∞) *
              Gap.geometricReturnCost
                (meshPointEscapeChance m band.scale) band.returns) := by
  calc
    simpleRandomWalk gapEvent ≤
        simpleRandomWalk (lazyOverflowExceptionalEvent m cap ∪
          lazyGoodPart gapEvent m cap) :=
      measure_mono (subset_lazyOverflow_union_lazyGoodPart gapEvent m cap)
    _ ≤ simpleRandomWalk (lazyOverflowExceptionalEvent m cap) +
        simpleRandomWalk (lazyGoodPart gapEvent m cap) := measure_union_le _ _
    _ ≤ simpleRandomWalk (lazyOverflowExceptionalEvent m cap) +
        (simpleRandomWalk
            (candidateOverflow bands (randomClockBandSites m cutoff)
              (fun band ↦ candidateBudget48 m band.beta)) +
          ∑ band ∈ bands,
            (candidateBudget48 m band.beta : ℝ≥0∞) *
              Gap.geometricReturnCost
                (meshPointEscapeChance m band.scale) band.returns) := by
      gcongr
      exact measure_lazyGoodPart_le_randomClockScreen
        gapEvent m cutoff cap bands hextract

/-- Eventual logarithmic-square estimate obtained by combining the literal
stopped insertion-law cost with the dynamic Proposition 4.8 overflow cost
and the random-clock return sum.  The three costs share one numerical
inequality, so no coefficient is lost by separately bounding branches. -/
theorem eventually_measure_gapEvent_le_exp_of_lazy_randomClockScreen
    (c : ℝ) (gapEvent : ℕ → Set WalkPath) (cap : ℕ → ℕ)
    (laws : StoppedLazyLawFamily cap)
    (bands : ℕ → Finset RandomClockBand)
    (hextract : ∀ m,
      LazyGoodRandomClockExtraction (gapEvent m) m
        (levelCutoffTime upperTailDelta m) (cap m) (bands m))
    (overflowCost : ℕ → ℝ≥0∞)
    (hoverflow : ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk
          (candidateOverflow (bands m)
            (randomClockBandSites m (levelCutoffTime upperTailDelta m))
            (fun band ↦ candidateBudget48 m band.beta)) ≤
        overflowCost m)
    (hnumeric : ∀ᶠ m : ℕ in atTop,
      stoppedLazyOverflowCost laws m +
          (overflowCost m +
            ∑ band ∈ bands m,
              (candidateBudget48 m band.beta : ℝ≥0∞) *
                Gap.geometricReturnCost
                  (meshPointEscapeChance m band.scale) band.returns) ≤
        ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2))) :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk (gapEvent m) ≤
        ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) := by
  filter_upwards [hoverflow, hnumeric] with m hoverflowM hnumericM
  refine (measure_gapEvent_le_lazy_randomClockScreen
    (gapEvent m) m (levelCutoffTime upperTailDelta m) (cap m)
      (bands m) (hextract m)).trans ?_
  calc
    simpleRandomWalk (lazyOverflowExceptionalEvent m (cap m)) +
        (simpleRandomWalk
            (candidateOverflow (bands m)
              (randomClockBandSites m (levelCutoffTime upperTailDelta m))
              (fun band ↦ candidateBudget48 m band.beta)) +
          ∑ band ∈ bands m,
            (candidateBudget48 m band.beta : ℝ≥0∞) *
              Gap.geometricReturnCost
                (meshPointEscapeChance m band.scale) band.returns) ≤
      stoppedLazyOverflowCost laws m +
        (overflowCost m +
          ∑ band ∈ bands m,
            (candidateBudget48 m band.beta : ℝ≥0∞) *
              Gap.geometricReturnCost
                (meshPointEscapeChance m band.scale) band.returns) := by
      gcongr
      exact simpleRandomWalk_lazyOverflowExceptionalEvent_le_family laws m
    _ ≤ ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) := hnumericM

theorem simpleRandomWalk_gapEvent_series_ne_top_of_lazy_randomClockScreen
    {c : ℝ} (hc : 0 < c) (gapEvent : ℕ → Set WalkPath)
    (cap : ℕ → ℕ) (laws : StoppedLazyLawFamily cap)
    (bands : ℕ → Finset RandomClockBand)
    (hextract : ∀ m,
      LazyGoodRandomClockExtraction (gapEvent m) m
        (levelCutoffTime upperTailDelta m) (cap m) (bands m))
    (overflowCost : ℕ → ℝ≥0∞)
    (hoverflow : ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk
          (candidateOverflow (bands m)
            (randomClockBandSites m (levelCutoffTime upperTailDelta m))
            (fun band ↦ candidateBudget48 m band.beta)) ≤
        overflowCost m)
    (hnumeric : ∀ᶠ m : ℕ in atTop,
      stoppedLazyOverflowCost laws m +
          (overflowCost m +
            ∑ band ∈ bands m,
              (candidateBudget48 m band.beta : ℝ≥0∞) *
                Gap.geometricReturnCost
                  (meshPointEscapeChance m band.scale) band.returns) ≤
        ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2))) :
    ∑' m, simpleRandomWalk (gapEvent m) ≠ ∞ := by
  exact HLOZUpperEstimates.measure_series_ne_top_of_eventually_exp_neg_log_sq_bound
    simpleRandomWalk gapEvent hc
      (eventually_measure_gapEvent_le_exp_of_lazy_randomClockScreen
        c gapEvent cap laws bands hextract overflowCost hoverflow hnumeric)

theorem measure_onTimeGapDeficitExceptionalEvent_le_lazy_randomClockScreen
    (t : DominoTiling) (m cutoff cap : ℕ)
    (bands : Finset RandomClockBand)
    (hextract : LazyGoodRandomClockBandExtraction
      t m cutoff cap bands) :
    simpleRandomWalk (onTimeGapDeficitExceptionalEvent t m) ≤
      simpleRandomWalk (lazyOverflowExceptionalEvent m cap) +
        (simpleRandomWalk
            (candidateOverflow bands (randomClockBandSites m cutoff)
              (fun band ↦ candidateBudget48 m band.beta)) +
          ∑ band ∈ bands,
            (candidateBudget48 m band.beta : ℝ≥0∞) *
              Gap.geometricReturnCost
                (meshPointEscapeChance m band.scale) band.returns) := by
  exact measure_gapEvent_le_lazy_randomClockScreen
    (onTimeGapDeficitExceptionalEvent t m) m cutoff cap bands hextract

/-! ## Transport to a positive dynamic external threshold -/

/-- The general arithmetic used after the lazy-good split.  The cap and the
whole displayed deficit window may depend on the band; no physical creation
time occurs in the inequality. -/
theorem externalThreshold_le_orientedExternal_of_lazyGood_deficit
    {o : Orientation} {s : WalkPath} {n : ℕ}
    {point : Point} {m externalThreshold cap deficit : ℕ}
    (hlazy : orientedNonExternalLocalTime o s n point ≤ cap)
    (hactual : m - localTime s n point < deficit)
    (hscale : externalThreshold + cap + deficit ≤ m + 1) :
    externalThreshold ≤
      ExternalThickCount.orientedExternalLocalTime o s n point := by
  apply externalThreshold_le_orientedExternalLocalTime_of_lazyCap hlazy
  have hlocal : externalThreshold + cap ≤ localTime s n point := by
    by_cases hle : localTime s n point ≤ m
    · have hdef : m - localTime s n point + localTime s n point = m :=
        Nat.sub_add_cancel hle
      omega
    · have hlarge : m + 1 ≤ localTime s n point := by omega
      exact (by omega : externalThreshold + cap ≤ m + 1).trans hlarge
  exact hlocal

/-! ## Exact variable-time finite-cap insertion seam -/

/-- A finite-cap predicate selecting a lazy-overflow subfamily in one
variable-time retained-word fibre.  `bad` is a statement about the genuine
natural insertion vector, while the creation time is left variable by
`StrictlyBeforeClockCutoff`. -/
def StrictLazyOverflowCoordinates {o : Orientation} {i : ℕ}
    (r : Fin i → RetainedBlock o) (tail : BoundaryTail) (cutoff cap : ℕ)
    (bad : (Fin (i + 1) → ℕ) → Prop) (q : CappedCoordinates i cap) : Prop :=
  StrictlyBeforeClockCutoff r tail cutoff q ∧
    bad (fun j ↦ (q j : ℕ))

/-- Exact mass of a finite-cap lazy-overflow subfibre.  This is a direct
specialization of the variable-time product law, not a fixed-physical-time
conditional distribution. -/
theorem fairSteps_strictCappedLazyOverflowFiber_eq_geometricSum
    {o : Orientation} (m k cutoff coordinateCap : ℕ)
    (code : ExternalWordCode o)
    (bad : (Fin (code.retainedCount + 1) → ℕ) → Prop) :
    fairSteps
        (preStoppingFiberEvent (truncatedLevelTime m k cutoff)
          code.retained coordinateCap code.tail.1
          (StrictLazyOverflowCoordinates code.retained code.tail cutoff
            coordinateCap bad)) =
      ENNReal.ofReal
        (prefixFiberConstant code.retainedCount code.tail.1 *
          ∑ q : AcceptedCappedCoordinates
              (truncatedLevelTime m k cutoff) code.retained coordinateCap
              code.tail.1
              (StrictLazyOverflowCoordinates code.retained code.tail cutoff
                coordinateCap bad),
            gapVectorMass (fun j ↦ (q.1 j : ℕ))) := by
  exact fairSteps_preStoppingFiberEvent_eq_geometricSum
    (isFiniteStoppingTime_truncatedLevelTime m k cutoff)
    code.retained coordinateCap code.tail.1
    (StrictLazyOverflowCoordinates code.retained code.tail cutoff
      coordinateCap bad)

end

end Erdos1165.HLOZLazyOverflow
